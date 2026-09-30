// integral/integrate — the public entry integrate(): the cascade, a clean answer, hints for non-elementary integrals.

import { splitCoeff } from '../../core/simplify.js';
import { containsVar, nodeKey, sym, isConst, pow, mapNode, fn, add, freeVars, nodeSome } from '../../core/ast.js';
import { Poly } from '../../core/poly.js';
import { niceForm, prettyForm } from '../derivative.js';
import { MathError } from '../../core/rational.js';
import { step } from '../../core/steps.js';
import { NM1, T_, asNode, bt, checkAnti, iTex, isNum, isVar, simp, surelyPositive, trySimp, tx } from './common.js';
import { I } from './engine.js';

// ---------------------------------------------------------------- non-elementary integrals

function nonElementaryHint(f, v) {
    const g = trySimp(f) ?? f;
    const { rest } = splitCoeff(g);
    if (!rest) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    const vfs = fs.filter((x) => containsVar(x, v));
    const key = (x) => nodeKey(x);
    const X = sym(v);
    const quadExp = (x) => x.type === 'pow' && isConst(x.base) && x.base.name === 'e' && (() => {
        const P = Poly.fromNode(x.exp, v);
        return P && P.degree === 2;
    })();
    if (vfs.length === 1 && quadExp(vfs[0])) {
        // e^(−x²) goes with erf, e^(+x²) with the imaginary error function erfi
        if (Poly.fromNode(vfs[0].exp, v).lead.isPos()) {
            return T_('Этот интеграл не выражается через элементарные функции (так доказал Лиувилль). Через специальную функцию, мнимую функцию ошибок: ∫e^(x²)dx = (√π/2)·erfi x + C.',
                'This integral has no elementary antiderivative (Liouville). With a special function, the imaginary error function: ∫e^(x²)dx = (√π/2)·erfi x + C.');
        }
        return T_('Этот интеграл не выражается через элементарные функции (так доказал Лиувилль). Через специальную функцию ошибок: ∫e^(−x²)dx = (√π/2)·erf x + C.',
            'This integral has no elementary antiderivative (Liouville). With the error function: ∫e^(−x²)dx = (√π/2)·erf x + C.');
    }
    const names = vfs.map((x) => (x.type === 'fn' ? x.name : x.type === 'pow' && x.base.type === 'fn' ? x.base.name + '^' + key(x.exp) : key(x)));
    const xm1 = key(pow(X, NM1));
    if (vfs.length === 2 && vfs.some((x) => key(x) === xm1)) {
        const other = vfs.find((x) => key(x) !== xm1);
        if (other.type === 'fn' && other.name === 'sin' && isVar(other.args[0], v)) return T_('∫(sin x / x)dx не берётся в элементарных функциях; это интегральный синус Si x.', '∫(sin x / x)dx has no elementary antiderivative; it is the sine integral Si x.');
        if (other.type === 'fn' && other.name === 'cos' && isVar(other.args[0], v)) return T_('∫(cos x / x)dx не берётся в элементарных функциях; это интегральный косинус Ci x.', '∫(cos x / x)dx has no elementary antiderivative; it is the cosine integral Ci x.');
        if (other.type === 'pow' && isConst(other.base) && other.base.name === 'e' && isVar(other.exp, v)) return T_('∫(eˣ / x)dx не берётся в элементарных функциях; это интегральная экспонента Ei x.', '∫(eˣ / x)dx has no elementary antiderivative; it is the exponential integral Ei x.');
    }
    if (vfs.length === 1 && vfs[0].type === 'pow' && isNum(vfs[0].exp) && vfs[0].exp.value.eq(-1) && vfs[0].base.type === 'fn' && vfs[0].base.name === 'ln') {
        return T_('∫dx/ln x не берётся в элементарных функциях; это интегральный логарифм li x.', '∫dx/ln x has no elementary antiderivative; it is the logarithmic integral li x.');
    }
    if (vfs.length === 1 && vfs[0].type === 'fn' && (vfs[0].name === 'sin' || vfs[0].name === 'cos')) {
        const P = Poly.fromNode(vfs[0].args[0], v);
        if (P && P.degree === 2) return T_('Интегралы Френеля ∫sin(x²)dx и ∫cos(x²)dx не выражаются через элементарные функции.', 'The Fresnel integrals ∫sin(x²)dx and ∫cos(x²)dx have no elementary antiderivative.');
    }
    if (vfs.length === 1 && vfs[0].type === 'pow' && isVar(vfs[0].base, v) && isVar(vfs[0].exp, v)) return T_('∫xˣdx не выражается через элементарные функции.', '∫xˣdx has no elementary antiderivative.');
    void names;
    return null;
}

// ---------------------------------------------------------------- cleaning the answer

export function cleanAnti(F, v) {
    let G = simp(F);
    // atan(tan u) = u up to a piecewise constant — fine for an antiderivative
    G = simp(mapNode(G, (m) => (m.type === 'fn' && m.name === 'atan' && m.args[0].type === 'fn' && m.args[0].name === 'tan' ? m.args[0].args[0] : undefined)));
    // ln|u| with u > 0 everywhere (after a substitution t = eˣ, …) is just ln u
    G = simp(mapNode(G, (m) => (m.type === 'fn' && m.name === 'ln' && m.args[0].type === 'fn' && m.args[0].name === 'abs' && surelyPositive(m.args[0].args[0], v) ? fn('ln', m.args[0].args[0]) : undefined)));
    if (G.type === 'add') {
        const kept = G.args.filter((t) => containsVar(t, v));
        if (kept.length && kept.length < G.args.length) G = simp(add(kept));
    }
    return niceForm(G, v, { fnFractions: false });
}

// ---------------------------------------------------------------- public API

export function checkExpr(node) {
    if (node.type === 'rel' || node.type === 'chain' || node.type === 'list') {
        throw new MathError({ ru: 'Нужна формула функции, а не уравнение или список', en: 'A formula is needed, not an equation or a list' }, null, null, 'not-expr');
    }
}

export function answerStep(title, tex) {
    const s = step({ title, tex, rule: 'answer' });
    s.final = true;
    return s;
}

/**
 * Indefinite integral. → {result: node | null, method, steps, verified, reason?: {ru, en}, tex}.
 * result is an antiderivative (the printed tex adds + C); verified means F′ = f was checked numerically on
 * the domain. When nothing works (or the only candidate fails the check), result is null and reason says
 * so honestly (with a hint for known non-elementary integrals).
 */
export function integrate(node, v = 'x', opts = {}) {
    node = asNode(node);
    checkExpr(node);
    let f;
    try {
        f = simp(node);
    } catch (e) {
        if (e instanceof MathError) throw e;
        throw new MathError({ ru: 'Не удалось разобрать выражение', en: 'Could not process the expression' }, null, null, 'internal');
    }
    const ctx = { v, depth: 0, budget: { calls: 0, max: opts.budget ?? 600, memo: new Map() } };
    const start = step({
        title: T_('Что интегрируем', 'What we integrate'),
        tex: bt((L) => iTex(node, v, L)),
        text: freeVars(node).filter((w) => w !== v).length
            ? T_(`Интегрируем по ${v}; остальные буквы считаем постоянными.`, `We integrate with respect to ${v}; the other letters are constants.`)
            : T_('Ищем первообразную: функцию, производная которой равна подынтегральной.', 'We look for an antiderivative: a function whose derivative is the integrand.'),
        rule: 'start',
    });
    const r = I(f, ctx);
    const fail = (reason) => ({
        result: null,
        method: null,
        steps: opts.steps ? [start, step({ title: T_('Не получилось', 'Not found'), text: reason, rule: 'fail' })] : [],
        verified: false,
        reason,
        tex: null,
    });
    if (!r) {
        const hint = nonElementaryHint(f, v);
        return fail(hint ?? T_('Не удалось найти первообразную: такой интеграл движок пока не берёт (возможно, он и не выражается через элементарные функции). Определённый интеграл можно посчитать численно.',
            'Could not find an antiderivative: the engine cannot do this integral yet (it may have no elementary antiderivative at all). A definite integral can still be computed numerically.'));
    }
    let F = cleanAnti(r.F, v);
    let verified = checkAnti(F, f, v) === true;
    if (!verified) {
        const raw = simp(r.F);
        if (checkAnti(raw, f, v) === true) {
            F = prettyForm(raw);
            verified = true;
        }
    }
    if (!verified && checkAnti(F, f, v) === false) {
        return fail(T_('Найденная функция не прошла проверку дифференцированием, поэтому ответа не показываем.', 'The candidate failed the check by differentiation, so no answer is shown.'));
    }
    const tex = bt((L) => `${iTex(node, v, L)} = ${tx(F, L)} + C`);
    const steps = [];
    if (opts.steps) {
        steps.push(start);
        steps.push(r.step);
        const rawTex = (L) => tx(simp(r.F), L);
        if (rawTex('ru') !== tx(F, 'ru')) {
            const raw = simp(r.F);
            const dropped = raw.type === 'add' && raw.args.some((t) => !containsVar(t, v));
            const atanTan = nodeSome(raw, (m) => m.type === 'fn' && m.name === 'atan' && m.args[0].type === 'fn' && m.args[0].name === 'tan');
            let text = dropped
                ? T_('Приводим ответ к аккуратному виду; слагаемые-константы уходят в произвольную постоянную C.', 'Tidy up the answer; constant terms go into the arbitrary constant C.')
                : T_('Приводим ответ к аккуратному виду.', 'Tidy up the answer.');
            if (atanTan) {
                text = T_(`${text.ru} arctg(tg u) отличается от u на постоянную (πk на каждом промежутке), её тоже забирает C.`, `${text.en} arctan(tan u) differs from u by a constant (πk on each interval), which C also absorbs.`);
            }
            steps.push(step({
                title: T_('Упрощаем', 'Simplify'),
                tex: bt((L) => `${rawTex(L)} = ${tx(F, L)}${dropped ? ' + \\mathrm{const}' : ''}`),
                text,
                rule: 'simplify',
            }));
        }
        steps.push(step({
            title: T_('Проверка', 'Check'),
            tex: bt((L) => `\\left(${tx(F, L)}\\right)' = ${tx(f, L)}`),
            text: verified
                ? T_('Дифференцируем ответ и сравниваем с подынтегральной функцией в нескольких точках — совпадает.', 'Differentiate the answer and compare with the integrand at several points: they agree.')
                : T_('Проверить ответ численно не удалось: область определения слишком узкая для выборочных точек.', 'The numeric check could not be done: the domain is too narrow for the sample points.'),
            rule: 'check',
        }));
        steps.push(answerStep(T_('Ответ', 'Answer'), tex));
    }
    return { result: F, method: r.method, steps, verified, tex };
}
