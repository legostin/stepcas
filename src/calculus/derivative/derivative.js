// derivative/derivative — the public API (derivative, partial and higher derivatives, gradient, tangent line) with
// the numeric check against central differences.

import { rng } from '../../core/random.js';
import { freeVars, toNode, substitute, sym, neg } from '../../core/ast.js';
import { evaluate } from '../../core/evaluate.js';
import { step } from '../../core/steps.js';
import { MathError } from '../../core/rational.js';
import { parse } from '../../core/parse.js';
import { simplify, canonContext } from '../../core/simplify.js';
import { niceForm, penalty, score } from './clean.js';
import { N0, NM1, T_, agree, asNode, bt, calcTex, checkExpr, isZero, negLeading, randomEnv } from './display.js';
import { quickDerivative } from './quick.js';
import { dS } from './steps.js';

// ---------------------------------------------------------------- numeric check against central differences

function smoothPoints(f, v, count, seed) {
    const r = rng(seed);
    const vars = freeVars(f).filter((w) => w !== v);
    const ranges = [[0.3, 1.7], [-1.7, -0.3], [1.7, 4], [-4, -1.7], [0.1, 0.9], [-0.9, -0.1]];
    const out = [];
    for (let k = 0; k < count * 4 && out.length < count; k++) {
        const env = randomEnv(vars, r);
        const [lo, hi] = ranges[k % ranges.length];
        env[v] = r.real(lo, hi);
        const h = 1e-3 * Math.max(1, Math.abs(env[v]));
        try {
            const ys = [-2, -1, 0, 1, 2].map((j) => evaluate(f, { ...env, [v]: env[v] + j * h }));
            if (ys.every((y) => Number.isFinite(y) && Math.abs(y) < 1e8)) out.push(env);
        } catch {
            return out;
        }
    }
    return out;
}

/** Five-point central difference with one Richardson step; NaN when two step sizes disagree (a point too close to a pole). */
function centralDiff(f, env, v) {
    const x = env[v];
    const at = (t) => evaluate(f, { ...env, [v]: t });
    const D = (h) => (at(x - 2 * h) - 8 * at(x - h) + 8 * at(x + h) - at(x + 2 * h)) / (12 * h);
    const h = 1e-3 * Math.max(1, Math.abs(x));
    const a = D(h);
    const b = D(h / 2);
    if (!Number.isFinite(a) || !Number.isFinite(b) || Math.abs(a - b) > 1e-6 * Math.max(1, Math.abs(b))) return NaN;
    return (16 * b - a) / 15;
}

function numericCheck(f, d, v) {
    const pts = smoothPoints(f, v, 6, 101);
    let ok = 0;
    for (const env of pts) {
        let a;
        let b;
        try {
            a = evaluate(d, env);
            b = centralDiff(f, env, v);
        } catch {
            return null;
        }
        if (!Number.isFinite(a) || !Number.isFinite(b)) continue;
        if (Math.abs(a - b) > 1e-5 * Math.max(1, Math.abs(a), Math.abs(b))) return false;
        ok++;
    }
    return ok >= 2 ? true : null;
}

// ---------------------------------------------------------------- public API

function primeTex(v, order = 1, partial = false, name = 'f') {
    if (partial) return order === 1 ? `\\frac{\\partial ${name}}{\\partial ${v}}` : `\\frac{\\partial^{${order}} ${name}}{\\partial ${v}^{${order}}}`;
    const marks = order <= 3 ? "'".repeat(order) : `^{(${order})}`;
    return `${name}${marks}(${v})`;
}

function answerStep(title, tex) {
    const s = step({ title, tex, rule: 'answer' });
    s.final = true;
    return s;
}

/**
 * Derivative of node (AST or string) by v. opts: {steps = false, simplify = true, partial = false}.
 * → {result (display node), steps (Step[], empty unless asked), verified, tex ("f'(x) = …", string | {ru, en})}.
 * Other letters are constants (a partial derivative). Throws MathError for equations/lists and fact().
 */
export function derivative(node, v = 'x', opts = {}) {
    node = asNode(node);
    checkExpr(node);
    const wantSteps = !!opts.steps;
    const partial = !!opts.partial;
    const fast = quickDerivative(node, v);
    let result;
    const steps = [];
    if (wantSteps || opts.simplify === false) {
        const r = dS(node, { v });
        result = opts.simplify === false ? r.raw : r.res;
        if (wantSteps) {
            const others = freeVars(node).filter((w) => w !== v);
            steps.push(step({
                title: T_('Что дифференцируем', 'What we differentiate'),
                tex: bt((L) => `f(${v}) = ${calcTex(node, L)}`),
                text: others.length
                    ? T_(`Ищем производную по ${v}. Остальные буквы (${others.join(', ')}) считаем постоянными — это частная производная.`, `We differentiate with respect to ${v}. The other letters (${others.join(', ')}) are treated as constants: this is a partial derivative.`)
                    : T_(`Ищем производную по ${v}: разбираем выражение от внешней операции к внутренним.`, `We differentiate with respect to ${v}, going from the outermost operation inwards.`),
                rule: 'start',
            }));
            if (r.step) steps.push(r.step);
        }
        if (opts.simplify !== false) {
            // the independent canonical derivative sometimes tidies up better than the rule tree
            const alt = niceForm(fast, v);
            if (score(alt) + penalty(alt) < score(result) + penalty(result) && agree(alt, result, v, { tol: 1e-8 }).ok !== false) {
                if (wantSteps) {
                    const from = result;
                    steps.push(step({
                        title: T_('Упрощаем', 'Simplify'),
                        tex: bt((L) => `${calcTex(from, L)} = ${calcTex(alt, L)}`),
                        text: T_('Раскрываем скобки, приводим к общему знаменателю и собираем подобные.', 'Expand, bring to a common denominator and collect like terms.'),
                        rule: 'simplify',
                    }));
                }
                result = alt;
            }
        }
    } else {
        result = niceForm(fast, v);
    }
    let verified = true;
    if (agree(result, fast, v, { tol: 1e-8 }).ok === false) {
        // never show a result that disagrees with the independent computation
        result = niceForm(fast, v);
        verified = agree(result, fast, v, { tol: 1e-8 }).ok !== false;
    }
    if (numericCheck(node, result, v) === false) verified = false;
    const tex = bt((L) => `${primeTex(v, 1, partial)} = ${calcTex(result, L)}`);
    if (wantSteps) steps.push(answerStep(T_('Ответ', 'Answer'), tex));
    return { result, steps, verified, tex };
}

/** Partial derivative ∂f/∂v (the other letters are constants): derivative() with ∂ notation. */
export function partialDerivative(node, v = 'x', opts = {}) {
    return derivative(node, v, { ...opts, partial: true });
}

/**
 * n-th derivative (1 ≤ n ≤ 30). → {result, list: [f', f'', …], steps, verified, tex}. Each order
 * differentiates the previous answer as written; with opts.steps every order is a step holding its rule tree.
 */
export function derivativeN(node, v = 'x', n = 2, opts = {}) {
    node = asNode(node);
    checkExpr(node);
    if (!Number.isInteger(n) || n < 1 || n > 30) throw new MathError({ ru: 'Порядок производной — целое число от 1 до 30', en: 'The order must be a whole number from 1 to 30' }, null, null, 'range');
    let cur = node;
    const list = [];
    const steps = [];
    let verified = true;
    for (let k = 1; k <= n; k++) {
        const r = derivative(cur, v, { steps: !!opts.steps });
        verified = verified && r.verified;
        list.push(r.result);
        if (opts.steps) {
            const prevTex = k === 1 ? null : primeTex(v, k - 1);
            const src = cur;
            steps.push(step({
                title: T_(`Производная ${k}-го порядка`, `Derivative of order ${k}`),
                tex: bt((L) => `${primeTex(v, k)} = \\left(${prevTex ?? calcTex(src, L)}\\right)' = ${calcTex(r.result, L)}`),
                text: k === 1 ? undefined : T_('Дифференцируем предыдущую производную.', 'Differentiate the previous derivative.'),
                rule: 'order',
                sub: r.steps.filter((s) => s.rule !== 'start' && s.rule !== 'answer'),
            }));
        }
        cur = r.result;
        if (isZero(r.result)) {
            for (let j = k + 1; j <= n; j++) list.push(N0);
            break;
        }
    }
    const result = list[n - 1];
    const tex = bt((L) => `${primeTex(v, n)} = ${calcTex(result, L)}`);
    if (opts.steps) steps.push(answerStep(T_('Ответ', 'Answer'), tex));
    return { result, list, steps, verified, tex };
}

/** ∇f → {result: list node of the partials, components: {x: node, …}, vars, steps, tex}. vars default: freeVars. */
export function gradientOf(node, vars = null, opts = {}) {
    node = asNode(node);
    checkExpr(node);
    const vs = vars ?? freeVars(node);
    if (!vs.length) throw new MathError({ ru: 'В выражении нет переменных', en: 'The expression has no variables' }, null, null, 'no-var');
    const components = {};
    const steps = [];
    for (const w of vs) {
        const r = partialDerivative(node, w, { steps: !!opts.steps });
        components[w] = r.result;
        if (opts.steps) {
            steps.push(step({
                title: T_(`Частная производная по ${w}`, `Partial derivative with respect to ${w}`),
                tex: r.tex,
                text: T_(`Дифференцируем по ${w}, остальные переменные считаем постоянными.`, `Differentiate with respect to ${w}, keeping the other variables constant.`),
                rule: 'partial',
                sub: r.steps.filter((s) => s.rule !== 'start' && s.rule !== 'answer'),
            }));
        }
    }
    const result = Object.freeze({ type: 'list', items: Object.freeze(vs.map((w) => components[w])) });
    const tex = bt((L) => {
        const sep = L === 'ru' ? ';\\ ' : ',\\ ';
        return `\\nabla f = \\left(${vs.map((w) => primeTex(w, 1, true)).join(sep)}\\right) = \\left(${vs.map((w) => calcTex(components[w], L)).join(sep)}\\right)`;
    });
    if (opts.steps) steps.push(answerStep(T_('Градиент', 'Gradient'), tex));
    return { result, components, vars: vs, steps, tex };
}

/**
 * Tangent to y = f(v) at v = a (number, string or node): {k, b (nodes), point: {x, y}, line (node), tex, steps}.
 * Throws MathError 'undefined' when f(a) is not defined and 'no-derivative' when f'(a) is not finite.
 */
export function tangentLine(node, v = 'x', a = 0, opts = {}) {
    node = asNode(node);
    checkExpr(node);
    const A = typeof a === 'string' ? parse(a) : toNode(a);
    const noF = () => new MathError({ ru: 'Функция не определена в этой точке', en: 'The function is not defined at this point' }, null, null, 'undefined');
    let fa;
    try {
        fa = simplify(substitute(node, { [v]: A }));
    } catch {
        throw noF();
    }
    const others = freeVars(node).filter((w) => w !== v);
    const env = Object.fromEntries(others.map((w) => [w, 1.3]));
    if (!Number.isFinite(evaluate(fa, env))) throw noF();
    const d = derivative(node, v, { steps: !!opts.steps });
    let k = null;
    try {
        k = simplify(substitute(quickDerivative(node, v), { [v]: A }));
    } catch {
        k = null;
    }
    if (!k || !Number.isFinite(evaluate(k, env))) {
        throw new MathError({ ru: 'В этой точке у функции нет конечной производной: касательная вертикальна или её нет', en: 'The function has no finite derivative here: the tangent is vertical or does not exist' }, null, null, 'no-derivative');
    }
    const C = canonContext();
    const X = sym(v);
    const b = C.add([fa, C.mul([NM1, k, A])]);
    const line = niceForm(C.add([C.mul([k, X]), b]), v);
    const tex = bt((L) => `y = ${calcTex(line, L)}`);
    const steps = [];
    if (opts.steps) {
        const at = (L) => calcTex(A, L);
        steps.push(step({
            title: T_('Уравнение касательной', 'Equation of the tangent'),
            tex: bt((L) => `y = f(${at(L)}) + f'(${at(L)})\\,${isZero(A) ? v : `(${v} ${negLeading(A) ? '+ ' + calcTex(simplify(neg(A)), L) : '- ' + at(L)})`}`),
            text: T_('Касательная проходит через точку графика, а её наклон равен производной в этой точке.', 'The tangent passes through the point of the graph, and its slope equals the derivative at that point.'),
            rule: 'tangent-formula',
        }));
        steps.push(step({ title: T_('Значение функции', 'Value of the function'), tex: bt((L) => `f(${at(L)}) = ${calcTex(fa, L)}`), rule: 'value' }));
        steps.push(step({ title: T_('Производная', 'Derivative'), tex: d.tex, rule: 'derivative', sub: d.steps.filter((s) => s.rule !== 'start' && s.rule !== 'answer') }));
        steps.push(step({
            title: T_('Угловой коэффициент', 'Slope'),
            tex: bt((L) => `k = f'(${at(L)}) = ${calcTex(k, L)}`),
            text: T_('Подставляем точку в производную: это тангенс угла наклона касательной.', 'Substitute the point into the derivative: this is the slope of the tangent.'),
            rule: 'slope',
        }));
        steps.push(answerStep(T_('Касательная', 'Tangent line'), tex));
    }
    return { k, b, point: { x: A, y: fa }, line, tex, steps };
}
