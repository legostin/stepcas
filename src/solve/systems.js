// solve/systems — systems of equations: linear (Gauss, Cramer, substitution) and a linear with a quadratic.

import { parse } from '../core/parse.js';
import { linearForm, Poly } from '../core/poly.js';
import { rel, num, substitute, add, neg, freeVars, sym, mul, div, nodeKey } from '../core/ast.js';
import { bigLcm, Q, MathError } from '../core/rational.js';
import { toText } from '../core/print.js';
import { matSolveCramer, Matrix, matSolve } from '../linalg/index.js';
import { S, T, approxOf, byLang, close, exactZero, pick, simpOr, tex } from './common.js';
import { sideValue } from './domain.js';
import { solveEquation } from './equation.js';
import { monoNode, solveLinearSchool, sumNode } from './polynomial.js';
import { rootsTex } from './roots.js';

// ---------------------------------------------------------------- systems of equations

const VAR_ORDER = ['x', 'y', 'z', 't', 'u', 'v', 'w'];

function sortVars(vs) {
    return [...vs].sort((a, b) => {
        const ia = VAR_ORDER.indexOf(a);
        const ib = VAR_ORDER.indexOf(b);
        if (ia >= 0 || ib >= 0) return (ia < 0 ? 99 : ia) - (ib < 0 ? 99 : ib);
        return a.localeCompare(b, 'en', { numeric: true });
    });
}

function relsOf(input, varsHint = []) {
    const long = varsHint.filter((x) => x.length > 1);
    const one = (x) => (typeof x === 'string' ? parse(x, { vars: long }) : x);
    const flat = (n) => (n.type === 'list' ? [...n.items] : [n]);
    if (Array.isArray(input)) return input.flatMap((x) => flat(one(x)));
    return flat(one(input));
}

/** Rows {a: Q[], b: Q} of a linear system (null for a non-linear equation). */
function linearRows(rels, vars) {
    return rels.map((r) => {
        if (r.type !== 'rel' || r.op !== '=') return null;
        const lf = linearForm(r, vars);
        return lf && { a: vars.map((x) => lf.coeffs[x]), b: lf.constant.neg() };
    });
}

function linEqNode(a, b, vars) {
    const terms = [];
    a.forEach((q, j) => {
        if (!q.isZero()) terms.push(monoNode(q, vars[j]));
    });
    return rel('=', sumNode(terms), num(b));
}

export const casesTex = (lines) => (lines.length > 1 ? `\\begin{cases} ${lines.join(' \\\\ ')} \\end{cases}` : lines[0]);
const systemTexB = (rows, vars) => byLang((l) => casesTex(rows.map((r) => tex(linEqNode(r.a, r.b, vars), l))));
const tupleTex = (items, lang) => `\\left(${items.join(lang === 'ru' ? ';\\ ' : ',\\ ')}\\right)`;
const ORD = { ru: ['первого', 'второго', 'третьего'], en: ['first', 'second', 'third'] };
const ORD_ACC = { ru: ['первое', 'второе', 'третье'], en: ['first', 'second', 'third'] };

/** Substitute a solution into every equation → {ok, step}. */
function checkSystem(rels, sol) {
    const items = rels.map((r) => {
        const Ls = substitute(r.lhs, sol);
        const Rs = substitute(r.rhs, sol);
        const z = exactZero(add(Ls, neg(Rs)));
        const ok = z === true || (z === null && close(approxOf(Ls), approxOf(Rs), 1e-9));
        const tx = byLang((l) => {
            const lv = sideValue(Ls);
            const rv = sideValue(Rs);
            const left = [tex(Ls, l)];
            if (lv && tex(lv, l) !== left[0]) left.push(tex(lv, l));
            const rightT = rv ? tex(rv, l) : tex(Rs, l);
            const rConst = freeVars(r.rhs).length === 0;
            if (ok && rConst && left[left.length - 1] === rightT) return `${left.join(' = ')}\\ \\checkmark`;
            return `${left.join(' = ')} ${ok ? '=' : '\\ne'} ${rightT}${ok ? '\\ \\checkmark' : ''}`;
        });
        return { ok, tex: tx };
    });
    const ok = items.every((x) => x.ok);
    return {
        ok,
        items,
        step: S(T('Проверка', 'Check'), {
            tex: byLang((l) => (items.length > 1 ? `\\begin{aligned} ${items.map((x) => `& ${pick(x.tex, l)}`).join(' \\\\ ')} \\end{aligned}` : pick(items[0].tex, l))),
            text: ok ? T('Подставили найденные значения в каждое уравнение — все равенства верны.', 'We substituted the values into every equation: all of them hold.') : T('Не все равенства выполняются.', 'Not all the equalities hold.'),
        }),
    };
}

function sysSubstitution(rows, vars) {
    let best = null;
    for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
            const a = rows[i].a[j];
            if (a.isZero()) continue;
            const score = a.abs().isOne() ? 0 : a.isInt() ? Number(a.abs().n) : 1000;
            if (!best || score < best.score) best = { i, j, score };
        }
    }
    if (!best) return null;
    const { i, j } = best;
    const k = 1 - j;
    const o = 1 - i;
    const [vj, vk] = [vars[j], vars[k]];
    const aij = rows[i].a[j];
    const aik = rows[i].a[k];
    const Y = sym(vk);
    const numer = simpOr(add(num(rows[i].b), mul(num(aik.neg()), Y)));
    const shown = aij.isOne() ? numer : aij.eq(-1) ? simpOr(neg(numer)) : div(numer, num(aij));
    const expr = simpOr(shown);
    const steps = [];
    steps.push(S(T(`Выражаем $${vj}$ из ${ORD.ru[i]} уравнения`, `Express $${vj}$ from the ${ORD.en[i]} equation`), { tex: byLang((l) => `${vj} = ${tex(shown, l)}`) }));
    const aoj = rows[o].a[j];
    const aok = rows[o].a[k];
    const lhsNode = sumNode([aoj.isZero() ? null : aoj.isOne() ? shown : mul(num(aoj), shown), aok.isZero() ? null : monoNode(aok, vk)].filter(Boolean));
    steps.push(S(T(`Подставляем ${o === 1 ? 'во' : 'в'} ${ORD_ACC.ru[o]} уравнение`, `Substitute into the ${ORD_ACC.en[o]} equation`), {
        tex: byLang((l) => `${tex(lhsNode, l)} = ${tex(num(rows[o].b), l)}`),
        text: T(`Получилось уравнение с одной неизвестной $${vk}$.`, `This is an equation in one unknown, $${vk}$.`),
    }));
    const A = Poly.fromNode(lhsNode, vk);
    const B = new Poly([rows[o].b]);
    const sub = solveLinearSchool(lhsNode, num(rows[o].b), A, B, { v: vk, domain: 'real', depth: 1 });
    steps.push(S(byLang((l) => (l === 'ru' ? `Решаем его` : 'Solve it')), { tex: byLang((l) => (sub.kind === 'roots' ? rootsTex(sub.roots, vk, l) : sub.kind === 'all' ? (l === 'ru' ? '\\text{верно при любом } ' : '\\text{true for every } ') + vk : l === 'ru' ? '\\text{решений нет}' : '\\text{no solutions}')), sub: sub.steps }));
    if (sub.kind === 'none') {
        steps.push(S(T('Получилось неверное равенство — система решений не имеет', 'A false equality: the system has no solutions'), { text: T('Геометрически это две параллельные прямые.', 'Geometrically these are two parallel lines.') }));
        return { kind: 'none', steps };
    }
    if (sub.kind === 'all') {
        steps.push(S(T('Уравнение верно при любом значении — решений бесконечно много', 'The equation holds for any value: infinitely many solutions'), {
            tex: byLang((l) => `${vk} \\in \\mathbb{R},\\quad ${vj} = ${tex(expr, l)}`),
            text: T('Оба уравнения задают одну и ту же прямую.', 'Both equations describe the same line.'),
        }));
        return { kind: 'infinite', steps, general: { [vk]: Y, [vj]: expr }, params: [vk] };
    }
    const yk = sub.roots[0].node;
    const yj = simpOr(substitute(expr, { [vk]: yk }));
    steps.push(S(T(`Находим $${vj}$`, `Find $${vj}$`), { tex: byLang((l) => `${vj} = ${tex(substitute(shown, { [vk]: yk }), l)} = ${tex(yj, l)}`) }));
    return { kind: 'unique', steps, solution: { [vj]: yj, [vk]: yk } };
}

function sysAddition(rows0, vars) {
    const steps = [];
    let rows = rows0.map((r) => {
        let den = 1n;
        for (const q of [...r.a, r.b]) den = bigLcm(den, q.d);
        return den > 1n ? { a: r.a.map((q) => q.mul(new Q(den))), b: r.b.mul(new Q(den)), den } : { ...r, den: 1n };
    });
    if (rows.some((r) => r.den > 1n)) steps.push(S(T('Избавляемся от дробей', 'Clear the fractions'), { tex: systemTexB(rows, vars) }));
    let pickJ = -1;
    let bestL = null;
    for (let j = 0; j < 2; j++) {
        const [a0, a1] = [rows[0].a[j], rows[1].a[j]];
        if (a0.isZero() || a1.isZero()) continue;
        const L = bigLcm(a0.abs().n, a1.abs().n);
        const score = a0.add(a1).isZero() ? -2n : a0.eq(a1) ? -1n : L;
        if (bestL === null || score < bestL) {
            bestL = score;
            pickJ = j;
        }
    }
    if (pickJ < 0) return null;
    const j = pickJ;
    const k = 1 - j;
    const [a0, a1] = [rows[0].a[j], rows[1].a[j]];
    const L = bigLcm(a0.abs().n, a1.abs().n);
    const m0 = new Q(L / a0.abs().n);
    let m1 = new Q(L / a1.abs().n);
    if (a0.isNeg() === a1.isNeg()) m1 = m1.neg();
    const scaled = [{ a: rows[0].a.map((q) => q.mul(m0)), b: rows[0].b.mul(m0) }, { a: rows[1].a.map((q) => q.mul(m1)), b: rows[1].b.mul(m1) }];
    if (!m0.isOne() || !m1.isOne()) {
        const what = (m, idx, l) => (m.isOne() ? '' : l === 'ru' ? `${ORD_ACC.ru[idx]} уравнение умножаем на $${tex(num(m), l)}$` : `multiply the ${ORD_ACC.en[idx]} equation by $${tex(num(m), l)}$`);
        const parts = (l) => [what(m0, 0, l), what(m1, 1, l)].filter(Boolean).join(l === 'ru' ? ', ' : ' and ');
        steps.push(S(byLang((l) => {
            const p0 = parts(l);
            return l === 'ru' ? p0.charAt(0).toUpperCase() + p0.slice(1) : p0.charAt(0).toUpperCase() + p0.slice(1);
        }), {
            tex: systemTexB(scaled, vars),
            text: T(`Теперь коэффициенты при $${vars[j]}$ противоположны.`, `Now the coefficients of $${vars[j]}$ are opposite.`),
        }));
    }
    const c = scaled[0].a[k].add(scaled[1].a[k]);
    const d = scaled[0].b.add(scaled[1].b);
    steps.push(S(T(`Складываем уравнения: $${vars[j]}$ исчезает`, `Add the equations: $${vars[j]}$ cancels`), { tex: byLang((l) => `${tex(monoNode(c, vars[k]), l)} = ${tex(num(d), l)}`) }));
    if (c.isZero()) {
        if (d.isZero()) {
            const pr = rows0[0].a[j].isZero() ? rows0[1] : rows0[0];
            const expr = simpOr(div(add(num(pr.b), mul(num(pr.a[k].neg()), sym(vars[k]))), num(pr.a[j])));
            steps.push(S(T('Получилось $0 = 0$ — решений бесконечно много', 'We get $0 = 0$: infinitely many solutions'), {
                tex: byLang((l) => `${vars[k]} \\in \\mathbb{R},\\quad ${vars[j]} = ${tex(expr, l)}`),
                text: T('Уравнения задают одну и ту же прямую.', 'The equations describe the same line.'),
            }));
            return { kind: 'infinite', steps, general: { [vars[k]]: sym(vars[k]), [vars[j]]: expr }, params: [vars[k]] };
        }
        steps.push(S(T(`Получилось $0 = ${tex(num(d))}$ — решений нет`, `We get $0 = ${tex(num(d), 'en')}$: no solutions`), { text: T('Прямые параллельны и не пересекаются.', 'The lines are parallel and never meet.') }));
        return { kind: 'none', steps };
    }
    const yk = d.div(c);
    if (!c.isOne()) steps.push(S(T(`Находим $${vars[k]}$`, `Find $${vars[k]}$`), { tex: byLang((l) => `${vars[k]} = ${tex(num(yk), l)}`) }));
    const src = rows0[0].a[j].isZero() ? 1 : 0;
    const r = rows0[src];
    const yj = r.b.sub(r.a[k].mul(yk)).div(r.a[j]);
    const substituted = sumNode([monoNode(r.a[j], vars[j]), r.a[k].isZero() ? null : mul(num(r.a[k]), num(yk))].filter(Boolean));
    steps.push(S(T(`Подставляем $${vars[k]} = ${tex(num(yk))}$ в ${ORD_ACC.ru[src]} уравнение`, `Substitute $${vars[k]} = ${tex(num(yk), 'en')}$ into the ${ORD_ACC.en[src]} equation`), {
        tex: byLang((l) => `${tex(substituted, l)} = ${tex(num(r.b), l)} \\quad\\Rightarrow\\quad ${vars[j]} = ${tex(num(yj), l)}`),
    }));
    return { kind: 'unique', steps, solution: { [vars[j]]: num(yj), [vars[k]]: num(yk) } };
}

/** Replay the row operations of matSolve on the system and show it as equations after each one. */
function withSystems(steps, rows, vars) {
    const W = rows.map((r) => [...r.a, r.b]);
    return steps.map((st) => {
        if (!st.op) return st;
        if (st.op === 'swap') [W[st.i], W[st.j]] = [W[st.j], W[st.i]];
        else if (st.op === 'scale') W[st.i] = W[st.i].map((x) => x.mul(st.k));
        else if (st.op === 'add') W[st.i] = W[st.i].map((x, c) => x.add(st.k.mul(W[st.j][c])));
        const sys = byLang((l) => casesTex(W.map((r) => tex(linEqNode(r.slice(0, -1), r[r.length - 1], vars), l))));
        const t = st.tex;
        return { ...st, tex: byLang((l) => `\\begin{gathered} ${pick(t, l)} \\\\ \\Leftrightarrow\\ ${pick(sys, l)} \\end{gathered}`) };
    });
}

// text is always {ru, en} (a one-unknown answer reads the same in both languages, but callers pick text[lang])
const bothLang = (f) => ({ ru: f('ru'), en: f('en') });
function sysAnswer(res, vars) {
    if (res.kind === 'unique') {
        if (vars.length === 1) {
            const x = vars[0];
            return { tex: byLang((l) => `${x} = ${tex(res.solution[x], l)}`), text: bothLang((l) => `${x} = ${toText(res.solution[x], { lang: l })}`) };
        }
        return {
            tex: byLang((l) => `${tupleTex(vars, l)} = ${tupleTex(vars.map((x) => tex(res.solution[x], l)), l)}`),
            text: bothLang((l) => `(${vars.map((x) => toText(res.solution[x], { lang: l })).join(l === 'ru' ? '; ' : ', ')})`),
        };
    }
    if (res.kind === 'infinite') {
        const g = res.general;
        return {
            tex: byLang((l) => `${tupleTex(vars.map((x) => tex(g[x], l)), l)},\\quad ${res.params.join(',\\ ')} \\in \\mathbb{R}`),
            text: bothLang((l) => `(${vars.map((x) => toText(g[x], { lang: l })).join(l === 'ru' ? '; ' : ', ')}), ${res.params.join(', ')} ∈ R`),
        };
    }
    if (res.kind === 'none') return { tex: T('\\text{решений нет}', '\\text{no solutions}'), text: T('Решений нет.', 'No solutions.') };
    return { tex: '', text: res.reason ?? T('Не удалось решить.', 'Could not solve.') };
}

/**
 * A system of linear equations. rels: array of equations (text or rel nodes) or one text with ";" or newlines.
 * vars: the unknowns (default: the letters found, x, y, z first). opts: {steps, method: 'gauss' | 'substitution' |
 * 'addition' | 'cramer'} (default: substitution or addition for 2×2, Gauss otherwise).
 * → {kind: 'unique'|'none'|'infinite'|'unsupported', solution?: {x: node, …}, general?: {x: node in params},
 *    params?: [names], method, vars, steps, check, answer: {tex, text}, reason?}
 */
export function solveLinearSystem(input, vars = null, opts = {}) {
    const rels = relsOf(input, vars ?? []);
    const withSteps = opts.steps !== false;
    if (!vars) vars = sortVars(new Set(rels.flatMap((r) => freeVars(r))));
    const done = (res) => {
        const out = { vars, steps: [], check: [], ...res };
        out.answer = sysAnswer(out, vars);
        if (out.kind === 'unsupported') out.steps.push(S(T('Не удалось решить', 'Could not solve'), { text: out.reason, final: true }));
        else out.steps.push(S(T('Ответ', 'Answer'), { tex: out.answer.tex, final: true }));
        if (!withSteps) out.steps = [];
        return out;
    };
    if (!rels.length || !vars.length) return done({ kind: 'unsupported', reason: T('Нет уравнений с неизвестными.', 'There are no equations with unknowns.') });
    const rows = linearRows(rels, vars);
    if (rows.some((r) => !r)) {
        const pair = rels.length === 2 && vars.length === 2 && rows.some(Boolean);
        return done({
            kind: 'unsupported',
            reason: pair
                ? T('Одно из уравнений не линейное — такую систему решают подстановкой: выражают неизвестную из линейного уравнения.', 'One of the equations is not linear: such a system is solved by substitution, expressing an unknown from the linear equation.')
                : T('Не все уравнения линейные, а метод Гаусса и формулы Крамера работают только для линейных систем.', 'Not all the equations are linear, and Gaussian elimination and Cramer’s rule work only for linear systems.'),
        });
    }
    const m = rows.length;
    const n = vars.length;
    let method = opts.method ?? (m === 2 && n === 2 ? (rows.some((r) => r.a.some((q) => q.abs().isOne())) ? 'substitution' : 'addition') : 'gauss');
    if ((method === 'substitution' || method === 'addition') && !(m === 2 && n === 2)) method = 'gauss';
    if (method === 'cramer' && (m !== n || n > 3)) method = 'gauss';
    const steps = [];
    const standard = rels.every((r) => r.rhs.type === 'num' && nodeKey(simpOr(r.lhs)) === nodeKey(simpOr(linEqNode(linearRows([r], vars)[0].a, Q.ZERO, vars).lhs)));
    if (!standard) steps.push(S(T('Приводим каждое уравнение к виду «неизвестные слева, число справа»', 'Bring each equation to the form "unknowns on the left, a number on the right"'), { tex: systemTexB(rows, vars) }));
    let res = null;
    if (method === 'substitution') res = sysSubstitution(rows, vars);
    else if (method === 'addition') res = sysAddition(rows, vars);
    else if (method === 'cramer') {
        const cr = matSolveCramer(Matrix.from(rows.map((r) => r.a)), rows.map((r) => r.b), { steps: true, vars });
        if (cr.kind === 'unique') res = { kind: 'unique', steps: cr.steps.filter((s) => s.rule !== 'answer').concat(cr.steps.filter((s) => s.rule === 'answer').map((s) => ({ ...s, title: T('Находим неизвестные', 'Find the unknowns') }))), solution: Object.fromEntries(vars.map((x, j) => [x, num(cr.x[j])])) };
        else {
            steps.push(...cr.steps);
            method = 'gauss';
        }
    }
    if (!res) {
        method = method === 'cramer' ? 'gauss' : method;
        let ms;
        try {
            ms = matSolve(Matrix.from(rows.map((r) => r.a)), rows.map((r) => r.b), { steps: true, vars });
        } catch (e) {
            if (!(e instanceof MathError)) throw e;
            return done({ kind: 'unsupported', reason: e.msg, method, steps });
        }
        const st = withSystems(ms.steps.filter((s) => s.rule !== 'check'), rows, vars);
        if (ms.kind === 'unique') res = { kind: 'unique', steps: st, solution: Object.fromEntries(vars.map((x, j) => [x, num(ms.x[j])])) };
        else if (ms.kind === 'none') res = { kind: 'none', steps: st };
        else {
            const general = {};
            vars.forEach((x, j) => {
                const p = ms.params.find((pp) => pp.index === j);
                general[x] = p ? sym(p.name) : simpOr(add(num(ms.x[j]), ...ms.params.map((pp, k) => mul(num(ms.basis[k][j]), sym(pp.name)))));
            });
            res = { kind: 'infinite', steps: st, general, params: ms.params.map((p) => p.name) };
        }
        method = 'gauss';
    }
    steps.push(...res.steps);
    const out = { ...res, steps, method };
    if (res.kind === 'unique') {
        const ch = checkSystem(rels, res.solution);
        steps.push(ch.step);
        out.check = ch.items.map((x) => ({ ok: x.ok, tex: x.tex }));
    }
    return done(out);
}

/**
 * A linear and a non-linear equation in two unknowns, by substitution: express one unknown from the
 * linear equation and substitute it into the other. → {kind: 'solutions'|'none'|'unsupported',
 * solutions: [{x: node, y: node}], steps, check, answer, reason?}
 */
export function solveSystem2(input, vars = null, opts = {}) {
    const rels = relsOf(input, vars ?? []);
    const withSteps = opts.steps !== false;
    if (!vars) vars = sortVars(new Set(rels.flatMap((r) => freeVars(r))));
    const done = (res) => {
        const out = { vars, steps: [], check: [], solutions: [], ...res };
        if (out.kind === 'solutions') {
            out.answer = {
                tex: byLang((l) => out.solutions.map((s) => tupleTex(vars.map((x) => tex(s[x], l)), l)).join(l === 'ru' ? ';\\quad ' : ',\\quad ')),
                text: byLang((l) => out.solutions.map((s) => `(${vars.map((x) => toText(s[x], { lang: l })).join(l === 'ru' ? '; ' : ', ')})`).join(l === 'ru' ? '; ' : ', ')),
            };
        } else if (out.kind === 'none') out.answer = { tex: T('\\text{решений нет}', '\\text{no solutions}'), text: T('Решений нет.', 'No solutions.') };
        else out.answer = { tex: '', text: out.reason };
        out.steps.push(out.kind === 'unsupported' ? S(T('Не удалось решить', 'Could not solve'), { text: out.reason, final: true }) : S(T('Ответ', 'Answer'), { tex: out.answer.tex, final: true }));
        if (!withSteps) out.steps = [];
        return out;
    };
    if (rels.length !== 2 || vars.length !== 2) return done({ kind: 'unsupported', reason: T('Нужны два уравнения с двумя неизвестными.', 'Two equations in two unknowns are needed.') });
    const rows = linearRows(rels, vars);
    if (rows.every(Boolean)) {
        const r = solveLinearSystem(rels, vars, opts);
        if (r.kind === 'unique') return done({ kind: 'solutions', solutions: [r.solution], steps: r.steps.slice(0, -1), check: r.check });
        if (r.kind === 'none') return done({ kind: 'none', steps: r.steps.slice(0, -1) });
        return done({ kind: 'unsupported', reason: T('Решений бесконечно много — это случай линейной системы.', 'Infinitely many solutions: see the linear system solver.'), steps: r.steps.slice(0, -1) });
    }
    const li = rows.findIndex(Boolean);
    if (li < 0) return done({ kind: 'unsupported', reason: T('Ни одно из уравнений не линейное — способ подстановки здесь не сработает.', 'Neither equation is linear, so substitution will not work here.') });
    const other = rels[1 - li];
    const row = rows[li];
    let j = row.a.findIndex((q) => q.abs().isOne());
    if (j < 0) j = row.a.findIndex((q) => !q.isZero());
    if (j < 0) return done({ kind: 'unsupported', reason: T('Линейное уравнение не содержит неизвестных.', 'The linear equation has no unknowns.') });
    const k = 1 - j;
    const [vj, vk] = [vars[j], vars[k]];
    const expr = simpOr(div(add(num(row.b), mul(num(row.a[k].neg()), sym(vk))), num(row.a[j])));
    const steps = [S(T(`Выражаем $${vj}$ из линейного уравнения`, `Express $${vj}$ from the linear equation`), { tex: byLang((l) => `${vj} = ${tex(expr, l)}`) })];
    const subst = rel('=', substitute(other.lhs, { [vj]: expr }), substitute(other.rhs, { [vj]: expr }));
    steps.push(S(T('Подставляем в другое уравнение', 'Substitute into the other equation'), { tex: byLang((l) => tex(subst, l)), text: T(`Осталась одна неизвестная — $${vk}$.`, `One unknown is left: $${vk}$.`) }));
    const r = solveEquation(subst, vk, { steps: true });
    steps.push(S(byLang((l) => (l === 'ru' ? `Решаем уравнение относительно $${vk}$` : `Solve for $${vk}$`)), { tex: r.answer.tex, sub: r.steps.slice(0, -1) }));
    if (r.kind === 'none') return done({ kind: 'none', steps });
    if (r.kind !== 'roots' || r.families || r.roots.some((x) => x.approxOnly)) {
        return done({ kind: 'unsupported', steps, reason: r.reason ?? T('Не удалось найти точные корни уравнения с одной неизвестной.', 'Could not find exact roots of the equation in one unknown.') });
    }
    const solutions = r.roots.map((x) => ({ [vk]: x.node, [vj]: simpOr(substitute(expr, { [vk]: x.node })) }))
        .sort((a, b) => approxOf(a[vars[0]]) - approxOf(b[vars[0]]) || approxOf(a[vars[1]]) - approxOf(b[vars[1]]));
    steps.push(S(T(`Находим $${vj}$ для каждого корня`, `Find $${vj}$ for each root`), {
        tex: byLang((l) => solutions.map((s) => `${vk} = ${tex(s[vk], l)}:\\ ${vj} = ${tex(s[vj], l)}`).join(l === 'ru' ? ';\\quad ' : ',\\quad ')),
    }));
    const check = [];
    const good = [];
    for (const s of solutions) {
        const ch = checkSystem(rels, s);
        check.push({ solution: s, ok: ch.ok, items: ch.items });
        if (ch.ok) good.push(s);
        steps.push(S(byLang((l) => (l === 'ru' ? 'Проверка ' : 'Check ') + `$${tupleTex(vars.map((x) => tex(s[x], l)), l)}$`), { tex: ch.step.tex, text: ch.step.text }));
    }
    return done({ kind: good.length ? 'solutions' : 'none', solutions: good, steps, check });
}