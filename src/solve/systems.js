// solve/systems — systems of equations: linear (Gauss, Cramer, substitution) and a linear with a quadratic.

import { parse } from '../core/parse.js';
import { linearForm, Poly } from '../core/poly.js';
import { rel, num, substitute, add, neg, freeVars, sym, mul, div, nodeKey } from '../core/ast.js';
import { bigLcm, Q, MathError } from '../core/rational.js';
import { toText } from '../core/print.js';
import { matSolveCramer, Matrix, matSolve } from '../linalg/index.js';
import { S, approxOf, close, exactZero, pick, simpOr, tex } from './common.js';
import { sideValue } from './domain.js';
import { solveEquation } from './equation.js';
import { monoNode, solveLinearSchool, sumNode } from './polynomial.js';
import { rootsTex } from './roots.js';
import { msg, notation, eachLanguage } from '../i18n/index.js';

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
const systemTexB = (rows, vars) => eachLanguage((l) => casesTex(rows.map((r) => tex(linEqNode(r.a, r.b, vars), l))));
const tupleTex = (items, lang) => `\\left(${items.join(notation(lang).listTex)}\\right)`;

/** Substitute a solution into every equation → {ok, step}. */
function checkSystem(rels, sol) {
    const items = rels.map((r) => {
        const Ls = substitute(r.lhs, sol);
        const Rs = substitute(r.rhs, sol);
        const z = exactZero(add(Ls, neg(Rs)));
        const ok = z === true || (z === null && close(approxOf(Ls), approxOf(Rs), 1e-9));
        const tx = eachLanguage((l) => {
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
        step: S(msg('solve.systems.check'), {
            tex: eachLanguage((l) => (items.length > 1 ? `\\begin{aligned} ${items.map((x) => `& ${pick(x.tex, l)}`).join(' \\\\ ')} \\end{aligned}` : pick(items[0].tex, l))),
            text: ok ? msg('solve.systems.we_substituted_values_into_every_equation') : msg('solve.systems.not_all_equalities_hold'),
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
    steps.push(S(msg('solve.systems.express_from_equation', { vj, n: i + 1 }), { tex: eachLanguage((l) => `${vj} = ${tex(shown, l)}`) }));
    const aoj = rows[o].a[j];
    const aok = rows[o].a[k];
    const lhsNode = sumNode([aoj.isZero() ? null : aoj.isOne() ? shown : mul(num(aoj), shown), aok.isZero() ? null : monoNode(aok, vk)].filter(Boolean));
    steps.push(S(msg('solve.systems.substitute_into_equation', { n: o + 1 }), {
        tex: eachLanguage((l) => `${tex(lhsNode, l)} = ${tex(num(rows[o].b), l)}`),
        text: msg('solve.systems.this_is_equation_in_one_unknown', { vk }),
    }));
    const A = Poly.fromNode(lhsNode, vk);
    const B = new Poly([rows[o].b]);
    const sub = solveLinearSchool(lhsNode, num(rows[o].b), A, B, { v: vk, domain: 'real', depth: 1 });
    steps.push(S(eachLanguage((l) => (msg('solve.systems.solve_it').in(l))), { tex: eachLanguage((l) => (sub.kind === 'roots' ? rootsTex(sub.roots, vk, l) : sub.kind === 'all' ? (msg('solve.systems.true_for_every').in(l)) + vk : msg('solve.systems.no_solutions').in(l))), sub: sub.steps }));
    if (sub.kind === 'none') {
        steps.push(S(msg('solve.systems.false_equality_system_has_no_solutions'), { text: msg('solve.systems.geometrically_these_are_two_parallel_lines') }));
        return { kind: 'none', steps };
    }
    if (sub.kind === 'all') {
        steps.push(S(msg('solve.systems.equation_holds_for_any_value_infinitely'), {
            tex: eachLanguage((l) => `${vk} \\in \\mathbb{R},\\quad ${vj} = ${tex(expr, l)}`),
            text: msg('solve.systems.both_equations_describe_same_line'),
        }));
        return { kind: 'infinite', steps, general: { [vk]: Y, [vj]: expr }, params: [vk] };
    }
    const yk = sub.roots[0].node;
    const yj = simpOr(substitute(expr, { [vk]: yk }));
    steps.push(S(msg('solve.systems.find', { vj }), { tex: eachLanguage((l) => `${vj} = ${tex(substitute(shown, { [vk]: yk }), l)} = ${tex(yj, l)}`) }));
    return { kind: 'unique', steps, solution: { [vj]: yj, [vk]: yk } };
}

function sysAddition(rows0, vars) {
    const steps = [];
    const rows = rows0.map((r) => {
        let den = 1n;
        for (const q of [...r.a, r.b]) den = bigLcm(den, q.d);
        return den > 1n ? { a: r.a.map((q) => q.mul(new Q(den))), b: r.b.mul(new Q(den)), den } : { ...r, den: 1n };
    });
    if (rows.some((r) => r.den > 1n)) steps.push(S(msg('solve.systems.clear_fractions'), { tex: systemTexB(rows, vars) }));
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
        const what = (m, idx, l) => (m.isOne() ? '' : msg('solve.systems.multiply_equation_by', { n: idx + 1, k: tex(num(m), l) }).in(l));
        const parts = (l) => [what(m0, 0, l), what(m1, 1, l)].filter(Boolean).join(msg('solve.systems.and').in(l));
        steps.push(S(eachLanguage((l) => {
            const p0 = parts(l);
            return l === 'ru' ? p0.charAt(0).toUpperCase() + p0.slice(1) : p0.charAt(0).toUpperCase() + p0.slice(1);
        }), {
            tex: systemTexB(scaled, vars),
            text: msg('solve.systems.now_coefficients_of_are_opposite', { p: vars[j] }),
        }));
    }
    const c = scaled[0].a[k].add(scaled[1].a[k]);
    const d = scaled[0].b.add(scaled[1].b);
    steps.push(S(msg('solve.systems.add_equations_cancels', { p: vars[j] }), { tex: eachLanguage((l) => `${tex(monoNode(c, vars[k]), l)} = ${tex(num(d), l)}`) }));
    if (c.isZero()) {
        if (d.isZero()) {
            const pr = rows0[0].a[j].isZero() ? rows0[1] : rows0[0];
            const expr = simpOr(div(add(num(pr.b), mul(num(pr.a[k].neg()), sym(vars[k]))), num(pr.a[j])));
            steps.push(S(msg('solve.systems.we_get_infinitely_many_solutions'), {
                tex: eachLanguage((l) => `${vars[k]} \\in \\mathbb{R},\\quad ${vars[j]} = ${tex(expr, l)}`),
                text: msg('solve.systems.equations_describe_same_line'),
            }));
            return { kind: 'infinite', steps, general: { [vars[k]]: sym(vars[k]), [vars[j]]: expr }, params: [vars[k]] };
        }
        steps.push(S(msg('solve.systems.we_get_no_solutions', { p: (lng) => tex(num(d), lng) }), { text: msg('solve.systems.lines_are_parallel_and_never_meet') }));
        return { kind: 'none', steps };
    }
    const yk = d.div(c);
    if (!c.isOne()) steps.push(S(msg('solve.systems.find_2', { p: vars[k] }), { tex: eachLanguage((l) => `${vars[k]} = ${tex(num(yk), l)}`) }));
    const src = rows0[0].a[j].isZero() ? 1 : 0;
    const r = rows0[src];
    const yj = r.b.sub(r.a[k].mul(yk)).div(r.a[j]);
    const substituted = sumNode([monoNode(r.a[j], vars[j]), r.a[k].isZero() ? null : mul(num(r.a[k]), num(yk))].filter(Boolean));
    steps.push(S(msg('solve.systems.substitute_into_equation_2', { v: vars[k], value: (lng) => tex(num(yk), lng), n: src + 1 }), {
        tex: eachLanguage((l) => `${tex(substituted, l)} = ${tex(num(r.b), l)} \\quad\\Rightarrow\\quad ${vars[j]} = ${tex(num(yj), l)}`),
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
        const sys = eachLanguage((l) => casesTex(W.map((r) => tex(linEqNode(r.slice(0, -1), r[r.length - 1], vars), l))));
        const t = st.tex;
        return { ...st, tex: eachLanguage((l) => `\\begin{gathered} ${pick(t, l)} \\\\ \\Leftrightarrow\\ ${pick(sys, l)} \\end{gathered}`) };
    });
}

// text is always {ru, en} (a one-unknown answer reads the same in both languages, but callers pick text[lang])
const bothLang = (f) => ({ ru: f('ru'), en: f('en') });
function sysAnswer(res, vars) {
    if (res.kind === 'unique') {
        if (vars.length === 1) {
            const x = vars[0];
            return { tex: eachLanguage((l) => `${x} = ${tex(res.solution[x], l)}`), text: bothLang((l) => `${x} = ${toText(res.solution[x], { lang: l })}`) };
        }
        return {
            tex: eachLanguage((l) => `${tupleTex(vars, l)} = ${tupleTex(vars.map((x) => tex(res.solution[x], l)), l)}`),
            text: bothLang((l) => `(${vars.map((x) => toText(res.solution[x], { lang: l })).join(notation(l).listText)})`),
        };
    }
    if (res.kind === 'infinite') {
        const g = res.general;
        return {
            tex: eachLanguage((l) => `${tupleTex(vars.map((x) => tex(g[x], l)), l)},\\quad ${res.params.join(',\\ ')} \\in \\mathbb{R}`),
            text: bothLang((l) => `(${vars.map((x) => toText(g[x], { lang: l })).join(notation(l).listText)}), ${res.params.join(', ')} ∈ R`),
        };
    }
    if (res.kind === 'none') return { tex: msg('solve.systems.no_solutions'), text: msg('solve.systems.no_solutions_2') };
    return { tex: '', text: res.reason ?? msg('solve.systems.could_not_solve') };
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
        if (out.kind === 'unsupported') out.steps.push(S(msg('solve.systems.could_not_solve_2'), { text: out.reason, final: true }));
        else out.steps.push(S(msg('solve.systems.answer'), { tex: out.answer.tex, final: true }));
        if (!withSteps) out.steps = [];
        return out;
    };
    if (!rels.length || !vars.length) return done({ kind: 'unsupported', reason: msg('solve.systems.there_are_no_equations_with_unknowns') });
    const rows = linearRows(rels, vars);
    if (rows.some((r) => !r)) {
        const pair = rels.length === 2 && vars.length === 2 && rows.some(Boolean);
        return done({
            kind: 'unsupported',
            reason: pair
                ? msg('solve.systems.one_of_equations_is_not_linear')
                : msg('solve.systems.not_all_equations_are_linear_and'),
        });
    }
    const m = rows.length;
    const n = vars.length;
    let method = opts.method ?? (m === 2 && n === 2 ? (rows.some((r) => r.a.some((q) => q.abs().isOne())) ? 'substitution' : 'addition') : 'gauss');
    if ((method === 'substitution' || method === 'addition') && !(m === 2 && n === 2)) method = 'gauss';
    if (method === 'cramer' && (m !== n || n > 3)) method = 'gauss';
    const steps = [];
    const standard = rels.every((r) => r.rhs.type === 'num' && nodeKey(simpOr(r.lhs)) === nodeKey(simpOr(linEqNode(linearRows([r], vars)[0].a, Q.ZERO, vars).lhs)));
    if (!standard) steps.push(S(msg('solve.systems.bring_each_equation_to_form_unknowns'), { tex: systemTexB(rows, vars) }));
    let res = null;
    if (method === 'substitution') res = sysSubstitution(rows, vars);
    else if (method === 'addition') res = sysAddition(rows, vars);
    else if (method === 'cramer') {
        const cr = matSolveCramer(Matrix.from(rows.map((r) => r.a)), rows.map((r) => r.b), { steps: true, vars });
        if (cr.kind === 'unique') res = { kind: 'unique', steps: cr.steps.filter((s) => s.rule !== 'answer').concat(cr.steps.filter((s) => s.rule === 'answer').map((s) => ({ ...s, title: msg('solve.systems.find_unknowns') }))), solution: Object.fromEntries(vars.map((x, j) => [x, num(cr.x[j])])) };
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
                tex: eachLanguage((l) => out.solutions.map((s) => tupleTex(vars.map((x) => tex(s[x], l)), l)).join(notation(l).listWideTex)),
                text: eachLanguage((l) => out.solutions.map((s) => `(${vars.map((x) => toText(s[x], { lang: l })).join(notation(l).listText)})`).join(notation(l).listText)),
            };
        } else if (out.kind === 'none') out.answer = { tex: msg('solve.systems.no_solutions'), text: msg('solve.systems.no_solutions_2') };
        else out.answer = { tex: '', text: out.reason };
        out.steps.push(out.kind === 'unsupported' ? S(msg('solve.systems.could_not_solve_2'), { text: out.reason, final: true }) : S(msg('solve.systems.answer'), { tex: out.answer.tex, final: true }));
        if (!withSteps) out.steps = [];
        return out;
    };
    if (rels.length !== 2 || vars.length !== 2) return done({ kind: 'unsupported', reason: msg('solve.systems.two_equations_in_two_unknowns_are') });
    const rows = linearRows(rels, vars);
    if (rows.every(Boolean)) {
        const r = solveLinearSystem(rels, vars, opts);
        if (r.kind === 'unique') return done({ kind: 'solutions', solutions: [r.solution], steps: r.steps.slice(0, -1), check: r.check });
        if (r.kind === 'none') return done({ kind: 'none', steps: r.steps.slice(0, -1) });
        return done({ kind: 'unsupported', reason: msg('solve.systems.infinitely_many_solutions_see_linear_system'), steps: r.steps.slice(0, -1) });
    }
    const li = rows.findIndex(Boolean);
    if (li < 0) return done({ kind: 'unsupported', reason: msg('solve.systems.neither_equation_is_linear_so_substitution') });
    const other = rels[1 - li];
    const row = rows[li];
    let j = row.a.findIndex((q) => q.abs().isOne());
    if (j < 0) j = row.a.findIndex((q) => !q.isZero());
    if (j < 0) return done({ kind: 'unsupported', reason: msg('solve.systems.linear_equation_has_no_unknowns') });
    const k = 1 - j;
    const [vj, vk] = [vars[j], vars[k]];
    const expr = simpOr(div(add(num(row.b), mul(num(row.a[k].neg()), sym(vk))), num(row.a[j])));
    const steps = [S(msg('solve.systems.express_from_linear_equation', { vj }), { tex: eachLanguage((l) => `${vj} = ${tex(expr, l)}`) })];
    const subst = rel('=', substitute(other.lhs, { [vj]: expr }), substitute(other.rhs, { [vj]: expr }));
    steps.push(S(msg('solve.systems.substitute_into_other_equation'), { tex: eachLanguage((l) => tex(subst, l)), text: msg('solve.systems.one_unknown_is_left', { vk }) }));
    const r = solveEquation(subst, vk, { steps: true });
    steps.push(S(eachLanguage((l) => (msg('solve.systems.solve_for', { vk }).in(l))), { tex: r.answer.tex, sub: r.steps.slice(0, -1) }));
    if (r.kind === 'none') return done({ kind: 'none', steps });
    if (r.kind !== 'roots' || r.families || r.roots.some((x) => x.approxOnly)) {
        return done({ kind: 'unsupported', steps, reason: r.reason ?? msg('solve.systems.could_not_find_exact_roots_of') });
    }
    const solutions = r.roots.map((x) => ({ [vk]: x.node, [vj]: simpOr(substitute(expr, { [vk]: x.node })) }))
        .sort((a, b) => approxOf(a[vars[0]]) - approxOf(b[vars[0]]) || approxOf(a[vars[1]]) - approxOf(b[vars[1]]));
    steps.push(S(msg('solve.systems.find_for_each_root', { vj }), {
        tex: eachLanguage((l) => solutions.map((s) => `${vk} = ${tex(s[vk], l)}:\\ ${vj} = ${tex(s[vj], l)}`).join(notation(l).listWideTex)),
    }));
    const check = [];
    const good = [];
    for (const s of solutions) {
        const ch = checkSystem(rels, s);
        check.push({ solution: s, ok: ch.ok, items: ch.items });
        if (ch.ok) good.push(s);
        steps.push(S(eachLanguage((l) => (msg('solve.systems.check_2').in(l)) + `$${tupleTex(vars.map((x) => tex(s[x], l)), l)}$`), { tex: ch.step.tex, text: ch.step.text }));
    }
    return done({ kind: good.length ? 'solutions' : 'none', solutions: good, steps, check });
}