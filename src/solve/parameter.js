// param — equations with a parameter: for which values of a does the equation have two roots, one root, …
//
//   solveWithParameter("x^2 - 2a x + 4 = 0", {param: 'a', want: 'two-roots'}) → {set, steps, answer, method}
//   want: 'two-roots' | 'one-root' | 'has-roots' | 'no-roots' | a number (exactly that many roots)
//
// A quadratic in x with coefficients depending on a goes the school way: the leading coefficient is zero (the
// equation is linear), otherwise the discriminant decides. Anything linear in a goes the graphical way: a = g(x),
// study g (domain, derivative, corners, limits at the ends) and count where the line y = a meets the graph.
import { MathError } from '../core/rational.js';
import { num, sym, add, mul, div, neg, pow, rel, containsVar, substitute, numValue, nodeSome, freeVars } from '../core/ast.js';
import { parse } from '../core/parse.js';
import { toTex } from '../core/print.js';
import { L, step } from '../core/steps.js';
import { limit } from '../calculus/limit/index.js';
import { solveEquation, solveInequality, IntervalSet, intervalTex, domainSet } from './index.js';
import { trySimplify, approx } from '../core/safe.js';
import { derivativeOf } from '../calculus/derivative/derivative.js';
import { msg, eachLanguage } from '../i18n/index.js';

const N0 = num(0);
const tex = (n, l = 'ru') => toTex(n, { lang: l });
const exactRoots = (r) => r && (r.kind === 'none' || (r.kind === 'roots' && !r.families?.length && !r.roots.some((z) => z.approxOnly)));
const rootNodes = (r) => (r.kind === 'none' ? [] : r.roots.map((z) => z.node));

// what is asked, as a count of roots and the phrase (solve.parameter.want.*)
const WANT = {
    'two-roots': { n: 2, phrase: msg('solve.parameter.want.two_roots') },
    'one-root': { n: 1, phrase: msg('solve.parameter.want.one_root') },
    'no-roots': { n: 0, phrase: msg('solve.parameter.want.no_roots') },
    'has-roots': { min: 1, phrase: msg('solve.parameter.want.has_roots') },
};
function wantOf(w) {
    if (typeof w === 'number') return { n: w, phrase: msg('solve.parameter.want.exactly', { n: w }) };
    return WANT[w] ?? WANT['has-roots'];
}
const fits = (want, count) => (want.min !== undefined ? count >= want.min : count === want.n);

/* ------------------------------------------------------------------ the quadratic way */

function quadratic(E, x, a, want) {
    if (nodeSome(E, (n) => (n.type === 'fn' && containsVar(n, x)) || (n.type === 'div' && containsVar(n.den, x)) || (n.type === 'pow' && containsVar(n.base, x) && !numValue(n.exp)?.isInt()))) return null;
    const A = trySimplify(div(derivativeOf(derivativeOf(E, x), x), num(2)));
    if (containsVar(A, x)) return null;
    const B = trySimplify(substitute(derivativeOf(E, x), { [x]: N0 }));
    const C = trySimplify(substitute(E, { [x]: N0 }));
    const X = sym(x);
    // E = Ax² + Bx + C identically
    const back = add(mul(A, pow(X, num(2))), mul(B, X), C);
    for (const [xv, av] of [[0.37, 1.3], [-1.2, 0.4], [2.1, -0.7]]) {
        if (Math.abs(approx(E, { [x]: xv, [a]: av }) - approx(back, { [x]: xv, [a]: av })) > 1e-9) return null;
    }
    if (!containsVar(A, a) && approx(A) === 0) return null; // not a quadratic
    if (!containsVar(A, a) && !containsVar(B, a) && !containsVar(C, a)) return null;
    const steps = [];
    const count = new Map(); // key → {set, n}
    const addPiece = (set, n) => {
        const k = String(n);
        count.set(k, { set: (count.get(k)?.set ?? IntervalSet.empty()).union(set), n });
    };
    let zeroA = [];
    if (containsVar(A, a)) {
        const r = solveEquation(rel('=', A, N0), a, { steps: true });
        if (!exactRoots(r)) return null;
        zeroA = rootNodes(r);
        const lines = [];
        for (const a0 of zeroA) {
            const b0 = trySimplify(substitute(B, { [a]: a0 }));
            const c0 = trySimplify(substitute(C, { [a]: a0 }));
            const bz = Math.abs(approx(b0)) < 1e-12;
            const cz = Math.abs(approx(c0)) < 1e-12;
            const n = !bz ? 1 : cz ? Infinity : 0;
            addPiece(IntervalSet.point(a0), n);
            const lin = rel('=', add(mul(b0, X), c0), N0);
            lines.push(msg('solve.parameter.formula', { a, a0: (lng) => tex(a0, lng), p: (lng) => tex(trySimplify(lin.lhs), lng), p2: (lng) => n === 1 ? msg('solve.parameter.one_root').in(lng) : n === 0 ? msg('solve.parameter.no_roots').in(lng) : msg('solve.parameter.every').in(lng) }));
        }
        steps.push(step({
            title: msg('solve.parameter.leading_coefficient_is_zero'),
            tex: eachLanguage((l) => (A.type === 'sym' ? `${a} = ${zeroA.map((z) => tex(z, l)).join(',\\ ')}` : `${tex(A, l)} = 0 \\;\\Rightarrow\\; ${a} = ${zeroA.map((z) => tex(z, l)).join(',\\ ')}`)),
            text: msg('solve.parameter.then_equation_is_linear', { p: (lng) => lines.map((z) => z[lng]).join('; ') }),
        }));
    }
    const notZero = IntervalSet.all().minus(IntervalSet.points(zeroA));
    const D = trySimplify(add(mul(B, B), neg(mul(num(4), A, C))));
    steps.push(step({
        title: zeroA.length ? msg('solve.parameter.for_quadratic_equation', { A: (lng) => tex(A, lng) }) : msg('solve.parameter.quadratic_equation'),
        tex: eachLanguage((l) => `D = b^2 - 4ac = ${tex(D, l)}`),
        text: msg('solve.parameter.two_roots_for_one_for_none'),
    }));
    const pos = solveInequality(rel('>', D, N0), a, { steps: true });
    const zer = solveEquation(rel('=', D, N0), a, { steps: true });
    if (!pos.set || !exactRoots(zer)) return null;
    const zeroSet = IntervalSet.points(rootNodes(zer));
    addPiece(pos.set.intersect(notZero), 2);
    addPiece(zeroSet.intersect(notZero), 1);
    addPiece(IntervalSet.all().minus(pos.set).minus(zeroSet).intersect(notZero), 0);
    steps.push(step({ title: L('$D > 0$', '$D > 0$'), tex: eachLanguage((l) => `${a} \\in ${intervalTex(pos.set, l)}`), sub: pos.steps.slice(0, -1) }));
    steps.push(step({ title: L('$D = 0$', '$D = 0$'), tex: eachLanguage((l) => (zer.kind === 'none' ? '\\varnothing' : `${a} = ${rootNodes(zer).map((z) => tex(z, l)).join(',\\ ')}`)) }));
    return { count, steps, method: 'quadratic' };
}

/* ------------------------------------------------------------------ the graphical way */

function graphical(E, x, a, want) {
    const Qn = derivativeOf(E, a);
    if (containsVar(Qn, a)) return null; // not linear in a
    const P = trySimplify(substitute(E, { [a]: N0 }));
    const g = trySimplify(neg(div(P, Qn)));
    const Dom = domainSet(E, x);
    if (!Dom) return null;
    // points where Q = 0: roots for every a when P = 0 there too, otherwise never
    const qz = containsVar(Qn, x) ? solveEquation(rel('=', Qn, N0), x, { steps: false }) : { kind: 'none', roots: [] };
    if (!exactRoots(qz)) return null;
    let always = 0;
    const holes = [];
    for (const z of rootNodes(qz)) {
        if (!Dom.contains(z)) continue;
        if (Math.abs(approx(substitute(P, { [x]: z }))) < 1e-12) always += 1;
        holes.push(z);
    }
    const G = Dom.minus(IntervalSet.points(holes));
    const gDom = domainSet(g, x);
    const D = gDom ? G.intersect(gDom) : G;
    // breakpoints: critical points, corners, ends of the domain
    const g1 = derivativeOf(g, x);
    const crit = solveEquation(rel('=', g1, N0), x, { steps: false });
    if (!(exactRoots(crit) || crit.kind === 'unsupported' || crit.kind === 'all')) return null;
    const pts = [];
    const push = (n) => {
        const v = approx(n);
        if (Number.isFinite(v) && !pts.some((p) => Math.abs(p.x - v) < 1e-12)) pts.push({ node: trySimplify(n), x: v });
    };
    if (exactRoots(crit)) rootNodes(crit).filter((z) => D.contains(z)).forEach(push);
    // corners: zeros of |u| arguments
    const corners = [];
    const walk = (n) => {
        if (n.type === 'fn' && n.name === 'abs' && containsVar(n.args[0], x)) corners.push(n.args[0]);
        for (const k of Object.values(n)) {
            if (k && typeof k === 'object' && k.type) walk(k);
            if (Array.isArray(k)) k.forEach((c) => c && c.type && walk(c));
        }
    };
    walk(g);
    for (const u of corners) {
        const r = solveEquation(rel('=', u, N0), x, { steps: false });
        if (!exactRoots(r)) return null;
        rootNodes(r).filter((z) => D.contains(z)).forEach(push);
    }
    for (const p of D.parts) {
        if (p.lo) push(p.lo.node);
        if (p.hi) push(p.hi.node);
    }
    holes.forEach(push);
    pts.sort((u, v) => u.x - v.x);
    // pieces between neighbouring breakpoints that lie in the domain
    const pieces = [];
    const lim = (b, side) => {
        let r;
        try {
            r = limit(g, x, b, { side });
        } catch {
            r = null;
        }
        if (!r) return null;
        if (r.value === 'inf') return { inf: 1 };
        if (r.value === '-inf') return { inf: -1 };
        if (r.value && typeof r.value === 'object') return { node: trySimplify(r.value), x: approx(r.value) };
        return null;
    };
    for (let i = 0; i <= pts.length; i++) {
        const lo = i > 0 ? pts[i - 1] : null;
        const hi = i < pts.length ? pts[i] : null;
        const xs = (lo && hi ? [1, 2, 3, 4, 5, 6, 7].map((j) => lo.x + ((hi.x - lo.x) * j) / 8) : hi ? [0.5, 1, 2, 5, 20, 100].map((t) => hi.x - t) : lo ? [0.5, 1, 2, 5, 20, 100].map((t) => lo.x + t) : [-50, -5, -1, 0.3, 1, 5, 50]).sort((u, v) => u - v);
        const inside = xs.map((t) => D.contains(t));
        if (inside.every((z) => !z)) continue;
        if (!inside.every(Boolean)) return null;
        const ys = xs.map((t) => approx(g, { [x]: t }));
        if (!ys.every(Number.isFinite)) return null;
        const diffs = ys.slice(1).map((y, j) => y - ys[j]);
        const up = diffs.every((z) => z > 0);
        const down = diffs.every((z) => z < 0);
        if (!up && !down) {
            if (diffs.every((z) => Math.abs(z) < 1e-12)) return null; // constant piece: every a of that value
            return null;
        }
        const left = lo ? lim(lo.node, 'right') : lim(mul(num(-1), sym('inf')), 'both');
        const right = hi ? lim(hi.node, 'left') : lim(sym('inf'), 'both');
        if (!left || !right) return null;
        pieces.push({ lo, hi, left, right, up });
    }
    // the value at a breakpoint inside the domain
    const pointVals = pts.filter((p) => D.contains(p.node)).map((p) => ({ ...p, y: trySimplify(substitute(g, { [x]: p.node })) }));
    // levels where the count may change
    const levels = [];
    const addLevel = (n) => {
        const v = approx(n);
        if (Number.isFinite(v) && !levels.some((z) => Math.abs(z.x - v) < 1e-12)) levels.push({ node: n, x: v });
    };
    for (const p of pieces) {
        if (p.left.node) addLevel(p.left.node);
        if (p.right.node) addLevel(p.right.node);
    }
    pointVals.forEach((p) => addLevel(p.y));
    levels.sort((u, v) => u.x - v.x);
    const inOpen = (p, y) => {
        const lv = p.left.inf ? p.left.inf * Infinity : p.left.x;
        const rv = p.right.inf ? p.right.inf * Infinity : p.right.x;
        const lo = Math.min(lv, rv);
        const hi = Math.max(lv, rv);
        return y > lo + 1e-12 && y < hi - 1e-12;
    };
    const countAt = (y) => always + pieces.filter((p) => inOpen(p, y)).length + pointVals.filter((p) => Math.abs(approx(p.y) - y) < 1e-12).length;
    const count = new Map();
    const addPiece = (set, n) => {
        const k = String(n);
        count.set(k, { set: (count.get(k)?.set ?? IntervalSet.empty()).union(set), n });
    };
    for (let i = 0; i <= levels.length; i++) {
        const lo = i > 0 ? levels[i - 1] : null;
        const hi = i < levels.length ? levels[i] : null;
        const y = lo && hi ? (lo.x + hi.x) / 2 : hi ? hi.x - 1 - Math.abs(hi.x) : lo ? lo.x + 1 + Math.abs(lo.x) : 0;
        addPiece(IntervalSet.interval(lo ? lo.node : null, hi ? hi.node : null, false, false), countAt(y));
        if (hi) addPiece(IntervalSet.point(hi.node), countAt(hi.x));
    }
    // steps
    const steps = [];
    steps.push(step({
        title: msg('solve.parameter.express_parameter'),
        tex: eachLanguage((l) => `${a} = ${tex(g, l)}`),
        text: msg('solve.parameter.number_of_roots_is_number_of', { a, x }),
    }));
    if (holes.length) steps.push(step({ title: msg('solve.parameter.excluded_points'), tex: eachLanguage((l) => `${x} \\ne ${holes.map((h) => tex(h, l)).join(',\\ ')}`), text: always ? msg('solve.parameter.here_equation_holds_for_every') : msg('solve.parameter.dividing_by_zero_would_happen_here') }));
    const endTex = (e, l) => (e.inf ? (e.inf > 0 ? '+\\infty' : '-\\infty') : tex(e.node, l));
    steps.push(step({
        title: msg('solve.parameter.study', { x }),
        tex: eachLanguage((l) => pieces.map((p) => `${intervalTex(IntervalSet.interval(p.lo ? p.lo.node : null, p.hi ? p.hi.node : null), l)}\\!:\\ ${p.up ? '\\nearrow' : '\\searrow'}\\ ${endTex(p.left, l)} \\to ${endTex(p.right, l)}`).join(';\\quad ')),
        text: msg('solve.parameter.derivative_is_g_is_monotone_on', { x, g1: (lng) => tex(g1, lng), p: (lng) => pointVals.length ? msg('solve.parameter.values_at_points', { p: (lng) => pointVals.map((p) => `$g(${tex(p.node, lng)}) = ${tex(p.y, lng)}$`).join(', ') }).in(lng) : '' }),
    }));
    return { count, steps, method: 'graphical' };
}

/* ------------------------------------------------------------------ entry */

/** For which values of the parameter does the equation have the wanted number of roots? */
export function solveWithParameter(input, opts = {}) {
    const obj = typeof input === 'object' && input !== null && !input.type ? input : null;
    const text = obj ? obj.task : input;
    const a = opts.param ?? obj?.param ?? 'a';
    const x = opts.v ?? obj?.v ?? 'x';
    const want = wantOf(opts.want ?? obj?.want ?? 'has-roots');
    let node;
    try {
        node = typeof text === 'string' ? parse(text) : text;
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        return { kind: 'unsupported', reason: e.msg, steps: [] };
    }
    if (node.type !== 'rel' || node.op !== '=') return { kind: 'unsupported', reason: msg('solve.parameter.equation_is_needed'), steps: [] };
    const others = freeVars(node).filter((v) => v !== a && v !== x);
    if (others.length) return { kind: 'unsupported', reason: msg('solve.parameter.extra_letters', { p: others.join(', ') }), steps: [] };
    const E = trySimplify(add(node.lhs, neg(node.rhs)));
    let r;
    try {
        r = quadratic(E, x, a, want) ?? graphical(E, x, a, want);
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        r = null;
    }
    if (!r) return { kind: 'unsupported', reason: msg('solve.parameter.this_parameter_problem_is_not_supported'), steps: [] };
    let set = IntervalSet.empty();
    for (const { set: s, n } of r.count.values()) if (fits(want, n)) set = set.union(s);
    const summary = [...r.count.values()].filter((z) => !z.set.isEmpty()).sort((u, v) => u.n - v.n);
    const steps = [
        step({ title: msg('solve.parameter.problem'), tex: eachLanguage((l) => tex(node, l)), text: msg('solve.parameter.for_which_does_equation_have', { a, want: want.phrase }) }),
        ...r.steps,
        step({
            title: msg('solve.parameter.number_of_roots_against_parameter'),
            tex: eachLanguage((l) => summary.map((z) => `${a} \\in ${intervalTex(z.set, l)}\\!:\\ ${z.n === Infinity ? '\\infty' : z.n}`).join(';\\quad ')),
        }),
    ];
    const answerTex = eachLanguage((l) => `${a} \\in ${intervalTex(set, l)}`);
    steps.push(step({ title: msg('solve.parameter.answer'), tex: answerTex }));
    steps[steps.length - 1].final = true;
    return { kind: 'set', set, method: r.method, steps, answer: { tex: answerTex, text: eachLanguage((l) => set.toText(l)) }, text: set.toText('en') };
}
