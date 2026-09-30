// calculus/limit/limit — the public API limit(): one-sided limits, the domain side, the steps and the check.

import { niceForm } from '../derivative/index.js';
import { nodeChildren, neg, num, add, mul, div, pow, fn, substitute, freeVars, mapNode, containsVar } from '../../core/ast.js';
import { evaluate } from '../../core/evaluate.js';
import { MathError } from '../../core/rational.js';
import { step } from '../../core/steps.js';
import { DNE, Split, atPoint, evalAt, fin, infV, isOneV, isZeroV, limTex, lt, makePoint, sideSignStrict } from './common.js';
import { ev, limitContext } from './evaluator.js';
import { FORM_NAME, FORM_TEX, plainNum, quotientParts } from './forms.js';
import { crossCheck, fmtNum, numericEstimate, tableFor, tableStep } from './table.js';
import { msg, eachLanguage } from '../../i18n/index.js';
import { asNode } from '../../core/parse.js';
import { simp, trySimp, calcTex } from '../display.js';

// ---------------------------------------------------------------- public API

function valueOut(L) {
    if (!L) return null;
    if (L.k === 'fin') return niceForm(L.node);
    if (L.k === 'inf') return L.s > 0 ? 'inf' : '-inf';
    if (L.k === 'dne' || L.k === 'bnd') return 'dne';
    return null;
}

function valueTex(val, L) {
    if (val === 'inf') return '+\\infty';
    if (val === '-inf') return '-\\infty';
    if (val === 'dne') return msg('calculus.limit.limit.does_not_exist').in(L);
    if (val && typeof val === 'object') return calcTex(val, L);
    return '?';
}

/** Is f defined at x = a (no 0⁰, no division by zero, no ln 0 …)? */
function definedAt(f, v, x) {
    let ok = true;
    const walk = (n) => {
        if (!ok) return;
        if (n.type === 'pow') {
            const b = evalAt(n.base, v, x);
            const e = evalAt(n.exp, v, x);
            if (b === 0 && !(e > 0)) ok = false;
        }
        if (n.type === 'fn' && (n.name === 'tan' || n.name === 'sec') && Math.abs(Math.cos(evalAt(n.args[0], v, x))) < 1e-12) ok = false;
        if (n.type === 'fn' && (n.name === 'cot' || n.name === 'csc') && Math.abs(Math.sin(evalAt(n.args[0], v, x))) < 1e-12) ok = false;
        nodeChildren(n).forEach(walk);
    };
    walk(f);
    return ok && Number.isFinite(evalAt(f, v, x));
}

/** |u| and sgn u with u → 0 at the point: replace by ±u and ±1 using the sign of u on the side. */
function unfoldAbs(f, v, P) {
    if (!Number.isFinite(P.x)) return f;
    let changed = false;
    const g = mapNodeDeep(f, (m) => {
        if (m.type !== 'fn' || (m.name !== 'abs' && m.name !== 'sign')) return undefined;
        const u = m.args[0];
        const u0 = evalAt(u, v, P.x);
        if (!(Math.abs(u0) < 1e-12)) return undefined;
        const s = sideSignStrict(u, v, P);
        if (!s || Number.isNaN(s)) return undefined;
        changed = true;
        return m.name === 'abs' ? (s > 0 ? u : neg(u)) : num(s);
    });
    return changed ? (trySimp(g) ?? f) : f;
}

function mapNodeDeep(n, fnc) {
    const r = fnc(n);
    if (r !== undefined) return r;
    const kids = nodeChildren(n);
    if (!kids.length) return n;
    const nk = kids.map((c) => mapNodeDeep(c, fnc));
    if (nk.every((c, i) => c === kids[i])) return n;
    return rebuild(n, nk);
}

function rebuild(n, kids) {
    switch (n.type) {
        case 'add':
            return add(kids);
        case 'mul':
            return mul(kids);
        case 'div':
            return div(kids[0], kids[1]);
        case 'neg':
            return neg(kids[0]);
        case 'pow':
            return pow(kids[0], kids[1]);
        case 'fn':
            return fn(n.name, ...kids);
        default:
            return n;
    }
}

function oneSide(f0, v, P, opts) {
    void opts;
    const C = limitContext(v, P);
    let f = f0;
    // direct substitution (continuity)
    if (P.a && definedAt(f0, v, P.x)) {
        let val = null;
        try {
            const s = simp(substitute(f, { [v]: P.a }));
            const x = evaluate(s);
            if (Number.isFinite(x) && !freeVars(s).length) {
                // continuity check: the values next to the point must approach f(a)
                const sides = P.side === 'both' ? ['left', 'right'] : [P.side];
                const ok = sides.every((side) => {
                    const ys = [1e-6, 1e-8].map((h) => evalAt(f, v, atPoint({ ...P, side }, h)));
                    return ys.every((y) => Number.isFinite(y) && Math.abs(y - x) < 1e-4 * Math.max(1, Math.abs(x)));
                });
                if (ok) val = fin(s);
            }
        } catch {
            val = null;
        }
        if (val) return { L: val, C, method: 'substitution' };
    }
    f = unfoldAbs(f0, v, P);
    C.root = f;
    const L = ev(f, C);
    if (L && L.k === 'inf' && L.s === 0) throw new Split();
    return { L, C, method: C.methods.size ? [...C.methods][C.methods.size - 1] : L ? 'arithmetic' : null };
}

/**
 * Limit of node as v → a. a: node, number, string ('inf', '-inf', 'pi/2', …) or ±Infinity.
 * opts: {steps, side: 'both' | 'left' | 'right'}.
 * → {value: node | 'inf' | '-inf' | 'dne' | null, method, steps, table: [{x, fx, side}], verified,
 *    approx?: number (a numeric estimate when no symbolic method worked; value is null then),
 *    sides?: {left, right} (when a two-sided limit splits), tex}.
 */
// |u| where the sign of u has settled near the point — x → ±∞ or a one-sided approach — is ±u there
function settleAbs(f, v, P) {
    if (P.side === 'both' && Number.isFinite(P.x)) return f;
    const probes = Number.isFinite(P.x)
        ? [1e-3, 1e-4, 1e-6, 1e-8].map((h) => P.x + (P.side === 'left' ? -h : h) * Math.max(1, Math.abs(P.x)))
        : [1e3, 1e4, 1e5, 1e6, 1e8].map((t) => (P.x > 0 ? t : -t));
    let changed = false;
    const g = mapNode(f, (n) => {
        if (n.type !== 'fn' || n.name !== 'abs' || !containsVar(n.args[0], v)) return undefined;
        const signs = probes.map((x) => Math.sign(evalAt(n.args[0], v, x)));
        if (!signs.every((z) => z === signs[0]) || !(signs[0] === 1 || signs[0] === -1)) return undefined;
        changed = true;
        const inner = settleAbs(n.args[0], v, P);
        return signs[0] > 0 ? inner : neg(inner);
    });
    if (!changed) return f;
    try {
        return simp(g);
    } catch {
        return g;
    }
}

export function limit(node, v = 'x', a = 0, opts = {}) {
    node = asNode(node);
    if (node.type === 'rel' || node.type === 'list' || node.type === 'chain')
        throw new MathError(msg('calculus.limit.limit.formula_is_needed'), null, null, 'not-expr');
    const others = freeVars(node).filter((w) => w !== v);
    const side = opts.side ?? 'both';
    let P = makePoint(asNode(a), side);
    let f;
    try {
        f = simp(node);
    } catch {
        f = node;
    }
    // x·ln x at 0: the function lives only on one side of the point, so the limit is taken from that side
    let domainSide = null;
    if (P.side === 'both' && Number.isFinite(P.x) && !others.length) {
        const scale = Math.max(1, Math.abs(P.x));
        const lives = (dir) => [1e-3, 1e-5, 1e-7].some((h) => !Number.isNaN(evalAt(f, v, P.x + dir * h * scale)));
        const l = lives(-1),
            r = lives(1);
        if (l !== r) {
            domainSide = r ? 'right' : 'left';
            P = { ...P, side: domainSide };
        }
    }
    if (!others.length) f = settleAbs(f, v, P);
    const wantSteps = !!opts.steps;
    const steps = [];
    const table = others.length ? [] : tableFor(f, v, P);
    const head = (L) => `${limTex(P, v, L)} ${lt(node, L)}`;
    if (wantSteps) {
        steps.push(step({ title: msg('calculus.limit.limit.what_we_look_for'), tex: eachLanguage(head), rule: 'start' }));
        if (domainSide) {
            steps.push(
                step({
                    title: msg('calculus.limit.limit.where_function_is_defined'),
                    text:
                        domainSide === 'right'
                            ? msg('calculus.limit.limit.left_of_function_is_undefined_so', { v, P: (lng) => plainNum(P, lng) })
                            : msg('calculus.limit.limit.right_of_function_is_undefined_so', { v, P: (lng) => plainNum(P, lng) }),
                    rule: 'domain-side',
                }),
            );
        }
    }
    let result;
    let sidesInfo = null;
    const run = (PP) => {
        try {
            return oneSide(f, v, PP, opts);
        } catch (e) {
            if (e instanceof Split) return { split: true };
            if (e instanceof MathError) return { L: null, C: { log: [], methods: new Set() } };
            throw e;
        }
    };
    result = run(P);
    if (result.split) {
        const l = run({ ...P, side: 'left' });
        const r = run({ ...P, side: 'right' });
        const vl = l.split ? null : l.L;
        const vr = r.split ? null : r.L;
        sidesInfo = { left: valueOut(vl), right: valueOut(vr) };
        const same = vl && vr && vl.k === vr.k && (vl.k !== 'fin' || Math.abs(vl.x - vr.x) < 1e-12) && (vl.k !== 'inf' || vl.s === vr.s);
        if (wantSteps) {
            steps.push(
                step({
                    title: msg('calculus.limit.limit.limit_from_left'),
                    tex: eachLanguage((L) => `${limTex({ ...P, side: 'left' }, v, L)} ${calcTex(node, L)} = ${valueTex(sidesInfo.left, L)}`),
                    rule: 'left',
                    sub: l.C?.log ?? [],
                }),
            );
            steps.push(
                step({
                    title: msg('calculus.limit.limit.limit_from_right'),
                    tex: eachLanguage((L) => `${limTex({ ...P, side: 'right' }, v, L)} ${calcTex(node, L)} = ${valueTex(sidesInfo.right, L)}`),
                    rule: 'right',
                    sub: r.C?.log ?? [],
                }),
            );
        }
        result = same
            ? { L: vl, C: l.C, method: l.method }
            : { L: vl && vr ? DNE : null, C: { log: [], methods: new Set() }, method: 'one-sided', splitDiffer: !!(vl && vr) };
    }
    let L = result.L;
    let method = result.method;
    let verified = false;
    let approx;
    // cross-check against the numbers
    if (L && !others.length && (L.k === 'fin' || L.k === 'inf')) {
        const sides = P.side === 'both' && Number.isFinite(P.x) ? ['left', 'right'] : [P.side];
        const checks = sides.map((s) => crossCheck(f, v, { ...P, side: s }, L));
        const usable = sides.filter((s) => numericEstimate(f, v, { ...P, side: s }) || tableFor(f, v, { ...P, side: s }).some((r) => Number.isFinite(r.fx)));
        if (checks.includes('contradict')) {
            L = null;
            method = null;
        } else verified = checks.includes('agree') || !usable.length;
    }
    if (L && (L.k === 'dne' || L.k === 'bnd') && !others.length) verified = true;
    if (!L && !others.length) {
        // numeric fallback
        const sides = P.side === 'both' && Number.isFinite(P.x) ? ['left', 'right'] : [P.side];
        const ests = sides.map((s) => numericEstimate(f, v, { ...P, side: s }));
        if (ests.every(Boolean)) {
            const [e1, e2] = ests;
            const agreeSides = !e2 || (e1.k === e2.k && (e1.k === 'inf' ? e1.s === e2.s : Math.abs(e1.x - e2.x) < 1e-3 * Math.max(1, Math.abs(e1.x))));
            if (!agreeSides) {
                L = DNE;
                method = 'numeric';
                sidesInfo = {
                    left: e1.k === 'inf' ? (e1.s > 0 ? 'inf' : '-inf') : null,
                    right: e2.k === 'inf' ? (e2.s > 0 ? 'inf' : '-inf') : null,
                    leftApprox: e1.k === 'fin' ? e1.x : undefined,
                    rightApprox: e2.k === 'fin' ? e2.x : undefined,
                };
            } else if (e1.k === 'inf') {
                L = infV(e1.s);
                method = 'numeric';
            } else {
                approx = e1.x;
                method = 'numeric';
            }
        }
    }
    const value = approx !== undefined ? null : valueOut(L);
    if (value === null && approx === undefined) method = null;
    const tex =
        approx !== undefined
            ? eachLanguage((Lg) => `${head(Lg)} \\approx ${fmtNum(approx, Lg)}`)
            : value !== null
              ? eachLanguage((Lg) => `${head(Lg)} = ${valueTex(value, Lg)}`)
              : null;
    if (wantSteps) {
        if (method === 'substitution') {
            steps.push(
                step({
                    title: msg('calculus.limit.limit.substitute'),
                    tex: eachLanguage((Lg) => `${head(Lg)} = ${valueTex(value, Lg)}`),
                    text: msg('calculus.limit.limit.function_is_defined_and_continuous_at', { v, P: (lng) => plainNum(P, lng) }),
                    rule: 'substitution',
                }),
            );
        } else if (result.C && result.C.log && !result.split) {
            const form = firstForm(f, v, P);
            if (form) {
                steps.push(
                    step({
                        title: msg('calculus.limit.limit.identify_indeterminate_form'),
                        tex: eachLanguage((Lg) => `${head(Lg)} = \\left[${FORM_TEX[form]}\\right]`),
                        text: msg('calculus.limit.limit.substitution_gives_indeterminate_form_expression_has', { p: FORM_NAME[form] }),
                        rule: 'form',
                    }),
                );
            }
            steps.push(...result.C.log);
        }
        if (result.splitDiffer || (L && L.k === 'dne')) {
            steps.push(
                step({
                    title: msg('calculus.limit.limit.no_limit'),
                    text: sidesInfo
                        ? msg('calculus.limit.limit.limits_from_left_and_from_right')
                        : msg('calculus.limit.limit.function_oscillates_and_approaches_no_number'),
                    rule: 'dne',
                }),
            );
        }
        if (table.length) steps.push(tableStep(table, v, P, f));
        if (approx !== undefined) {
            steps.push(
                step({
                    title: msg('calculus.limit.limit.numeric_estimate'),
                    text: msg('calculus.limit.limit.exact_methods_did_not_work_judging'),
                    rule: 'numeric',
                }),
            );
        }
        if (tex) {
            const s = step({
                title: approx !== undefined ? msg('calculus.limit.limit.answer_approximate') : msg('calculus.limit.limit.answer'),
                tex,
                rule: 'answer',
            });
            s.final = true;
            steps.push(s);
        } else {
            steps.push(step({ title: msg('calculus.limit.limit.not_found'), text: msg('calculus.limit.limit.this_limit_could_not_be_found'), rule: 'fail' }));
        }
    }
    const out = { value, method, steps, table, verified, tex };
    if (approx !== undefined) out.approx = approx;
    if (sidesInfo) out.sides = sidesInfo;
    if (domainSide) out.domainSide = domainSide;
    return out;
}

function firstForm(f, v, P) {
    // the form of the top-level expression after naive substitution (for the explanation)
    const C = limitContext(v, P, { depth: 99 });
    const S = trySimp(f) ?? f;
    try {
        if (S.type === 'add') {
            const vals = S.args.map((t) => ev(t, C));
            if (vals.some((x) => x && x.k === 'inf' && x.s > 0) && vals.some((x) => x && x.k === 'inf' && x.s < 0)) return 'inf-inf';
        }
        if (S.type === 'pow' && containsVar(S.exp, v) && containsVar(S.base, v)) {
            const B = ev(S.base, C);
            const Ex = ev(S.exp, C);
            if (isOneV(B) && Ex && Ex.k === 'inf') return '1^inf';
            if (isZeroV(B) && isZeroV(Ex)) return '0^0';
            if (B && B.k === 'inf' && isZeroV(Ex)) return 'inf^0';
        }
        const q = quotientParts(S, v);
        if (q) {
            const U = ev(q.u, C);
            const W = ev(q.w, C);
            if (isZeroV(U) && isZeroV(W)) return '0/0';
            if (U && W && U.k === 'inf' && W.k === 'inf') return 'inf/inf';
        }
        if (S.type === 'mul') {
            const vals = S.args.map((t) => ev(t, C));
            if (vals.some(isZeroV) && vals.some((x) => x && x.k === 'inf')) return '0*inf';
        }
    } catch {
        return null;
    }
    return null;
}
