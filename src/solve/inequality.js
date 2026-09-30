// solve/inequality — inequalities: linear, quadratic, rational, with moduli, radicals, exponents, logarithms;
// the generalised method of intervals as the last resort.

import { bigLcm, Q, MathError } from '../core/rational.js';
import { nodeKey, num, add, neg, containsVar, rel, nodeSome, numValue, div, pow, sym, mapNode, mul, freeVars, summands } from '../core/ast.js';
import { Poly, linearForm } from '../core/poly.js';
import { simplify, splitCoeff } from '../core/simplify.js';
import { collectTerms } from '../core/expand.js';
import { parse } from '../core/parse.js';
import {
    N0,
    N1,
    TMP,
    approxOf,
    exactZero,
    isConstNode,
    linearIn,
    orTex,
    outermost,
    qGcd,
    replaceNode,
    simpOr,
    tex,
    relHoldsNum,
    isZeroNode,
    monoNode,
    sumNode,
} from './common.js';
import { OP_OF, collectConds, condTex, odzInfo } from './domain.js';
import { pickVar, solveCore, solveEquation } from './equation.js';
import { analyzeExp, baseInfo, baseNode, exactPower, logNode, logNodeB, sameBase } from './exponential.js';
import { IntervalSet, cmpEnd, endOf, intervalTex, intervalText, relToSet } from './intervals.js';
import { analyzeLog } from './logarithmic.js';
import { polyTex, quadSolve, solveAnyPoly } from './polynomial.js';
import { hasRadical, splitRadicalTerm } from './radical.js';
import { factoredNode } from './rational.js';
import { mergeRoots, rootsTex } from './roots.js';
import { chartOf, chartOut, ratParts, realRootsMult, setFromChart, signSet } from './signs.js';
import { casesTex } from './systems.js';
import { msg, notation, eachLanguage } from '../i18n/index.js';
import { step } from '../core/steps.js';

// ---------------------------------------------------------------- inequalities

const OP_TEX = { '<': '<', '<=': '\\le', '>': '>', '>=': '\\ge', '!=': '\\ne', '=': '=' };
const OP_FLIP = { '<': '>', '<=': '>=', '>': '<', '>=': '<=', '!=': '!=', '=': '=' };
const strictOf = (op) => op === '<' || op === '>';

function ineqTexB(l, op, r) {
    return eachLanguage((lang) => `${typeof l === 'string' ? l : tex(l, lang)} ${OP_TEX[op]} ${typeof r === 'string' ? r : tex(r, lang)}`);
}

const pointsListTex = (pts, v, l) =>
    pts
        .map((p) => `${v} = ${tex(p.node, l)}${p.mult > 1 || p.mN > 1 ? `\\ (${msg('solve.inequality.multiplicity').in(l)}${p.mult ?? p.mN})` : ''}`)
        .join(';\\ ');

function signsTex(chart, l) {
    const pts = chart.points;
    const iv = (k) => {
        const a = k ? tex(pts[k - 1].node, l) : '-\\infty';
        const b = k < pts.length ? tex(pts[k].node, l) : '+\\infty';
        return `(${a}${notation(l).intervalTex}${b})`;
    };
    return chart.signs.map((s, k) => `${iv(k)}\\!:\\ ${s > 0 ? '+' : s < 0 ? '-' : '0'}`).join(';\\quad ');
}

/** Method of intervals for N/L op 0 with steps. */
function intervalMethod(N, L, op, ctx, pre = []) {
    const v = ctx.v;
    const steps = [...pre];
    const hasL = L && L.degree >= 1;
    const chart = chartOf(N, hasL ? L : null, v);
    const zeros = chart.points.filter((p) => p.mN > 0);
    const poles = chart.points.filter((p) => p.mL > 0);
    steps.push(
        step({
            title: msg('solve.inequality.mark_zeros_of_numerator_on_number'),
            tex: eachLanguage((l) =>
                zeros.length
                    ? pointsListTex(
                          zeros.map((p) => ({ ...p, mult: p.mN })),
                          v,
                          l,
                      )
                    : '\\varnothing',
            ),
            text: strictOf(op) ? msg('solve.inequality.inequality_is_strict_so_these_points') : msg('solve.inequality.inequality_is_not_strict_so_these'),
        }),
    );
    if (poles.length) {
        steps.push(
            step({
                title: msg('solve.inequality.mark_zeros_of_denominator_they_are'),
                tex: eachLanguage((l) =>
                    pointsListTex(
                        poles.map((p) => ({ ...p, mult: p.mL })),
                        v,
                        l,
                    ),
                ),
                text: msg('solve.inequality.division_by_zero_is_not_allowed'),
            }),
        );
    }
    const set = setFromChart(chart, op);
    const even = chart.points.filter((p) => (p.mN + p.mL) % 2 === 0);
    steps.push(
        step({
            title: msg('solve.inequality.put_signs_on_intervals'),
            tex: eachLanguage((l) => signsTex(chart, l)),
            text: even.length
                ? msg('solve.inequality.check_sign_by_substituting_point_from', { p: (lng) => even.map((p) => `$${tex(p.node, lng)}$`).join(', ') })
                : msg('solve.inequality.check_sign_by_substituting_point_from_2'),
        }),
    );
    const want = op === '>' || op === '>=' ? '+' : '−';
    steps.push(
        step({
            title: msg('solve.inequality.take_intervals_with', { p: want }),
            tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`),
            text:
                !strictOf(op) &&
                zeros.some(
                    (p) =>
                        set.contains(p.node) &&
                        !set.parts.some(
                            (q) =>
                                q.lo &&
                                q.hi &&
                                cmpEnd(q.lo, q.hi) !== 0 &&
                                ((q.lo && cmpEnd(q.lo, endOf(p.node)) === 0) || (q.hi && cmpEnd(q.hi, endOf(p.node)) === 0)),
                        ),
                )
                    ? msg('solve.inequality.zeros_of_numerator_are_added_since')
                    : undefined,
        }),
    );
    return { set, steps, chart: chartOut(chart), approx: chart.points.some((p) => p.approxOnly) };
}

function linearIneq(lhs, op, rhs, A, B, ctx) {
    const v = ctx.v;
    const steps = [];
    let den = 1n;
    for (const q of [...A.c, ...B.c]) den = bigLcm(den, q.d);
    let A1 = A;
    let B1 = B;
    const eqT = (P1, P2, o) => eachLanguage((l) => `${polyTex(P1, v, l)} ${OP_TEX[o]} ${polyTex(P2, v, l)}`);
    if (den > 1n) {
        A1 = A.scale(new Q(den));
        B1 = B.scale(new Q(den));
        steps.push(
            step({
                title: msg('solve.inequality.multiply_both_sides_by', { den }),
                tex: eqT(A1, B1, op),
                text: msg('solve.inequality.number_is_positive_so_sign_stays'),
            }),
        );
    } else if (nodeKey(simpOr(lhs)) !== nodeKey(A.toNode(v)) || nodeKey(simpOr(rhs)) !== nodeKey(B.toNode(v))) {
        steps.push(step({ title: msg('solve.inequality.expand_brackets_and_collect_like_terms'), tex: eqT(A1, B1, op) }));
    }
    const a = A1.coeff(1).sub(B1.coeff(1));
    const b = B1.coeff(0).sub(A1.coeff(0));
    steps.push(step({ title: msg('solve.inequality.move_terms_to_left_and_numbers', { v }), tex: ineqTexB(monoNode(a, v), op, num(b)) }));
    if (a.isZero()) {
        const ok = relHoldsNum(op, 0, b.toNumber());
        steps.push(
            step({
                title: ok ? msg('solve.inequality.true_numeric_inequality') : msg('solve.inequality.false_numeric_inequality'),
                tex: ineqTexB('0', op, num(b)),
                text: ok ? msg('solve.inequality.every_number_fits') : msg('solve.inequality.no_solutions'),
            }),
        );
        return { set: ok ? IntervalSet.all() : IntervalSet.empty(), steps, type: 'linear' };
    }
    const r = b.div(a);
    const op2 = a.isNeg() ? OP_FLIP[op] : op;
    if (!a.isOne()) {
        steps.push(
            step({
                title: a.isNeg()
                    ? msg('solve.inequality.divide_by_negative_number_so_sign', { p: (lng) => tex(num(a), lng) })
                    : msg('solve.inequality.divide_by_sign_stays', { p: (lng) => tex(num(a), lng) }),
                tex: ineqTexB(v, op2, num(r)),
            }),
        );
    }
    const set = relToSet(op2, endOf(num(r)));
    const chart = chartOf(new Poly([r.neg(), Q.ONE]).scale(a.isNeg() ? Q.MINUS_ONE : Q.ONE), null, v);
    setFromChart(chart, op);
    return { set, steps, chart: chartOut(chart), type: 'linear' };
}

function quadIneq(P0, op0, ctx, pre) {
    const v = ctx.v;
    const steps = [...pre];
    let P = P0;
    let op = op0;
    if (P.lead.isNeg()) {
        P = P.neg();
        op = OP_FLIP[op];
        steps.push(
            step({
                title: msg('solve.inequality.multiply_by_and_flip_sign'),
                tex: eachLanguage((l) => `${polyTex(P, v, l)} ${OP_TEX[op]} 0`),
                text: msg('solve.inequality.now_leading_coefficient_is_positive'),
            }),
        );
    }
    const q = quadSolve(P, ctx);
    const roots = q.roots;
    steps.push(
        step({
            title: eachLanguage((l) => msg('solve.inequality.roots_of_trinomial_solve', { P: polyTex(P, v, l) }).in(l)),
            tex: eachLanguage((l) => rootsTex(roots, v, l)),
            sub: q.steps,
        }),
    );
    const chart = chartOf(P, null, v);
    const set = setFromChart(chart, op);
    const up = msg('solve.inequality.opening_upwards');
    let text;
    if (roots.length === 2) text = msg('solve.inequality.parabola_is_it_is_below_axis', { P: (lng) => polyTex(P, v, lng), p: up, v });
    else if (roots.length === 1) text = msg('solve.inequality.parabola_touches_axis_at_one_point', { P: (lng) => polyTex(P, v, lng), p: up });
    else text = msg('solve.inequality.no_roots_parabola_lies_entirely_above', { P: (lng) => polyTex(P, v, lng), p: up, v });
    steps.push(step({ title: msg('solve.inequality.look_at_parabola'), text, tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    return { set, steps, chart: chartOut(chart), type: 'quadratic' };
}

function ineqConst(E, op, steps) {
    const x = approxOf(E);
    const z = exactZero(E);
    const val = z === true ? 0 : x;
    const ok = relHoldsNum(op, val, 0);
    steps.push(
        step({
            title: ok
                ? msg('solve.inequality.variable_cancels_and_true_inequality_remains')
                : msg('solve.inequality.variable_cancels_and_false_inequality_remains'),
            tex: ineqTexB(E, op, N0),
        }),
    );
    return { set: ok ? IntervalSet.all() : IntervalSet.empty(), steps, type: 'identity' };
}

/** f op g with steps → {set, steps, chart?, type} or {set: null, reason}. */
function ineqCore(lhs, op, rhs, ctx) {
    const v = ctx.v;
    if (ctx.depth > 6) return { set: null, steps: [], reason: msg('solve.inequality.inequality_is_too_complex') };
    let E;
    try {
        E = simplify(add(lhs, neg(rhs)));
    } catch (e) {
        return { set: null, steps: [], reason: e instanceof MathError ? e.msg : msg('solve.inequality.could_not_simplify') };
    }
    if (!containsVar(E, v)) return ineqConst(E, op, []);
    const P = Poly.fromNode(rel('=', lhs, rhs), v);
    if (P && P.degree >= 1) {
        if (P.degree === 1) {
            const A = Poly.fromNode(lhs, v);
            const B = Poly.fromNode(rhs, v);
            if (A && B) return linearIneq(lhs, op, rhs, A, B, ctx);
        }
        const pre = [];
        const rhsZero = isZeroNode(simpOr(rhs));
        if (!(rhsZero && nodeKey(simpOr(lhs)) === nodeKey(P.toNode(v)))) {
            pre.push(
                step({ title: msg('solve.inequality.move_everything_to_left_and_collect'), tex: eachLanguage((l) => `${polyTex(P, v, l)} ${OP_TEX[op]} 0`) }),
            );
        }
        if (P.degree === 2) return quadIneq(P, op, ctx, pre);
        const fz = factoredNode(P, v);
        if (nodeKey(fz) !== nodeKey(P.toNode(v)))
            pre.push(step({ title: msg('solve.inequality.factor'), tex: eachLanguage((l) => `${tex(fz, l)} ${OP_TEX[op]} 0`) }));
        return { ...intervalMethod(P, null, op, ctx, pre), type: 'polynomial' };
    }
    const rp = ratParts(E, v);
    if (rp && rp.L.degree >= 1) {
        const pre = [
            step({
                title: msg('solve.inequality.move_everything_to_left_and_bring'),
                tex: eachLanguage(
                    (l) => `\\frac{${tex(rp.N.degree >= 1 ? factoredNode(rp.N, v) : rp.N.toNode(v), l)}}{${tex(factoredNode(rp.L, v), l)}} ${OP_TEX[op]} 0`,
                ),
                text: msg('solve.inequality.we_may_not_multiply_by_denominator'),
            }),
        ];
        if (rp.N.isZero()) {
            const set = (op === '>=' || op === '<=' ? IntervalSet.all() : IntervalSet.empty()).minus(
                IntervalSet.points(realRootsMult(rp.L, v).map((r) => r.node)),
            );
            return { set, steps: pre, type: 'rational' };
        }
        return { ...intervalMethod(rp.N, rp.L, op, ctx, pre), type: 'rational' };
    }
    const tries = [
        () => (nodeSome(E, (n) => n.type === 'fn' && n.name === 'abs') ? absIneq(E, op, ctx) : null),
        () => expIneq(E, op, ctx),
        () => logIneq(lhs, op, rhs, E, ctx),
        () => (hasRadical(E, v) ? radIneq(E, op, ctx) : null),
        () => nodeLinearIneq(E, op, ctx),
        () => rootsIneq(lhs, op, rhs, E, ctx),
    ];
    for (const t of tries) {
        const r = t();
        if (r) return r;
    }
    return { set: null, steps: [], reason: msg('solve.inequality.this_kind_of_inequality_is_not') };
}

/** A single even root against a constant: √f op c. */
function radIneq(E, op, ctx) {
    const v = ctx.v;
    const terms = summands(E);
    const rads = terms.filter((t) => hasRadical(t, v));
    if (rads.length !== 1) return null;
    const sp = splitRadicalTerm(rads[0], v);
    if (!sp) return null;
    const e = numValue(sp.R.exp);
    if (e.n !== 1n) return null;
    const q = e.d;
    const kv = approxOf(sp.coef);
    if (!Number.isFinite(kv) || kv === 0) return null;
    const c = simpOr(div(neg(sumNode(terms.filter((t) => t !== rads[0]))), sp.coef));
    if (containsVar(c, v)) return null;
    const op2 = kv < 0 ? OP_FLIP[op] : op;
    const f = sp.R.base;
    const cv = approxOf(c);
    const steps = [step({ title: msg('solve.inequality.isolate_root'), tex: ineqTexB(sp.R, op2, c) })];
    const sub = (l2, o2, r2) => ineqCore(l2, o2, r2, { ...ctx, depth: ctx.depth + 1 });
    const even = q % 2n === 0n;
    if (!even) {
        const cq = simpOr(pow(c, num(q)));
        steps.push(step({ title: msg('solve.inequality.raise_to_odd_power_sign_stays'), tex: ineqTexB(f, op2, cq) }));
        const r = sub(f, op2, cq);
        if (!r.set) return null;
        return { set: r.set, steps: [...steps, ...r.steps], chart: r.chart, type: 'radical' };
    }
    const dom = sub(f, '>=', N0);
    if (!dom.set) return null;
    const cz = exactZero(c) === true;
    let set;
    if (op2 === '<' || op2 === '<=') {
        if (cv < 0 || (cz && op2 === '<')) {
            steps.push(step({ title: msg('solve.inequality.root_is_never_negative'), text: msg('solve.inequality.no_solutions') }));
            return { set: IntervalSet.empty(), steps, type: 'radical' };
        }
        const cq = simpOr(pow(c, num(q)));
        steps.push(
            step({
                title: msg('solve.inequality.both_sides_are_non_negative_raise'),
                tex: eachLanguage((l) => casesTex([`${tex(f, l)} \\ge 0`, `${tex(f, l)} ${OP_TEX[op2]} ${tex(cq, l)}`])),
            }),
        );
        const r = sub(f, op2, cq);
        if (!r.set) return null;
        set = r.set.intersect(dom.set);
    } else {
        if (cv < 0 || (cz && op2 === '>=')) {
            steps.push(step({ title: msg('solve.inequality.root_is_non_negative_inequality_holds'), tex: eachLanguage((l) => `${tex(f, l)} \\ge 0`) }));
            set = dom.set;
        } else {
            const cq = simpOr(pow(c, num(q)));
            steps.push(
                step({
                    title: msg('solve.inequality.both_sides_are_non_negative_raise_2'),
                    tex: ineqTexB(f, op2, cq),
                    text: msg('solve.inequality.condition_holds_automatically_exceeds_positive_number'),
                }),
            );
            const r = sub(f, op2, cq);
            if (!r.set) return null;
            set = r.set.intersect(dom.set);
        }
    }
    steps.push(step({ title: msg('solve.inequality.result_of_this_step'), tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    return { set, steps, type: 'radical' };
}

/** a·x + b op 0 with constant (possibly irrational) node coefficients. */
function nodeLinearIneq(E, op, ctx) {
    const v = ctx.v;
    let ct;
    try {
        ct = collectTerms(E, v);
    } catch {
        return null;
    }
    if (!ct || !ct.has(1) || ![...ct.keys()].every((d) => d === 0 || d === 1)) return null;
    const a = ct.get(1);
    const b = ct.get(0) ?? N0;
    if (!isConstNode(a) || !isConstNode(b)) return null;
    const av = approxOf(a);
    if (!Number.isFinite(av) || av === 0) return null;
    const r = simpOr(div(neg(b), a));
    const op2 = av < 0 ? OP_FLIP[op] : op;
    const steps = [
        step({
            title: msg('solve.inequality.solve_for', { v }),
            tex: ineqTexB(v, op2, r),
            text: av < 0 ? msg('solve.inequality.dividing_by_negative_number_flips_sign') : undefined,
        }),
    ];
    return { set: relToSet(op2, endOf(r)), steps, type: 'linear' };
}

function absIneq(E, op, ctx) {
    const v = ctx.v;
    const A = outermost(E, (n) => n.type === 'fn' && n.name === 'abs' && containsVar(n, v));
    const steps = [];
    if (A.length === 1) {
        const f = A[0].args[0];
        const li = linearIn(replaceNode(E, A[0], sym(TMP)), TMP, v);
        if (li && !containsVar(li.beta, v)) {
            const av = approxOf(li.alpha);
            const c = simpOr(div(neg(li.beta), li.alpha));
            const op2 = av < 0 ? OP_FLIP[op] : op;
            const cv = approxOf(c);
            const cz = exactZero(c) === true;
            steps.push(step({ title: msg('solve.inequality.isolate_absolute_value'), tex: ineqTexB(A[0], op2, c) }));
            const sub = (l2, o2, r2) => ineqCore(l2, o2, r2, { ...ctx, depth: ctx.depth + 1 });
            if (op2 === '<' || op2 === '<=') {
                if (cv < 0 || (cz && op2 === '<')) {
                    steps.push(step({ title: msg('solve.inequality.absolute_value_is_never_below_negative'), text: msg('solve.inequality.no_solutions') }));
                    return { set: IntervalSet.empty(), steps, type: 'abs' };
                }
                if (cz) {
                    steps.push(step({ title: msg('solve.inequality.absolute_value_is_at_most_zero'), tex: eachLanguage((l) => `${tex(f, l)} = 0`) }));
                    const r = solveCore(f, N0, { ...ctx, depth: ctx.depth + 1 });
                    const set =
                        r.kind === 'roots' ? IntervalSet.points(r.roots.map((x) => x.node)) : r.kind === 'all' ? IntervalSet.all() : IntervalSet.empty();
                    return { set, steps: [...steps, ...r.steps], type: 'abs' };
                }
                steps.push(
                    step({
                        title: msg('solve.inequality.double_inequality'),
                        tex: eachLanguage((l) => `${tex(simpOr(neg(c)), l)} ${OP_TEX[op2]} ${tex(f, l)} ${OP_TEX[op2]} ${tex(c, l)}`),
                        text: msg('solve.inequality.distance_from_zero_is_less_than'),
                    }),
                );
                const r1 = sub(f, OP_FLIP[op2], simpOr(neg(c)));
                const r2 = sub(f, op2, c);
                if (!r1.set || !r2.set) return null;
                const set = r1.set.intersect(r2.set);
                steps.push(
                    step({
                        title: eachLanguage((l) => `$${tex(f, l)} ${OP_TEX[OP_FLIP[op2]]} ${tex(simpOr(neg(c)), l)}$`),
                        tex: eachLanguage((l) => `${v} \\in ${intervalTex(r1.set, l)}`),
                        sub: r1.steps,
                    }),
                );
                steps.push(
                    step({
                        title: eachLanguage((l) => `$${tex(f, l)} ${OP_TEX[op2]} ${tex(c, l)}$`),
                        tex: eachLanguage((l) => `${v} \\in ${intervalTex(r2.set, l)}`),
                        sub: r2.steps,
                    }),
                );
                steps.push(step({ title: msg('solve.inequality.intersect'), tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`) }));
                return { set, steps, type: 'abs' };
            }
            // > and >=
            if (cv < 0 || (cz && op2 === '>=')) {
                steps.push(
                    step({ title: msg('solve.inequality.absolute_value_is_always_non_negative'), text: msg('solve.inequality.inequality_holds_for_every') }),
                );
                return { set: IntervalSet.all(), steps, type: 'abs' };
            }
            if (cz) {
                steps.push(step({ title: msg('solve.inequality.absolute_value_is_positive_except_where'), tex: eachLanguage((l) => `${tex(f, l)} \\ne 0`) }));
                const r = solveCore(f, N0, { ...ctx, depth: ctx.depth + 1 });
                const set =
                    r.kind === 'roots'
                        ? IntervalSet.all().minus(IntervalSet.points(r.roots.map((x) => x.node)))
                        : r.kind === 'all'
                          ? IntervalSet.empty()
                          : IntervalSet.all();
                return { set, steps: [...steps, ...r.steps], type: 'abs' };
            }
            steps.push(
                step({
                    title: msg('solve.inequality.two_alternatives'),
                    tex: eachLanguage(
                        (l) => `${tex(f, l)} ${OP_TEX[OP_FLIP[op2]]} ${tex(simpOr(neg(c)), l)} ${orTex(l)} ${tex(f, l)} ${OP_TEX[op2]} ${tex(c, l)}`,
                    ),
                    text: msg('solve.inequality.distance_from_zero_is_more_than'),
                }),
            );
            const r1 = sub(f, OP_FLIP[op2], simpOr(neg(c)));
            const r2 = sub(f, op2, c);
            if (!r1.set || !r2.set) return null;
            const set = r1.set.union(r2.set);
            steps.push(
                step({
                    title: eachLanguage((l) => `$${tex(f, l)} ${OP_TEX[OP_FLIP[op2]]} ${tex(simpOr(neg(c)), l)}$`),
                    tex: eachLanguage((l) => `${v} \\in ${intervalTex(r1.set, l)}`),
                    sub: r1.steps,
                }),
            );
            steps.push(
                step({
                    title: eachLanguage((l) => `$${tex(f, l)} ${OP_TEX[op2]} ${tex(c, l)}$`),
                    tex: eachLanguage((l) => `${v} \\in ${intervalTex(r2.set, l)}`),
                    sub: r2.steps,
                }),
            );
            steps.push(step({ title: msg('solve.inequality.take_union'), tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`) }));
            return { set, steps, type: 'abs' };
        }
    }
    // several absolute values (or |f| against an expression): intervals by the zeros of the insides
    let pts = [];
    for (const a of A) {
        const P = Poly.fromNode(a.args[0], v);
        if (!P) return null;
        if (P.degree >= 1) pts.push(...solveAnyPoly(P, { v, domain: 'real' }).roots);
    }
    pts = mergeRoots(pts);
    if (pts.length > 12) return null;
    steps.push(
        step({
            title: msg('solve.inequality.mark_zeros_of_expressions_inside_absolute'),
            tex: eachLanguage((l) => (pts.length ? pts.map((p) => `${v} = ${tex(p.node, l)}`).join(';\\ ') : '\\varnothing')),
            text: msg('solve.inequality.on_each_interval_between_them_absolute'),
        }),
    );
    const bounds = [null, ...pts, null];
    let set = IntervalSet.empty();
    for (let k = 0; k + 1 < bounds.length; k++) {
        const lo = bounds[k];
        const hi = bounds[k + 1];
        const t = lo === null && hi === null ? 0 : lo === null ? hi.approx - 1 : hi === null ? lo.approx + 1 : (lo.approx + hi.approx) / 2;
        const Ei = simpOr(
            mapNode(E, (n) => {
                if (n.type !== 'fn' || n.name !== 'abs' || !containsVar(n, v)) return undefined;
                return approxOf(n.args[0], { [v]: t }) >= 0 ? n.args[0] : neg(n.args[0]);
            }),
        );
        const piece = IntervalSet.interval(lo && lo.node, hi && hi.node, lo !== null, false);
        const sub = ineqCore(Ei, op, N0, { ...ctx, depth: ctx.depth + 1 });
        if (!sub.set) return null;
        const part = sub.set.intersect(piece);
        set = set.union(part);
        steps.push(
            step({
                title: eachLanguage((l) => msg('solve.inequality.on', { piece: intervalTex(piece, l) }).in(l)),
                tex: eachLanguage((l) => `${tex(Ei, l)} ${OP_TEX[op]} 0 \\;\\Rightarrow\\; ${v} \\in ${intervalTex(part, l)}`),
                sub: sub.steps,
            }),
        );
    }
    steps.push(step({ title: msg('solve.inequality.take_union'), tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    return { set, steps, type: 'abs' };
}

// p·b^f − q·b^g op 0 with q/p a power of b: b^f op b^(g + m) → f op g + m (by the monotonicity of b^t)
function twoPowersIneq(E, op, ctx) {
    const v = ctx.v;
    const ts = summands(E);
    if (ts.length !== 2) return null;
    const parts = ts.map((t) => {
        const { coef, rest } = splitCoeff(t);
        const r = rest ?? N1;
        if (r.type !== 'pow' || containsVar(r.base, v) || !containsVar(r.exp, v)) return null;
        const bi = baseInfo(r.base);
        return bi && { coef, base: r.base, exp: r.exp, bi };
    });
    if (parts.some((x) => !x) || !sameBase(parts[0].bi.c, parts[1].bi.c)) return null;
    let [P1, P2] = parts;
    const op1 = op;
    if (P1.coef.isNeg()) {
        [P1, P2] = [P2, P1];
    }
    if (!P1.coef.isPos() || !P2.coef.isNeg()) return null;
    // P1.coef·b1^f + P2.coef·b2^g op 0  ⇔  b1^f op (−P2.coef/P1.coef)·b2^g
    const k = P2.coef.neg().div(P1.coef);
    const m = exactPower(P1.bi.c, num(k));
    if (m === null) return null;
    // everything as powers of the primitive base c: b1^f = c^(k1 f)
    const c = P1.bi.c;
    const cN = baseNode(c);
    const left = simpOr(mul(num(P1.bi.k), P1.exp));
    const right = simpOr(add(mul(num(P2.bi.k), P2.exp), num(m)));
    const dec = approxOf(cN) < 1;
    const op3 = dec ? OP_FLIP[op1] : op1;
    const steps = [
        step({
            title: msg('solve.inequality.bring_both_sides_to_one_base'),
            tex: eachLanguage((l) => `${tex(pow(cN, left), l)} ${OP_TEX[op1]} ${tex(pow(cN, right), l)}`),
            text: msg('solve.inequality.move_one_power_to_right_and', { p: (lng) => num(k).value.toTex(lng), p2: (lng) => tex(pow(cN, num(m)), lng) }),
        }),
        step({
            title: dec
                ? msg('solve.inequality.base_is_below_1_function_decreases', { cN: (lng) => tex(cN, lng) })
                : msg('solve.inequality.base_is_above_1_function_increases', { cN: (lng) => tex(cN, lng) }),
            tex: ineqTexB(left, op3, right),
        }),
    ];
    const r = ineqCore(left, op3, right, { ...ctx, depth: ctx.depth + 1 });
    if (!r.set) return null;
    return { set: r.set, steps: [...steps, ...r.steps], chart: r.chart, type: 'exponential' };
}

function expIneq(E, op, ctx) {
    const v = ctx.v;
    const tp = twoPowersIneq(E, op, ctx);
    if (tp) return tp;
    const info = analyzeExp(E, v);
    if (!info || info.mixed) return null;
    const { c, terms, constant } = info;
    const cN = baseNode(c);
    const steps = [];
    const sub = (l2, o2, r2) => ineqCore(l2, o2, r2, { ...ctx, depth: ctx.depth + 1 });
    if (terms.length === 1 && terms[0].pows.length === 1) {
        const { coef, pows } = terms[0];
        const kv = approxOf(coef);
        if (!Number.isFinite(kv) || kv === 0) return null;
        const op2 = kv < 0 ? OP_FLIP[op] : op;
        const R = simpOr(div(neg(constant), coef));
        const b = pows[0].base;
        const f = pows[0].exp;
        steps.push(
            step({
                title: msg('solve.inequality.isolate_power'),
                tex: ineqTexB(pows[0], op2, R),
                text: kv < 0 ? msg('solve.inequality.we_divided_by_negative_number_so') : undefined,
            }),
        );
        const Rv = approxOf(R);
        if (!(Rv > 0) || exactZero(R) === true) {
            const all = op2 === '>' || op2 === '>=';
            steps.push(
                step({
                    title: msg('solve.inequality.power_of_positive_number_is_always'),
                    text: all ? msg('solve.inequality.it_holds_for_every') : msg('solve.inequality.no_solutions'),
                }),
            );
            return { set: all ? IntervalSet.all() : IntervalSet.empty(), steps, type: 'exponential' };
        }
        const bv = approxOf(b);
        const dec = bv < 1;
        const op3 = dec ? OP_FLIP[op2] : op2;
        const bi = baseInfo(b);
        const r = exactPower(bi.c, R);
        const rhsN = r !== null ? num(r.div(bi.k)) : logNodeB(b, R);
        const rDisp = r !== null ? pow(b, rhsN) : null;
        steps.push(
            step({
                title: dec
                    ? msg('solve.inequality.base_is_below_1_function_decreases_2', { b: (lng) => tex(b, lng) })
                    : msg('solve.inequality.base_is_above_1_function_increases_2', { b: (lng) => tex(b, lng) }),
                tex: eachLanguage(
                    (l) =>
                        (rDisp ? `${tex(pows[0], l)} ${OP_TEX[op2]} ${tex(rDisp, l)} \\;\\Rightarrow\\; ` : '') + `${tex(f, l)} ${OP_TEX[op3]} ${tex(rhsN, l)}`,
                ),
            }),
        );
        const r2 = sub(f, op3, rhsN);
        if (!r2.set) return null;
        steps.push(...r2.steps);
        return { set: r2.set, steps, chart: r2.chart, type: 'exponential' };
    }
    // polynomial in t = c^(m x)
    const lin = [];
    for (const t of terms) {
        const lf = linearForm(t.g, [v]);
        const k = numValue(t.coef);
        if (!lf || !k || lf.coeffs[v].isZero()) return null;
        lin.push({ m: lf.coeffs[v], s: lf.constant, k, t });
    }
    let m = lin[0].m.abs();
    for (const x of lin) m = qGcd(m, x.m.abs());
    if (lin.some((x) => x.m.isNeg())) return null;
    const C0 = numValue(constant);
    if (!C0 || c === 'e') return null;
    const coefs = new Map([[0, C0]]);
    for (const x of lin) {
        const j = x.m.div(m);
        if (!j.isInt() || !x.s.isInt()) return null;
        const jj = Number(j.n);
        coefs.set(jj, (coefs.get(jj) ?? Q.ZERO).add(x.k.mul(c.pow(x.s.n))));
    }
    const maxJ = Math.max(...coefs.keys());
    if (maxJ > 6) return null;
    const arr = new Array(maxJ + 1).fill(Q.ZERO);
    for (const [j, q] of coefs) arr[j] = q;
    const Pt = new Poly(arr);
    const tNode = m.isInt() ? pow(num(c.pow(m.n)), sym(v)) : pow(cN, simpOr(mul(num(m), sym(v))));
    steps.push(
        step({
            title: msg('solve.inequality.substitute', { tNode: (lng) => tex(tNode, lng) }),
            tex: eachLanguage((l) => `${polyTex(Pt, 't', l)} ${OP_TEX[op]} 0`),
        }),
    );
    const tr = ineqCore(Pt.toNode('t'), op, N0, { ...ctx, v: 't', depth: ctx.depth + 1 });
    if (!tr.set) return null;
    const tset = tr.set.intersect(IntervalSet.above(0, false));
    steps.push(step({ title: msg('solve.inequality.solve_for_with'), tex: eachLanguage((l) => `t \\in ${intervalTex(tset, l)}`), sub: tr.steps }));
    const mq = m;
    const back = (node) => {
        const tv = approxOf(node);
        if (!(tv > 0)) return null;
        const r = exactPower(c, node);
        return r !== null ? num(r.div(mq)) : simpOr(div(logNode(c, node), num(mq)));
    };
    const parts = tset.parts.map((p) => ({
        lo: p.lo === null || p.lo.x <= 0 ? null : endOf(back(p.lo.node)),
        hi: p.hi === null ? null : endOf(back(p.hi.node)),
        loC: p.lo !== null && p.lo.x > 0 && p.loC,
        hiC: p.hiC,
    }));
    const set = new IntervalSet(parts);
    steps.push(
        step({
            title: msg('solve.inequality.substitute_back'),
            tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`),
            text: msg('solve.inequality.function_increases_so_bounds_map_to', { tNode: (lng) => tex(tNode, lng) }),
        }),
    );
    return { set, steps, chart: tr.chart, type: 'exponential' };
}

function logIneq(lhs, op, rhs, E, ctx) {
    const v = ctx.v;
    const an = analyzeLog(E, v);
    if (!an || an.vt.some((x) => x.info.varBase)) return null;
    const { vt, constant } = an;
    const steps = [];
    const sub = (l2, o2, r2) => ineqCore(l2, o2, r2, { ...ctx, depth: ctx.depth + 1 });
    const C = simpOr(sumNode(constant));
    let odz = IntervalSet.all();
    for (const x of vt) {
        const s = sub(x.info.arg, '>', N0);
        if (!s.set) return null;
        odz = odz.intersect(s.set);
    }
    steps.push(
        step({
            title: msg('solve.inequality.domain_arguments_of_logarithms_are_positive'),
            tex: eachLanguage((l) => `${vt.map((x) => `${tex(x.info.arg, l)} > 0`).join(',\\ ')} \\;\\Rightarrow\\; ${v} \\in ${intervalTex(odz, l)}`),
        }),
    );
    const monotone = (b) => {
        const dec = approxOf(b) < 1;
        return {
            dec,
            step: dec
                ? msg('solve.inequality.base_is_below_1_logarithm_decreases', { b: (lng) => tex(b, lng) })
                : msg('solve.inequality.base_is_above_1_logarithm_increases', { b: (lng) => tex(b, lng) }),
        };
    };
    let res;
    if (vt.length === 1 && vt[0].p === 1) {
        const { coef, info, F } = vt[0];
        const kv = approxOf(coef);
        if (!Number.isFinite(kv) || kv === 0) return null;
        const op2 = kv < 0 ? OP_FLIP[op] : op;
        const R = simpOr(div(neg(C), coef));
        if (!isConstNode(R)) return null;
        const val = simpOr(pow(info.base, R));
        const mono = monotone(info.base);
        const op3 = mono.dec ? OP_FLIP[op2] : op2;
        steps.push(step({ title: msg('solve.inequality.isolate_logarithm'), tex: ineqTexB(F, op2, R) }));
        steps.push(
            step({
                title: mono.step,
                tex: eachLanguage(
                    (l) =>
                        `${tex(F, l)} ${OP_TEX[op2]} ${tex(logNodeB(info.base, val), l)} \\;\\Rightarrow\\; ${tex(info.arg, l)} ${OP_TEX[op3]} ${tex(val, l)}`,
                ),
                text: msg('solve.inequality.we_wrote_as_logarithm', { R: (lng) => tex(R, lng), p: (lng) => tex(logNodeB(info.base, val), lng) }),
            }),
        );
        res = sub(info.arg, op3, val);
    } else if (vt.length === 2 && isZeroNode(C) && vt.every((x) => x.p === 1 && x.info.k.isOne()) && nodeKey(vt[0].info.base) === nodeKey(vt[1].info.base)) {
        const k0 = numValue(vt[0].coef);
        const k1 = numValue(vt[1].coef);
        if (!k0 || !k1 || !k0.add(k1).isZero()) return null;
        const [pos, negT] = k0.isPos() ? [vt[0], vt[1]] : [vt[1], vt[0]];
        const mono = monotone(pos.info.base);
        const op3 = mono.dec ? OP_FLIP[op] : op;
        steps.push(step({ title: mono.step, tex: eachLanguage((l) => `${tex(pos.info.arg, l)} ${OP_TEX[op3]} ${tex(negT.info.arg, l)}`) }));
        res = sub(pos.info.arg, op3, negT.info.arg);
    } else if (vt.length >= 2 && vt.every((x) => x.p === 1 && nodeKey(x.info.base) === nodeKey(vt[0].info.base) && numValue(x.coef)?.isInt())) {
        // Σ cᵢ·log_b fᵢ + C op 0 → log_b(Π fᵢ^cᵢ) op −C: on the domain every fᵢ > 0, so the rules hold
        const b = vt[0].info.base;
        const up = [];
        const down = [];
        for (const x of vt) {
            const c = numValue(x.coef);
            (c.isNeg() ? down : up).push(c.abs().isOne() ? x.info.arg : pow(x.info.arg, num(c.abs())));
        }
        const prod = down.length ? div(up.length ? mul(up) : N1, mul(down)) : mul(up);
        const R = simpOr(neg(C));
        if (!isConstNode(R)) return null;
        const val = simpOr(pow(b, R));
        const mono = monotone(b);
        const op3 = mono.dec ? OP_FLIP[op] : op;
        steps.push(
            step({
                title: msg('solve.inequality.write_sum_of_logarithms_as_one'),
                tex: ineqTexB(logNodeB(b, prod), op, R),
                text: msg('solve.inequality.on_domain_every_argument_is_positive'),
            }),
        );
        steps.push(
            step({
                title: mono.step,
                tex: eachLanguage((l) => `${tex(prod, l)} ${OP_TEX[op3]} ${tex(val, l)}`),
                text: msg('solve.inequality.we_wrote_as_logarithm', { R: (lng) => tex(R, lng), p: (lng) => tex(logNodeB(b, val), lng) }),
            }),
        );
        res = sub(prod, op3, val);
    } else if (vt.every((x) => nodeKey(x.F) === nodeKey(vt[0].F)) && vt.some((x) => x.p >= 2)) {
        // a polynomial in one logarithm: the substitution t = log_b f
        const F = vt[0].F;
        const tv = v === 't' ? 'u' : 't';
        const T0 = sym(tv);
        const poly = simpOr(add([...vt.map((x) => mul(x.coef, x.p === 1 ? T0 : pow(T0, num(x.p)))), ...constant]));
        const rt = ineqCore(poly, op, N0, { ...ctx, v: tv, depth: ctx.depth + 1 });
        if (!rt.set) return null;
        steps.push(step({ title: msg('solve.inequality.substitute_2', { tv, F: (lng) => tex(F, lng) }), tex: ineqTexB(poly, op, N0) }));
        steps.push(...rt.steps);
        steps.push(step({ title: msg('solve.inequality.we_got', { tv, p: (lng) => intervalTex(rt.set, lng) }) }));
        let back = IntervalSet.empty();
        const backSteps = [];
        for (const part of rt.set.parts) {
            let piece = IntervalSet.all();
            const conds = [];
            if (part.lo && part.hi && cmpEnd(part.lo, part.hi) === 0) conds.push(['=', part.lo.node]);
            else {
                if (part.lo) conds.push([part.loC ? '>=' : '>', part.lo.node]);
                if (part.hi) conds.push([part.hiC ? '<=' : '<', part.hi.node]);
            }
            for (const [o, c] of conds) {
                let r;
                if (o === '=') {
                    const e = solveEquation(rel('=', F, c), v, { steps: true });
                    if (e.kind !== 'roots' || e.families?.length || e.roots.some((x) => x.approxOnly)) return null;
                    r = { set: IntervalSet.points(e.roots.map((x) => x.node)), steps: e.steps.slice(0, -1) };
                } else r = sub(F, o, c);
                if (!r.set) return null;
                piece = piece.intersect(r.set);
                backSteps.push(
                    step({
                        title: eachLanguage((l) => `$${tex(F, l)} ${OP_TEX[o]} ${tex(c, l)}$`),
                        tex: eachLanguage((l) => `${v} \\in ${intervalTex(r.set, l)}`),
                        sub: r.steps,
                    }),
                );
            }
            back = back.union(piece);
        }
        steps.push(step({ title: msg('solve.inequality.back_to', { v }), tex: eachLanguage((l) => `${v} \\in ${intervalTex(back, l)}`), sub: backSteps }));
        res = { set: back, steps: [] };
    } else return null;
    if (!res.set) return null;
    steps.push(...res.steps);
    const set = res.set.intersect(odz);
    steps.push(step({ title: msg('solve.inequality.take_domain_into_account'), tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    return { set, steps, chart: res.chart, type: 'logarithmic' };
}

/** The domain of a node in v as an IntervalSet (trigonometric conditions are not handled) → {D, odz} or null. */
function domainOf(node, v, ctx = { v, domain: 'real', depth: 0 }) {
    const conds = collectConds(node, v);
    if (conds.some((c) => c.kind === 'cos' || c.kind === 'sin')) return null;
    const odz = conds.length ? odzInfo(conds, v) : null;
    // conditions that are not rational (√x ≠ 0, ln x ≠ 0) are solved here one by one
    let D = IntervalSet.all();
    for (const c of conds) {
        let cs = signSet(c.expr, OP_OF[c.kind], v);
        if (!cs && c.kind === 'ne0') {
            const e = solveEquation(rel('=', c.expr, N0), v, { steps: false });
            if (e.kind === 'none') cs = IntervalSet.all();
            else if (e.kind === 'roots' && !e.families?.length && !e.roots.some((x) => x.approxOnly))
                cs = IntervalSet.all().minus(IntervalSet.points(e.roots.map((x) => x.node)));
        } else if (!cs) cs = ineqCore(c.expr, OP_OF[c.kind], N0, { ...ctx, v, depth: (ctx.depth ?? 0) + 1 }).set;
        if (!cs) return null;
        D = D.intersect(cs);
    }
    return { D, odz };
}

/** The set where a function of one variable is defined (null when it cannot be found exactly). */
export function domainSet(input, v = 'x') {
    const node = typeof input === 'string' ? parse(input) : input;
    return domainOf(node, v)?.D ?? null;
}

/**
 * The generalised method of intervals: f(x) = lhs − rhs is continuous on the domain, so its sign can change only at
 * its zeros and at the ends of the domain. The zeros come from solveEquation (exact, finite); the sign on every
 * interval is checked at several points, and any disagreement (a zero the equation solver missed) refuses.
 */
function rootsIneq(lhs, op, rhs, E, ctx) {
    const v = ctx.v;
    const JUMPY = new Set(['sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'floor', 'ceil', 'frac', 'sign', 'round', 'mod']);
    if (nodeSome(E, (n) => n.type === 'fn' && JUMPY.has(n.name))) return null;
    const node = rel(op, lhs, rhs);
    const dom = domainOf(node, v, ctx);
    if (!dom) return null;
    const { D, odz } = dom;
    const eq = solveEquation(rel('=', lhs, rhs), v, { steps: true });
    let roots;
    if (eq.kind === 'none') roots = [];
    else if (eq.kind === 'roots' && !eq.families?.length && !eq.roots.some((x) => x.approxOnly))
        roots = eq.roots.map((x) => x.node).filter((x) => D.contains(x));
    else return null;
    const f = (x) => approxOf(E, { [v]: x });
    const ends = [];
    const addEnd = (n) => {
        const e = endOf(n);
        if (Number.isFinite(e.x) && !ends.some((o) => cmpEnd(o, e) === 0)) ends.push(e);
    };
    roots.forEach(addEnd);
    for (const p of D.parts) {
        if (p.lo) addEnd(p.lo.node);
        if (p.hi) addEnd(p.hi.node);
    }
    ends.sort((a, b) => cmpEnd(a, b));
    const good = (y) => (op === '>' ? y > 0 : op === '>=' ? y >= 0 : op === '<' ? y < 0 : y <= 0);
    const parts = [];
    const signs = [];
    for (let k = 0; k <= ends.length; k++) {
        const a = k > 0 ? ends[k - 1] : null;
        const b = k < ends.length ? ends[k] : null;
        let xs;
        if (a && b) xs = [1, 2, 3, 4, 5].map((j) => a.x + ((b.x - a.x) * j) / 6);
        else if (b) xs = [0.05, 0.5, 2, 10, 100].map((d) => b.x - d * (1 + Math.abs(b.x)));
        else if (a) xs = [0.05, 0.5, 2, 10, 100].map((d) => a.x + d * (1 + Math.abs(a.x)));
        else xs = [-100, -3, 0.5, 3, 100];
        const inside = xs.map((x) => D.contains(x));
        if (inside.every((z) => !z)) continue;
        if (!inside.every(Boolean)) return null;
        const ys = xs.map(f);
        if (ys.some((y) => Number.isNaN(y))) return null; // ±∞ from an overflow still has a sign
        const sg = ys.filter((y) => Math.abs(y) > 1e-12).map(Math.sign);
        if (!sg.length || sg.some((z) => z !== sg[0])) return null;
        signs.push({ a, b, sign: sg[0] });
        if (good(sg[0])) parts.push({ lo: a, hi: b, loC: false, hiC: false });
    }
    for (const e of ends) {
        if (!D.contains(e.node)) continue;
        const isRoot = roots.some((r) => cmpEnd(endOf(r), e) === 0);
        const y = isRoot ? 0 : f(e.x);
        if (Number.isFinite(y) && (isRoot ? !strictOf(op) : good(y))) parts.push({ lo: e, hi: e, loC: true, hiC: true });
    }
    const set = new IntervalSet(parts).intersect(D);
    const steps = [];
    // solveInequality shows the domain itself unless there are logarithms
    if (odz && (odz.partial || nodeSome(node, (n) => n.type === 'fn' && (n.name === 'log' || n.name === 'ln' || n.name === 'lg')))) {
        steps.push(
            step({
                title: msg('solve.inequality.domain_admissible_values'),
                tex: eachLanguage((l) => `${odz.conds.map((c) => condTex(c, l)).join(',\\ ')} \\;\\Rightarrow\\; ${v} \\in ${intervalTex(D, l)}`),
                text: odz.text,
            }),
        );
    }
    const fNode = isZeroNode(simpOr(rhs)) ? lhs : add(lhs, neg(rhs));
    steps.push(
        step({
            title: msg('solve.inequality.generalised_method_of_intervals'),
            tex: eachLanguage((l) => `f(${v}) = ${tex(fNode, l)}`),
            text: msg('solve.inequality.function_is_continuous_on_its_domain'),
        }),
    );
    steps.push(step({ title: msg('solve.inequality.zeros_solve_equation'), tex: eq.answer?.tex, sub: eq.steps.slice(0, -1) }));
    const ivTex = (s, l) => {
        const p = new IntervalSet([{ lo: s.a, hi: s.b, loC: false, hiC: false }]);
        return `${intervalTex(p, l)}\\!:\\ ${s.sign > 0 ? '+' : '-'}`;
    };
    steps.push(
        step({
            title: msg('solve.inequality.signs_on_intervals'),
            tex: eachLanguage((l) => signs.map((s) => ivTex(s, l)).join(';\\quad ')),
            text: msg('solve.inequality.sign_on_each_interval_is_checked'),
        }),
    );
    const want = op === '>' || op === '>=' ? '+' : '−';
    steps.push(step({ title: msg('solve.inequality.take_intervals_with', { p: want }), tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    return { set, steps, type: 'intervals' };
}

/**
 * Solve an inequality in one variable (also a double one: a < f(x) ≤ b).
 * → {set: IntervalSet | null, steps, signChart: {points: [{x, tex, kind: 'zero'|'pole', included, mult}], signs} | null,
 *    answer: {tex, text}, type, odz?, reason? (when unsupported), approx?}
 */
export function solveInequality(input, v = 'x', opts = {}) {
    const node = typeof input === 'string' ? parse(input, { vars: v && v.length > 1 ? [v] : [] }) : input;
    const withSteps = opts.steps !== false;
    const out = (r) => {
        const res = { set: null, steps: [], signChart: null, ...r, v };
        res.answer = res.set
            ? { tex: eachLanguage((l) => `${v} \\in ${intervalTex(res.set, l)}`), text: eachLanguage((l) => intervalText(res.set, l)) }
            : { tex: '', text: res.reason ?? msg('solve.inequality.could_not_solve') };
        if (res.set)
            res.steps.push(
                step({
                    title: msg('solve.inequality.answer'),
                    tex: res.answer.tex,
                    final: true,
                    text: res.approx ? msg('solve.inequality.bounds_are_approximate') : undefined,
                }),
            );
        else if (res.reason) res.steps.push(step({ title: msg('solve.inequality.could_not_solve_2'), text: res.reason, final: true }));
        if (!withSteps) res.steps = [];
        return res;
    };
    if (node.type === 'chain') {
        v = pickVar(node, v);
        let set = IntervalSet.all();
        const steps = [step({ title: msg('solve.inequality.double_inequality_is_system_of_two') })];
        for (let k = 0; k < node.ops.length; k++) {
            const r = solveInequality(rel(node.ops[k], node.items[k], node.items[k + 1]), v, { steps: true });
            if (!r.set) return out({ reason: r.reason, steps });
            set = set.intersect(r.set);
            steps.push(
                step({
                    title: eachLanguage((l) => `$${tex(rel(node.ops[k], node.items[k], node.items[k + 1]), l)}$`),
                    tex: r.answer.tex,
                    sub: r.steps.slice(0, -1),
                }),
            );
        }
        steps.push(step({ title: msg('solve.inequality.intersect'), tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`) }));
        return out({ set, steps, type: 'double' });
    }
    if (node.type !== 'rel' || node.op === '=') return out({ reason: msg('solve.inequality.inequality_is_needed') });
    v = pickVar(node, v);
    const others = freeVars(node).filter((x) => x !== v);
    if (others.length) return out({ reason: msg('solve.inequality.besides_there_are_other_letters_inequalities', { v, p: others.join(', ') }) });
    const ctx = { v, domain: 'real', depth: 0 };
    if (node.op === '!=') {
        const r = solveEquation(rel('=', node.lhs, node.rhs), v, { steps: true });
        const conds = collectConds(node, v);
        const dom = conds.length ? (odzInfo(conds, v).set ?? IntervalSet.all()) : IntervalSet.all();
        let set = null;
        if (r.kind === 'roots' && !r.families && !r.roots.some((x) => x.approxOnly)) set = dom.minus(IntervalSet.points(r.roots.map((x) => x.node)));
        else if (r.kind === 'none') set = dom;
        else if (r.kind === 'all' || r.kind === 'set') set = dom.minus(r.set ?? IntervalSet.all());
        if (!set) return out({ reason: msg('solve.inequality.could_not_solve_corresponding_equation_exactly') });
        return out({
            set,
            steps: [step({ title: msg('solve.inequality.solve_equation_and_exclude_its_roots'), sub: r.steps, tex: r.answer.tex })],
            type: 'ne',
        });
    }
    const steps = [];
    const conds = collectConds(node, v).filter((c) => !(c.whys.size === 1 && c.whys.has('den')));
    let odz = null;
    if (conds.length && !nodeSome(node, (n) => n.type === 'fn' && (n.name === 'log' || n.name === 'ln' || n.name === 'lg'))) {
        odz = odzInfo(conds, v);
        steps.push(odz.step);
    }
    let core;
    try {
        core = ineqCore(node.lhs, node.op, node.rhs, ctx);
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        core = { set: null, steps: [], reason: e.msg };
    }
    steps.push(...core.steps);
    if (!core.set) return out({ steps, reason: core.reason ?? msg('solve.inequality.this_kind_of_inequality_is_not') });
    let set = core.set;
    if (odz) {
        if (odz.set === null) return out({ steps, reason: msg('solve.inequality.could_not_find_domain_exactly') });
        const before = set;
        set = set.intersect(odz.set);
        if (!before.equals(set))
            steps.push(step({ title: msg('solve.inequality.take_domain_into_account'), tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    }
    // denominators that cancelled during simplification still exclude their zeros
    const dens = collectConds(node, v).filter((c) => c.kind === 'ne0' || c.kind === 'gt0');
    for (const c of dens) {
        const ds = signSet(c.expr, OP_OF[c.kind], v);
        if (!ds) continue;
        const before = set;
        set = set.intersect(ds);
        if (!before.equals(set)) {
            steps.push(
                step({
                    title: msg('solve.inequality.exclude_points_where_fails', { c: (lng) => condTex(c, lng) }),
                    tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`),
                    text: msg('solve.inequality.fraction_cancelled_while_simplifying_but_expression'),
                }),
            );
        }
    }
    return out({
        set,
        steps,
        signChart: core.chart ?? null,
        type: core.type,
        odz: odz && { tex: odz.tex, text: odz.text, set: odz.set },
        approx: !!core.approx,
    });
}
