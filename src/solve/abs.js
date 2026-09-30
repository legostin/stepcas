// solve/abs — equations with absolute values.

import { containsVar, sym, div, neg, substitute, add, mul, mapNode } from '../core/ast.js';
import { Poly } from '../core/poly.js';
import { N0, N1, S, TMP, approxOf, exactZero, isolated, linearIn, orTex, outermost, replaceNode, simpOr, tex } from './common.js';
import { reject, mergeRoots, rootsTex } from './roots.js';
import { IntervalSet } from './intervals.js';
import { partStep, pushPart, solveAnyPoly } from './polynomial.js';
import { msg, notation, eachLanguage } from '../i18n/index.js';

// ---------------------------------------------------------------- absolute value

export function solveAbs(lhs, rhs, E, ctx) {
    const v = ctx.v;
    const A = outermost(E, (n) => n.type === 'fn' && n.name === 'abs' && containsVar(n, v));
    if (!A.length) return null;
    const steps = [];
    if (A.length === 1) {
        const f = A[0].args[0];
        const Eu = replaceNode(E, A[0], sym(TMP));
        const li = linearIn(Eu, TMP, v);
        if (li) {
            const g = simpOr(div(neg(li.beta), li.alpha));
            const absT = (l) => tex(A[0], l);
            if (!containsVar(g, v)) {
                const gv = approxOf(g);
                if (!isolated(lhs, rhs, A[0], g))
                    steps.push(S(msg('solve.abs.isolate_absolute_value'), { tex: eachLanguage((l) => `${absT(l)} = ${tex(g, l)}`) }));
                if (gv < 0 && exactZero(g) !== true) {
                    steps.push(S(msg('solve.abs.absolute_value_is_never_negative_no')));
                    return { kind: 'none', roots: [], steps, type: 'abs' };
                }
                if (exactZero(g) === true) {
                    const sub = ctx.solve(f, N0);
                    steps.push(
                        partStep(
                            eachLanguage((l) => `${tex(f, l)} = 0`),
                            sub,
                            v,
                        ),
                    );
                    return { ...sub, steps, type: 'abs' };
                }
                steps.push(
                    S(msg('solve.abs.absolute_value_equals_positive_number_two'), {
                        tex: eachLanguage((l) => `${tex(f, l)} = ${tex(g, l)} ${orTex(l)} ${tex(f, l)} = ${tex(simpOr(neg(g)), l)}`),
                        text: msg('solve.abs.number_at_distance_from_zero_is'),
                    }),
                );
                let roots = [];
                for (const rhs2 of [g, simpOr(neg(g))]) {
                    const sub = ctx.solve(f, rhs2);
                    if (sub.kind === 'unsupported') return null;
                    roots.push(...sub.roots);
                    pushPart(steps, f, rhs2, sub, v);
                }
                roots = mergeRoots(roots);
                return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'abs' };
            }
            // |f| = g(x)
            if (!isolated(lhs, rhs, A[0], g)) steps.push(S(msg('solve.abs.isolate_absolute_value'), { tex: eachLanguage((l) => `${absT(l)} = ${tex(g, l)}`) }));
            steps.push(
                S(msg('solve.abs.open_absolute_value'), {
                    tex: eachLanguage((l) => `${tex(g, l)} \\ge 0,\\qquad ${tex(f, l)} = ${tex(g, l)} ${orTex(l)} ${tex(f, l)} = ${tex(simpOr(neg(g)), l)}`),
                    text: msg('solve.abs.absolute_value_is_non_negative_so'),
                }),
            );
            let cands = [];
            for (const rhs2 of [g, simpOr(neg(g))]) {
                const sub = ctx.solve(f, rhs2);
                if (sub.kind === 'unsupported') return null;
                if (sub.kind === 'all' || sub.kind === 'set') return absIntervals(E, A, ctx);
                cands.push(...sub.roots);
                pushPart(steps, f, rhs2, sub, v);
            }
            cands = mergeRoots(cands);
            const good = [];
            const bad = [];
            for (const r of cands) {
                const gv = approxOf(g, { [v]: r.approx });
                if (Number.isFinite(gv) && (gv >= -1e-12 || (!r.approxOnly && exactZero(substitute(g, { [v]: r.node })) === true))) good.push(r);
                else bad.push(r);
            }
            if (bad.length) {
                reject(ctx, bad, 'sign');
                steps.push(
                    S(msg('solve.abs.drop_roots_where', { g: (lng) => tex(g, lng) }), {
                        tex: eachLanguage((l) => bad.map((r) => `${v} = ${tex(r.node, l)}`).join(',\\ ')),
                        text: msg('solve.abs.absolute_value_cannot_equal_negative_number'),
                    }),
                );
            }
            return { kind: good.length ? 'roots' : 'none', roots: good, steps, type: 'abs' };
        }
    }
    if (A.length === 2 && E.type === 'add' && E.args.length === 2) {
        // α|f| + β|g| = 0 with α = −β: |f| = |g|
        const sp = E.args.map((t) => splitAbsTerm(t, v));
        if (sp.every(Boolean) && exactZero(add(sp[0].coef, sp[1].coef)) === true) {
            const f = sp[0].abs.args[0];
            const g = sp[1].abs.args[0];
            steps.push(
                S(msg('solve.abs.equal_absolute_values_expressions_are_equal'), {
                    tex: eachLanguage((l) => `${tex(f, l)} = ${tex(g, l)} ${orTex(l)} ${tex(f, l)} = ${tex(simpOr(neg(g)), l)}`),
                }),
            );
            let roots = [];
            let ok = true;
            for (const rhs2 of [g, simpOr(neg(g))]) {
                const sub = ctx.solve(f, rhs2);
                if (sub.kind === 'unsupported' || sub.kind === 'all' || sub.kind === 'set') {
                    ok = false;
                    break;
                }
                roots.push(...sub.roots);
                pushPart(steps, f, rhs2, sub, v);
            }
            if (ok) {
                roots = mergeRoots(roots);
                return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'abs' };
            }
            steps.length = 0;
        }
    }
    return absIntervals(E, A, ctx);
}

function splitAbsTerm(t, v) {
    const isAbs = (n) => n.type === 'fn' && n.name === 'abs' && containsVar(n, v);
    if (isAbs(t)) return { coef: N1, abs: t };
    if (t.type !== 'mul') return null;
    const withV = t.args.filter((a) => containsVar(a, v));
    if (withV.length !== 1 || !isAbs(withV[0])) return null;
    const rest = t.args.filter((a) => !containsVar(a, v));
    return { coef: rest.length === 1 ? rest[0] : mul(rest), abs: withV[0] };
}

/** Method of intervals for several absolute values with polynomial insides. */
function absIntervals(E, A, ctx) {
    const v = ctx.v;
    let pts = [];
    for (const a of A) {
        const P = Poly.fromNode(a.args[0], v);
        if (!P) return null;
        if (P.degree >= 1) pts.push(...solveAnyPoly(P, { v, domain: 'real' }).roots);
    }
    pts = mergeRoots(pts);
    if (pts.length > 12) return null;
    const steps = [
        S(msg('solve.abs.mark_zeros_of_expressions_inside_absolute'), {
            tex: eachLanguage((l) => (pts.length ? pts.map((p) => `${v} = ${tex(p.node, l)}`).join(';\\ ') : '\\varnothing')),
            text: msg('solve.abs.between_these_points_every_expression_inside'),
        }),
    ];
    const bounds = [null, ...pts, null];
    let roots = [];
    let set = IntervalSet.empty();
    for (let k = 0; k + 1 < bounds.length; k++) {
        const lo = bounds[k];
        const hi = bounds[k + 1];
        const t = lo === null && hi === null ? 0 : lo === null ? hi.approx - 1 : hi === null ? lo.approx + 1 : (lo.approx + hi.approx) / 2;
        const Ei = simpOr(
            mapNode(E, (n) => {
                if (n.type !== 'fn' || n.name !== 'abs' || !containsVar(n, v)) return undefined;
                const s = approxOf(n.args[0], { [v]: t });
                return s >= 0 ? n.args[0] : neg(n.args[0]);
            }),
        );
        const where = eachLanguage((l) => {
            if (lo === null && hi === null) return msg('solve.abs.for_all').in(l);
            const a = lo && tex(lo.node, l);
            const b = hi && tex(hi.node, l);
            const w = lo === null ? `${v} < ${b}` : hi === null ? `${v} \\ge ${a}` : `${a} \\le ${v} < ${b}`;
            return msg('solve.abs.for').in(l) + `$${w}$`;
        });
        const sub = ctx.solve(Ei, N0);
        if (sub.kind === 'unsupported') return null;
        const inside = (r) => typeof r.approx === 'number' && (lo === null || r.approx >= lo.approx - 1e-9) && (hi === null || r.approx <= hi.approx + 1e-9);
        let txt;
        if (sub.kind === 'all') {
            set = set.union(IntervalSet.interval(lo && lo.node, hi && hi.node, lo !== null, hi !== null));
            txt = msg('solve.abs.true_equality_whole_interval_fits');
        } else {
            const ok = sub.roots.filter(inside);
            const no = sub.roots.filter((r) => !inside(r));
            roots.push(...ok);
            txt = no.length
                ? msg('solve.abs.outside_interval', { p: (lng) => no.map((r) => tex(r.node, lng)).join(notation(lng).listTex) })
                : ok.length
                  ? msg('solve.abs.root_lies_in_interval')
                  : msg('solve.abs.no_roots_on_this_interval');
        }
        steps.push(
            S(where, {
                tex: eachLanguage(
                    (l) => `${tex(Ei, l)} = 0 \\;\\Rightarrow\\; ${sub.kind === 'all' ? msg('solve.abs.always_true').in(l) : rootsTex(sub.roots, v, l)}`,
                ),
                text: txt,
                sub: sub.steps,
            }),
        );
    }
    roots = mergeRoots(roots);
    if (!set.isEmpty()) {
        const full = set.union(IntervalSet.points(roots.map((r) => r.node)));
        return { kind: 'set', roots, set: full, steps, type: 'abs' };
    }
    return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'abs' };
}
