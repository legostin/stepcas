// solve/radical — irrational equations (roots of the unknown).

import { containsVar, numValue, nodeSome, mul, nodeKey, div, neg, pow, num, substitute } from '../core/ast.js';
import { N0, N1, S, approxOf, exactZero, expd, isolated, simpOr, tex } from './common.js';
import { reject, subSolve } from './equation.js';
import { pushPart, sumNode } from './polynomial.js';
import { termsOfSum } from './rational.js';
import { msg, eachLanguage } from '../i18n/index.js';

// ---------------------------------------------------------------- radicals (irrational equations)

const isRadical = (n, v) => n.type === 'pow' && containsVar(n.base, v) && (() => {
    const e = numValue(n.exp);
    return !!e && !e.isInt();
})();

export const hasRadical = (node, v) => nodeSome(node, (n) => isRadical(n, v));

/** A term c·R with a constant c and a single radical factor R → {coef, R}. */
export function splitRadicalTerm(t, v) {
    if (isRadical(t, v)) return { coef: N1, R: t };
    if (t.type !== 'mul') return null;
    const withV = t.args.filter((a) => containsVar(a, v));
    if (withV.length !== 1 || !isRadical(withV[0], v)) return null;
    const rest = t.args.filter((a) => !containsVar(a, v));
    return { coef: rest.length === 1 ? rest[0] : mul(rest), R: withV[0] };
}

export function solveRadical(lhs, rhs, E, ctx) {
    const v = ctx.v;
    if (ctx.depth > 6) return null;
    const terms = termsOfSum(E);
    const rads = terms.filter((t) => hasRadical(t, v));
    if (!rads.length) return null;
    // prefer the radical that stands alone on a side of the original equation
    const alone = [lhs, rhs].map((s) => simpOr(s)).find((s) => isRadical(s, v));
    let pickT = alone && rads.find((t) => nodeKey(splitRadicalTerm(t, v)?.R ?? N0) === nodeKey(alone));
    pickT = pickT ?? rads.find((t) => splitRadicalTerm(t, v));
    if (!pickT) return null;
    const { coef, R } = splitRadicalTerm(pickT, v);
    const others = terms.filter((t) => t !== pickT);
    const g = simpOr(div(neg(sumNode(others)), coef));
    const e = numValue(R.exp);
    const p = e.n;
    const q = e.d;
    if (p < 0n || q > 6n || p > 6n) return null;
    const f = R.base;
    const steps = [];
    const eqRT = eachLanguage((l) => `${tex(R, l)} = ${tex(g, l)}`);
    if (!isolated(lhs, rhs, R, g)) steps.push(S(msg('solve.radical.isolate_root'), { tex: eqRT }));
    const even = q % 2n === 0n;
    const gConst = !containsVar(g, v);
    if (even && gConst && approxOf(g) < 0 && exactZero(g) !== true) {
        steps.push(S(msg('solve.radical.even_root_is_never_negative_no')));
        return { kind: 'none', roots: [], steps, type: 'radical' };
    }
    const qn2 = Number(q);
    const lhs2 = expd(p === 1n ? f : pow(f, num(p))) ?? f;
    const rhs2 = expd(pow(g, num(q))) ?? pow(g, num(q));
    const gNonNeg = !gConst && hasRadical(g, v) && termsOfSum(simpOr(g)).every((t) => isRadical(t, v) && numValue(t.exp).d % 2n === 0n);
    const powWord = qn2 === 2 ? msg('solve.radical.squared') : qn2 === 3 ? msg('solve.radical.cubed') : msg('solve.radical.to_power', { qn2 });
    steps.push(S(msg('solve.radical.raise_both_sides', { p: (lng) => powWord[lng] }), {
        tex: eachLanguage((l) => `${tex(lhs2, l)} = ${tex(rhs2, l)}`),
        text: even
            ? (gConst || gNonNeg
                ? msg('solve.radical.raising_to_even_power_may_add')
                : msg('solve.radical.even_root_is_non_negative_so', { g: (lng) => tex(g, lng), R: (lng) => tex(R, lng) }))
            : msg('solve.radical.odd_power_is_equivalent_transformation_no'),
    }));
    const sub = subSolve(lhs2, rhs2, ctx);
    if (sub.kind === 'unsupported' || sub.periodic) return null;
    pushPart(steps, lhs2, rhs2, sub, v);
    if (sub.kind === 'all' || sub.kind === 'set') return null;
    let roots = sub.roots;
    if (even && !gConst) {
        const bad = [];
        const good = [];
        for (const r of roots) {
            const gv = approxOf(g, { [v]: r.approx });
            if (Number.isFinite(gv) && gv < -1e-9 && (r.approxOnly || exactZero(substitute(g, { [v]: r.node })) !== true)) bad.push(r);
            else good.push(r);
        }
        if (bad.length) {
            reject(ctx, bad, 'sign');
            steps.push(S(msg('solve.radical.drop_roots_where', { g: (lng) => tex(g, lng) }), {
                tex: eachLanguage((l) => bad.map((r) => `${v} = ${tex(r.node, l)}:\\ ${tex(substitute(g, { [v]: r.node }), l)} = ${tex(simpOr(substitute(g, { [v]: r.node })), l)} < 0`).join(';\\ ')),
                text: msg('solve.radical.these_are_extraneous_even_root_cannot'),
            }));
        }
        roots = good;
    }
    return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'radical', numeric: sub.numeric };
}
