// solve/rational — equations with fractions of polynomials; algebraic equations with irrational coefficients.

import { pow, num, mul, substitute, div, neg, nodeKey } from '../core/ast.js';
import { numDen, collectTerms } from '../core/expand.js';
import { Poly } from '../core/poly.js';
import { Q } from '../core/rational.js';
import { N0, S, T, byLang, exactZero, isConstNode, simpOr, tex } from './common.js';
import { reject } from './equation.js';
import { IntervalSet } from './intervals.js';
import { multOf, nodeQuadRoots, partStep, polyTex, solveAnyPoly } from './polynomial.js';
import { hasI, mergeRoots, mkRoot, mkRootC } from './roots.js';

// ---------------------------------------------------------------- rational equations

export function polyLcm(A, B) {
    const g = A.gcd(B);
    return A.mul(B).divmod(g).q.monic();
}

/** Factored TeX of a polynomial: (x − 2)(x + 2). */
export function factoredNode(P, v) {
    const f = P.factor();
    const parts = f.factors.map((x) => (x.mult > 1 ? pow(x.poly.toNode(v), num(x.mult)) : x.poly.toNode(v)));
    if (!f.constant.isOne()) parts.unshift(num(f.constant));
    return parts.length ? (parts.length === 1 ? parts[0] : mul(parts)) : num(f.constant);
}

export function termsOfSum(n) {
    return n.type === 'add' ? n.args : [n];
}

/** f(x) = g(x) with polynomial fractions: common denominator, numerator = 0, poles excluded. */
export function solveRational(lhs, rhs, E, ctx) {
    const v = ctx.v;
    const parts = [];
    for (const t of termsOfSum(E)) {
        let nd;
        try {
            nd = numDen(t);
        } catch {
            return null;
        }
        const Pn = Poly.fromNode(nd.num, v);
        const Pd = Poly.fromNode(nd.den, v);
        if (!Pn || !Pd || Pd.isZero()) return null;
        parts.push({ Pn, Pd });
    }
    if (!parts.some((p) => p.Pd.degree >= 1)) return null;
    let L = new Poly([Q.ONE]);
    for (const p of parts) L = polyLcm(L, p.Pd.monic());
    let N = new Poly([]);
    for (const p of parts) {
        const { q, r } = L.divmod(p.Pd);
        if (!r.isZero()) return null;
        N = N.add(p.Pn.mul(q));
    }
    const Lp = L.primitive();
    const k = Lp.lead.div(L.lead);
    N = N.scale(k);
    const steps = [];
    const Lnode = factoredNode(Lp, v);
    steps.push(S(T('Переносим всё влево и приводим к общему знаменателю', 'Move everything to the left and bring to a common denominator'), {
        tex: byLang((l) => `\\frac{${polyTex(N, v, l)}}{${tex(Lnode, l)}} = 0`),
        text: T('Дробь равна нулю, когда числитель равен нулю, а знаменатель — нет.', 'A fraction is zero when its numerator is zero and its denominator is not.'),
    }));
    const poles = Lp.degree >= 1 ? solveAnyPoly(Lp, { v, domain: 'real' }).roots : [];
    const res = N.degree >= 1 ? solveAnyPoly(N, { ...ctx }) : { kind: N.isZero() ? 'all' : 'none', roots: [], cplx: [], steps: [] };
    if (N.degree >= 1) steps.push(partStep(byLang((l) => `${polyTex(N, v, l)} = 0`), res, v));
    const Np = N.primitive();
    for (const r of res.roots ?? []) if (r.minPoly && !r.approxOnly) r.mult = multOf(Np, r.minPoly.primitive());
    let roots = mergeRoots(res.roots ?? []);
    const bad = roots.filter((r) => Math.abs(Lp.evalNumber(r.approx)) <= 1e-9 * Math.max(1, Math.abs(r.approx)) ** Lp.degree && (r.approxOnly || exactZero(substitute(Lp.toNode(v), { [v]: r.node })) !== false));
    if (bad.length) {
        reject(ctx, bad, 'pole');
        roots = roots.filter((r) => !bad.includes(r));
        steps.push(S(T('Исключаем корни, при которых знаменатель равен нулю', 'Drop the roots that make the denominator zero'), {
            tex: byLang((l) => bad.map((r) => `${v} = ${tex(r.node, l)}`).join(',\\ ')),
            text: T('При этих значениях знаменатель обращается в ноль — дробь не имеет смысла, поэтому это не корни.', 'At these values the denominator is zero and the fraction makes no sense, so they are not roots.'),
        }));
    }
    if (N.degree < 1) {
        if (N.isZero()) {
            const set = IntervalSet.all().minus(IntervalSet.points(poles.map((p) => p.node)));
            steps.push(S(T('Числитель тождественно равен нулю', 'The numerator is identically zero'), { text: T('Равенство верно при всех допустимых значениях переменной.', 'The equality holds for all admissible values.') }));
            return { kind: 'all', roots: [], set, steps, type: 'rational' };
        }
        steps.push(S(T('Числитель — ненулевое число', 'The numerator is a non-zero number'), { text: T('Дробь с ненулевым числителем нулю не равна — корней нет.', 'A fraction with a non-zero numerator is never zero: no roots.') }));
        return { kind: 'none', roots: [], steps, type: 'rational' };
    }
    return { kind: roots.length ? 'roots' : 'none', roots, complexRoots: mergeRoots(res.cplx ?? []), steps, numeric: !!res.numeric, type: 'rational' };
}

// ---------------------------------------------------------------- algebraic with irrational constant coefficients

export function solveNodePoly(E, ctx) {
    const v = ctx.v;
    let ct;
    try {
        ct = collectTerms(E, v);
    } catch {
        return null;
    }
    if (!ct) return null;
    const degs = [...ct.keys()];
    if (!degs.length || degs.some((d) => !Number.isInteger(d) || d < 0 || d > 2)) return null;
    for (const c of ct.values()) if (!isConstNode(c)) return null;
    const c2 = ct.get(2) ?? N0;
    const c1 = ct.get(1) ?? N0;
    const c0 = ct.get(0) ?? N0;
    const steps = [S(T('Переносим всё в левую часть', 'Move everything to the left'), { tex: byLang((l) => `${tex(E, l)} = 0`) })];
    const cx = [c0, c1, c2].some(hasI);
    if (!ct.has(2)) {
        if (!ct.has(1)) return null;
        const q = div(neg(c0), c1);
        const r = simpOr(q, cx ? { complex: true } : undefined);
        const shown = cx && nodeKey(r) !== nodeKey(simpOr(q)) ? simpOr(q) : null;
        steps.push(S(T(`Выражаем $${v}$`, `Solve for $${v}$`), {
            tex: byLang((l) => `${v} = ${shown ? `${tex(shown, l)} = ` : ''}${tex(r, l)}`),
            text: shown ? T('Чтобы разделить на комплексное число, умножаем числитель и знаменатель на сопряжённое к знаменателю.', 'To divide by a complex number, multiply the numerator and the denominator by the conjugate of the denominator.') : undefined,
        }));
        const root = cx ? mkRootC(r) : mkRoot(r);
        if (root.complex && ctx.domain !== 'complex') {
            steps.push(S(T('Корень не действительный — действительных корней нет', 'The root is not real: no real roots')));
            return { kind: 'none', roots: [], complexRoots: [root], steps, type: 'linear' };
        }
        return { kind: 'roots', roots: [root], steps, type: 'linear' };
    }
    const res = nodeQuadRoots(c2, c1, c0, ctx);
    steps.push(...res.steps);
    const all = ctx.domain === 'complex' ? [...res.roots, ...res.cplx] : res.roots;
    return { kind: all.length ? 'roots' : 'none', roots: all, complexRoots: ctx.domain === 'complex' ? [] : res.cplx, steps, type: 'quadratic' };
}
