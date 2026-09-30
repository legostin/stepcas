// limit/taylor — Taylor polynomials with exact coefficients and the Lagrange bound of the remainder.

import { MathError } from '../../core/rational.js';
import { sym, substitute, freeVars, div, num, add, neg, pow, mul } from '../../core/ast.js';
import { quickDerivative } from '../derivative/index.js';
import { evaluate } from '../../core/evaluate.js';
import { canonContext } from '../../core/simplify.js';
import { step } from '../../core/steps.js';
import { N0, N1, T_, asNode, bt, evalAt, isNum, isZeroN, simp, tx } from './common.js';
import { limit } from './limit.js';
import { fmtNum } from './table.js';
import { msg } from '../../i18n/index.js';

// ---------------------------------------------------------------- Taylor polynomials

function factorialQ(k) {
    let r = 1n;
    for (let i = 2n; i <= BigInt(k); i++) r *= i;
    return r;
}

/**
 * Taylor polynomial of degree n at a: {poly (node in powers of (v − a)), coeffs: [nodes c₀…cₙ] (exact
 * where possible), terms: [{k, coeff, term}], tex, steps}. cₖ = f⁽ᵏ⁾(a)/k! (a limit when f⁽ᵏ⁾ has a
 * removable singularity at a).
 */
export function taylorPolynomial(node, v = 'x', a = 0, n = 5, opts = {}) {
    node = asNode(node);
    if (!Number.isInteger(n) || n < 0 || n > 20) throw new MathError(msg('calculus.limit.taylor.degree_must_be_from_0_to'), null, null, 'range');
    const A = simp(asNode(a));
    const X = sym(v);
    let d = simp(node);
    const coeffs = [];
    const derivs = [];
    for (let k = 0; k <= n; k++) {
        if (k > 0) d = quickDerivative(d, v);
        derivs.push(d);
        let val;
        try {
            val = simp(substitute(d, { [v]: A }));
            if (!Number.isFinite(evaluate(val)) && !freeVars(val).length) val = null;
        } catch {
            val = null;
        }
        if (!val) {
            const L = limit(d, v, A);
            if (!L.value || typeof L.value !== 'object') throw new MathError(msg('calculus.limit.taylor.derivative_of_order_is_undefined_at', { k }), null, null, 'undefined');
            val = L.value;
        }
        coeffs.push(simp(div(val, num(factorialQ(k)))));
    }
    const shift = isZeroN(A) ? X : add(X, neg(A));
    const terms = [];
    for (let k = 0; k <= n; k++) {
        if (isZeroN(coeffs[k])) continue;
        const pw = k === 0 ? N1 : k === 1 ? shift : pow(shift, num(k));
        terms.push({ k, coeff: coeffs[k], term: k === 0 ? coeffs[k] : mul(coeffs[k], pw) });
    }
    const C = canonContext();
    const poly = terms.length ? C.add(terms.map((t) => C.mul([t.coeff, t.k === 0 ? N1 : t.k === 1 ? C.simplify(shift) : C.pow(C.simplify(shift), num(t.k))]))) : N0;
    // ascending powers, as Taylor polynomials are written
    const termNode = (t) => {
        if (t.k === 0) return t.coeff;
        const pw = t.k === 1 ? shift : pow(shift, num(t.k));
        if (isNum(t.coeff)) return t.coeff.value.isOne() ? pw : t.coeff.value.eq(-1) ? neg(pw) : mul(t.coeff, pw);
        return mul(t.coeff, pw);
    };
    const polyShown = terms.length ? (terms.length === 1 ? termNode(terms[0]) : add(terms.map(termNode))) : N0;
    const tex = bt((L) => `T_{${n}}(${v}) = ${tx(polyShown, L)}`);
    const steps = [];
    if (opts.steps) {
        steps.push(step({
            title: msg('calculus.limit.taylor.taylor_s_formula'),
            tex: `T_{n}(${v}) = \\sum_{k=0}^{n} \\frac{f^{(k)}(a)}{k!}(${v} - a)^{k}`,
            text: msg('calculus.limit.taylor.coefficients_are_derivatives_at_point_divided'),
            rule: 'taylor',
        }));
        for (let k = 0; k <= n; k++) {
            steps.push(step({
                title: msg('calculus.limit.taylor.coefficient_of_degree', { k }),
                tex: bt((L) => `\\frac{f^{(${k})}(${tx(A, L)})}{${k}!} = ${tx(coeffs[k], L)}`),
                rule: 'coefficient',
            }));
        }
        const s = step({ title: msg('calculus.limit.taylor.taylor_polynomial'), tex, rule: 'answer' });
        s.final = true;
        steps.push(s);
    }
    return { poly: polyShown, polyCanonical: poly, coeffs, terms, tex, steps };
}

/**
 * Lagrange bound of the remainder |f(x) − Tₙ(x)| ≤ M·|x − a|ⁿ⁺¹/(n + 1)! with M = max |f⁽ⁿ⁺¹⁾| on the
 * segment between a and x (sampled numerically, with a small safety margin). → {bound, M, tex}.
 */
export function taylorRemainderBound(node, v = 'x', a = 0, n = 5, x = 1) {
    node = asNode(node);
    const A = evaluate(simp(asNode(a)));
    const X = typeof x === 'number' ? x : evaluate(simp(asNode(x)));
    let d = simp(node);
    for (let k = 0; k <= n; k++) d = quickDerivative(d, v);
    const lo = Math.min(A, X);
    const hi = Math.max(A, X);
    let M = 0;
    const N = 400;
    for (let i = 0; i <= N; i++) {
        const t = lo + ((hi - lo) * i) / N;
        const y = Math.abs(evalAt(d, v, t));
        if (!Number.isFinite(y)) return { bound: Infinity, M: Infinity, tex: null };
        M = Math.max(M, y);
    }
    M *= 1.0001;
    const fact = Number(factorialQ(n + 1));
    const bound = (M * Math.abs(X - A) ** (n + 1)) / fact;
    const tex = bt((L) => `\\left|R_{${n}}\\right| \\le \\frac{M\\,|${v} - a|^{${n + 1}}}{${n + 1}!} \\approx ${fmtNum(bound, L)}`);
    return { bound, M, tex };
}
