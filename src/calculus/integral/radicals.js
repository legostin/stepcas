// integral/radicals — square roots of quadratics and ∫Pₙ(x)/√Q dx by undetermined coefficients.

import { splitCoeff } from '../../core/simplify.js';
import { Q } from '../../core/rational.js';
import { containsVar, mul, sym, pow, add, div, fn, num } from '../../core/ast.js';
import { Poly } from '../../core/poly.js';
import { step } from '../../core/steps.js';
import { calcTex } from '../derivative/index.js';
import { HALF, N1, N2, T_, bt, iTex, isNum, lnAbs, q, trySimp, tx } from './common.js';
import { qn, solveQ } from './rational.js';

// ---- square roots of quadratics

function quadRootShape(f, v) {
    const { coef, rest } = splitCoeff(f);
    if (!rest) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    let rad = null;
    const others = [];
    for (const x of fs) {
        if (x.type === 'pow' && isNum(x.exp) && (x.exp.value.eq(Q.HALF) || x.exp.value.eq(q(-1, 2))) && containsVar(x.base, v)) {
            if (rad) return null;
            rad = x;
        } else others.push(x);
    }
    if (!rad) return null;
    const Qp = Poly.fromNode(rad.base, v);
    if (!Qp || Qp.degree !== 2) return null;
    const lin = others.length ? Poly.fromNode(mul(others), v) : new Poly([Q.ONE]);
    if (!lin || lin.degree > 1) return null;
    return { coef, Qp, e: rad.exp.value, B: lin.coeff(1).mul(coef), C: lin.coeff(0).mul(coef), radBase: rad.base };
}

export function mQuadRoot(f, ctx) {
    const { v } = ctx;
    const sh = quadRootShape(f, v);
    if (!sh) return null;
    const { Qp, e, B, C, radBase } = sh;
    const X = sym(v);
    const [c, b, a] = [Qp.coeff(0), Qp.coeff(1), Qp.coeff(2)];
    const D = b.mul(b).sub(a.mul(c).mul(4));
    const sqrtQ = pow(radBase, HALF);
    const lin2 = add(mul(qn(a.mul(2)), X), qn(b));
    const M = B.div(a.mul(2));
    const Nn = C.sub(B.mul(b).div(a.mul(2)));
    const parts = [];
    let text;
    const tShift = add(X, qn(b.div(a.mul(2))));
    if (e.isNeg()) {
        // ∫(Bx + C)/√Q = (B/a)√Q + N∫dx/√Q
        if (!M.isZero()) parts.push(mul(qn(B.div(a)), sqrtQ));
        if (!Nn.isZero()) {
            if (a.isPos()) parts.push(mul(qn(Nn), div(N1, pow(qn(a), HALF)), lnAbs(add(X, qn(b.div(a.mul(2))), div(sqrtQ, pow(qn(a), HALF))), v)));
            else {
                if (!D.isPos()) return null;
                parts.push(mul(qn(Nn), div(N1, pow(qn(a.neg()), HALF)), fn('asin', div(add(mul(qn(a.mul(-2)), X), qn(b.neg())), pow(qn(D), HALF)))));
            }
        }
        text = a.isPos()
            ? T_('Под корнем квадратный трёхчлен с положительным старшим коэффициентом. Выделяем полный квадрат и пользуемся «длинным логарифмом»: ∫dt/√(t² + k) = ln|t + √(t² + k)| + C. Если в числителе есть x, сначала отделяем производную подкоренного выражения.',
                'A quadratic with a positive leading coefficient under the root. Complete the square and use ∫dt/√(t² + k) = ln|t + √(t² + k)| + C. If x is in the numerator, first split off the derivative of the radicand.')
            : T_('Под корнем квадратный трёхчлен с отрицательным старшим коэффициентом. Выделяем полный квадрат: получается ∫dt/√(m² − t²) = arcsin(t/m) + C. Если в числителе есть x, сначала отделяем производную подкоренного выражения.',
                'A quadratic with a negative leading coefficient under the root. Completing the square gives ∫dt/√(m² − t²) = arcsin(t/m) + C. If x is in the numerator, first split off the derivative of the radicand.');
    } else {
        // ∫(Bx + C)√Q = (B/(3a)) Q^{3/2} + N∫√Q
        if (!M.isZero()) parts.push(mul(qn(B.div(a.mul(3))), pow(radBase, num(q(3, 2)))));
        if (!Nn.isZero()) {
            // ∫√Q dx with Q = a(t² + K), t = x + b/2a, K = (4ac − b²)/(4a²):
            //   a > 0: (t/2)√Q + (√a·K/2)·ln|t + √Q/√a|;   a < 0 (Q = |a|(m² − t²)): (t/2)√Q + (√|a|·m²/2)·arcsin(t/m)
            const K = D.neg().div(a.mul(a).mul(4));
            const sa = pow(qn(a.abs()), HALF);
            const half = mul(div(tShift, N2), sqrtQ);
            if (a.isPos()) {
                parts.push(mul(qn(Nn), add(half, mul(qn(K.div(2)), sa, lnAbs(add(tShift, div(sqrtQ, sa)), v)))));
            } else {
                const m2 = K.neg();
                if (!m2.isPos()) return null;
                parts.push(mul(qn(Nn), add(half, mul(qn(m2.div(2)), sa, fn('asin', div(tShift, pow(qn(m2), HALF)))))));
            }
        }
        text = T_('Корень из квадратного трёхчлена: выделяем полный квадрат и пользуемся формулами ∫√(m² − t²)dt = (t/2)√(m² − t²) + (m²/2)arcsin(t/m) + C и ∫√(t² + k)dt = (t/2)√(t² + k) + (k/2)ln|t + √(t² + k)| + C.',
            'The root of a quadratic: complete the square and use ∫√(m² − t²)dt = (t/2)√(m² − t²) + (m²/2)arcsin(t/m) + C and ∫√(t² + k)dt = (t/2)√(t² + k) + (k/2)ln|t + √(t² + k)| + C.');
    }
    if (!parts.length) return null;
    const F = add(parts);
    const complete = completeSquareTex(a, b, c, v);
    return {
        F,
        method: 'quadratic-root',
        step: step({
            title: T_('Квадратный трёхчлен под корнем', 'A quadratic under the root'),
            tex: bt((L) => `${complete ? complete(L) + ',\\quad ' : ''}${iTex(f, v, L)} = ${tx(trySimp(F) ?? F, L)}`),
            text,
            rule: 'quadratic-root',
        }),
    };
}

function completeSquareTex(a, b, c, v) {
    if (b.isZero()) return null;
    const X = sym(v);
    const h = b.div(a.mul(2));
    const k = c.sub(b.mul(b).div(a.mul(4)));
    const sq = pow(add(X, qn(h)), N2);
    const node = add(a.isOne() ? sq : mul(qn(a), sq), qn(k));
    const orig = new Poly([c, b, a]).toNode(v);
    return (L) => `${tx(orig, L)} = ${toTex2(node, L)}`;
}

function toTex2(n, L) {
    // keep (x + h)² unsimplified
    return calcTex(n, L);
}

// ---- ∫Pₙ(x)/√Q dx = Rₙ₋₁(x)·√Q + λ∫dx/√Q (undetermined coefficients)

/** ∫dx/√Q for a quadratic Q = ax² + bx + c (the «long logarithm» or arcsin), or null. */
function invSqrtQuad(Qp, v, radBase) {
    const X = sym(v);
    const [c, b, a] = [Qp.coeff(0), Qp.coeff(1), Qp.coeff(2)];
    const sqrtQ = pow(radBase, HALF);
    if (a.isPos()) return mul(div(N1, pow(qn(a), HALF)), lnAbs(add(X, qn(b.div(a.mul(2))), div(sqrtQ, pow(qn(a), HALF))), v));
    const D = b.mul(b).sub(a.mul(c).mul(4));
    if (!D.isPos()) return null;
    return mul(div(N1, pow(qn(a.neg()), HALF)), fn('asin', div(add(mul(qn(a.mul(-2)), X), qn(b.neg())), pow(qn(D), HALF))));
}

export function mRadicalPoly(f, ctx) {
    const { v } = ctx;
    const { coef, rest } = splitCoeff(f);
    if (!rest) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    let rad = null;
    const others = [];
    for (const x of fs) {
        if (x.type === 'pow' && isNum(x.exp) && (x.exp.value.eq(Q.HALF) || x.exp.value.eq(q(-1, 2))) && containsVar(x.base, v)) {
            if (rad) return null;
            rad = x;
        } else others.push(x);
    }
    if (!rad) return null;
    const Qp = Poly.fromNode(rad.base, v);
    if (!Qp || Qp.degree !== 2) return null;
    let P = Poly.fromNode(mul([num(coef), ...others]), v);
    if (!P) return null;
    if (rad.exp.value.isPos()) P = P.mul(Qp);
    const n = P.degree;
    if (n < 2 || n > 12) return null;
    // P = R′·Q + R·Q′/2 + λ, R of degree n − 1
    const dQ = Qp.derivative();
    const cols = [];
    for (let j = 0; j < n; j++) {
        const xj = Poly.monomial(Q.ONE, j);
        cols.push(xj.derivative().mul(Qp).add(xj.mul(dQ).scale(Q.HALF)));
    }
    cols.push(new Poly([Q.ONE]));
    const Am = [];
    const bv = [];
    for (let i = 0; i <= n; i++) {
        Am.push(cols.map((c) => c.coeff(i)));
        bv.push(P.coeff(i));
    }
    const sol = solveQ(Am, bv);
    if (!sol) return null;
    const R = new Poly(sol.slice(0, n));
    const lam = sol[n];
    const J = lam.isZero() ? null : invSqrtQuad(Qp, v, rad.base);
    if (!lam.isZero() && !J) return null;
    const sqrtQ = pow(rad.base, HALF);
    const F = add([mul(R.toNode(v), sqrtQ), ...(J ? [mul(qn(lam), J)] : [])]);
    return {
        F,
        method: 'radical-polynomial',
        step: step({
            title: T_('Метод неопределённых коэффициентов', 'Undetermined coefficients'),
            tex: bt((L) => `${iTex(f, v, L)} = \\left(${tx(R.toNode(v), L)}\\right)\\sqrt{${tx(rad.base, L)}}${lam.isZero() ? '' : ` ${lam.isNeg() ? '-' : '+'} ${lam.abs().isOne() ? '' : qn(lam.abs()).value.toTex(L)}\\int \\frac{d${v}}{\\sqrt{${tx(rad.base, L)}}}`} = ${tx(trySimp(F) ?? F, L)}`),
            text: T_(`Многочлен, делённый на корень из квадратного трёхчлена: ∫Pₙ(x)/√Q dx = Rₙ₋₁(x)·√Q + λ∫dx/√Q. Коэффициенты многочлена R степени ${n - 1} и число λ находим, продифференцировав обе части и приравняв коэффициенты при одинаковых степенях x.`,
                `A polynomial over the root of a quadratic: ∫Pₙ(x)/√Q dx = Rₙ₋₁(x)·√Q + λ∫dx/√Q. The coefficients of R (degree ${n - 1}) and λ come from differentiating both sides and matching the coefficients of equal powers of x.`),
            rule: 'radical-polynomial',
        }),
    };
}
