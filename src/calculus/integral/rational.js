// integral/rational — rational functions: division, partial fractions over Q, completing the square, and the even
// quartic x⁴ + px² + q through t = x ∓ √q/x.

import { num, mul, pow, div, fn, add, sym, neg, nodeKey } from '../../core/ast.js';
import { bigLcm, Q } from '../../core/rational.js';
import { ratFunctionOf } from '../derivative/index.js';
import { step } from '../../core/steps.js';
import { Poly } from '../../core/poly.js';
import { HALF, N0, N1, N2, T_, bt, iTex, lnAbs, q, simp, trySimp, tx } from './common.js';
import { I } from './engine.js';
import { canonicalRational } from './trig.js';

// ---- rational functions

export function solveQ(A, b) {
    const n = A.length;
    const M = A.map((row, i) => [...row, b[i]]);
    for (let col = 0; col < n; col++) {
        let p = col;
        while (p < n && M[p][col].isZero()) p++;
        if (p === n) return null;
        [M[col], M[p]] = [M[p], M[col]];
        const inv = M[col][col].inv();
        for (let j = col; j <= n; j++) M[col][j] = M[col][j].mul(inv);
        for (let i = 0; i < n; i++) {
            if (i === col || M[i][col].isZero()) continue;
            const k = M[i][col];
            for (let j = col; j <= n; j++) M[i][j] = M[i][j].sub(k.mul(M[col][j]));
        }
    }
    return M.map((row) => row[n]);
}

export const qn = (x) => num(x);

/** ∫ A/(ax + b)^k dx */
function intLinearPiece(A, lin, k, v) {
    const a = lin.coeff(1);
    const base = lin.toNode(v);
    if (k === 1) return mul(qn(A.div(a)), lnAbs(base, v));
    return mul(qn(A.neg().div(a.mul(k - 1))), pow(base, num(1 - k)));
}

/** ∫ dt/(t² + m2)^k (m2 > 0 rational, t a node) by the reduction formula. */
function intJ(k, tNode, m2) {
    const m = pow(qn(m2), HALF);
    if (k === 1) return mul(div(N1, m), fn('atan', div(tNode, m)));
    const kk = k - 1;
    const first = div(tNode, mul(qn(m2.mul(2 * kk)), pow(add(pow(tNode, N2), qn(m2)), num(kk))));
    const coef = qn(q(2 * k - 3).div(m2.mul(2 * kk)));
    return add(first, mul(coef, intJ(k - 1, tNode, m2)));
}

/** ∫ (Bx + C)/(ax² + bx + c)^k dx for a quadratic without rational roots. */
function intQuadPiece(B, Cc, quad, k, v) {
    const X = sym(v);
    const [c, b, a] = [quad.coeff(0), quad.coeff(1), quad.coeff(2)];
    const qNode = quad.toNode(v);
    const M = B.div(a.mul(2));
    const Nn = Cc.sub(B.mul(b).div(a.mul(2)));
    const disc = b.mul(b).sub(a.mul(c).mul(4));
    const parts = [];
    const lin2 = add(mul(qn(a.mul(2)), X), qn(b)); // 2ax + b
    if (k === 1) {
        if (!M.isZero()) parts.push(mul(qn(M), lnAbs(qNode, v)));
        if (!Nn.isZero()) {
            if (disc.isNeg()) {
                const s = pow(qn(disc.neg()), HALF);
                parts.push(mul(qn(Nn.mul(2)), div(N1, s), fn('atan', div(lin2, s))));
            } else {
                const s = pow(qn(disc), HALF);
                parts.push(mul(qn(Nn), div(N1, s), lnAbs(div(add(lin2, neg(s)), add(lin2, s)), v)));
            }
        }
        return add(parts);
    }
    if (!disc.isNeg()) return null;
    if (!M.isZero()) parts.push(mul(qn(M.div(1 - k)), pow(qNode, num(1 - k))));
    if (!Nn.isZero()) {
        const tNode = add(X, qn(b.div(a.mul(2))));
        const m2 = disc.neg().div(a.mul(a).mul(4));
        parts.push(mul(qn(Nn.mul(a.inv().pow(BigInt(k)))), intJ(k, tNode, m2)));
    }
    return add(parts);
}

/** A partial fraction for display: (2 − x)/(3(x² − x + 1)) rather than (2/3 − x/3)/(x² − x + 1), sign in front. */
function fracPiece(numP, denNode, v) {
    let P = numP;
    let sign = false;
    if (P.lead.isNeg() && P.c.every((c) => !c.isPos())) {
        sign = true;
        P = P.neg();
    }
    let l = 1n;
    for (const c of P.c) l = bigLcm(l, c.d);
    const top = P.scale(new Q(l)).toNode(v);
    const bottom = l === 1n ? denNode : mul(num(l), denNode);
    const d = div(top, bottom);
    return sign ? neg(d) : d;
}

export function mRational(f, ctx) {
    const { v } = ctx;
    const r = ratFunctionOf(f, v);
    if (!r) return null;
    if (r.den.degree < 1) {
        // a polynomial in disguise, (x² − 1)/(x − 1) − x: integrate its plain form
        const P0 = canonicalRational(f, v);
        if (!P0 || nodeKey(P0) === nodeKey(f)) return null;
        const rp = I(P0, ctx);
        if (!rp) return null;
        return { ...rp, step: step({
            title: T_('Упрощаем дробь', 'Simplify the fraction'),
            tex: bt((L) => `${tx(f, L)} = ${tx(P0, L)}`),
            text: T_('Дробь сокращается, под интегралом остаётся многочлен.', 'The fraction cancels, leaving a polynomial under the integral.'),
            rule: 'simplify',
            sub: [rp.step],
        }) };
    }
    const P = r.num;
    const D = r.den;
    const { q: polyPart, r: rem } = P.divmod(D);
    const { constant, factors } = D.factor();
    if (factors.some((x) => x.poly.degree > 2)) return null;
    // partial fractions: unknowns per (factor, power)
    const terms = [];
    for (const { poly, mult } of factors) for (let k = 1; k <= mult; k++) terms.push({ poly, k });
    const N = D.degree;
    const cols = [];
    for (const t of terms) {
        const base = D.divmod(t.poly.pow(t.k)).q;
        if (t.poly.degree === 1) cols.push({ t, kind: 'A', p: base });
        else {
            cols.push({ t, kind: 'B', p: base.mul(new Poly([Q.ZERO, Q.ONE])) });
            cols.push({ t, kind: 'C', p: base });
        }
    }
    if (cols.length !== N) return null;
    const A = [];
    const bvec = [];
    for (let i = 0; i < N; i++) {
        A.push(cols.map((c) => c.p.coeff(i)));
        bvec.push(rem.coeff(i));
    }
    const sol = rem.isZero() ? cols.map(() => Q.ZERO) : solveQ(A, bvec);
    if (!sol) return null;
    const pieces = [];
    let ci = 0;
    for (const t of terms) {
        if (t.poly.degree === 1) {
            pieces.push({ t, A: sol[ci++] });
        } else {
            pieces.push({ t, B: sol[ci++], C: sol[ci++] });
        }
    }
    // integrate
    const Fparts = [];
    const subs = [];
    if (!polyPart.isZero()) {
        const pp = polyPart.toNode(v);
        const rp = I(simp(pp), ctx);
        if (!rp) return null;
        Fparts.push(rp.F);
        subs.push(rp.step);
    }
    const pieceNodes = [];
    for (const pc of pieces) {
        const denNode = pc.t.k === 1 ? pc.t.poly.toNode(v) : pow(pc.t.poly.toNode(v), num(pc.t.k));
        let node;
        let Fp;
        if (pc.t.poly.degree === 1) {
            if (pc.A.isZero()) continue;
            node = fracPiece(new Poly([pc.A]), denNode, v);
            Fp = intLinearPiece(pc.A, pc.t.poly, pc.t.k, v);
        } else {
            if (pc.B.isZero() && pc.C.isZero()) continue;
            node = fracPiece(new Poly([pc.C, pc.B]), denNode, v);
            Fp = intQuadPiece(pc.B, pc.C, pc.t.poly, pc.t.k, v);
            if (!Fp) return null;
        }
        pieceNodes.push(node);
        Fparts.push(Fp);
        subs.push(pieceStep(node, Fp, pc, v));
    }
    const F = add(Fparts.length ? Fparts : [N0]);
    // steps
    const steps = [];
    const fNode = div(P.toNode(v), D.toNode(v));
    if (!polyPart.isZero()) {
        steps.push(step({
            title: T_('Выделяем целую часть', 'Divide the polynomials'),
            tex: bt((L) => `${tx(fNode, L)} = ${tx(polyPart.toNode(v), L)}${rem.isZero() ? '' : (() => { const r = tx(fracPiece(rem, D.toNode(v), v), L); return r.startsWith('-') ? ' - ' + r.slice(1) : ' + ' + r; })()}`),
            text: T_('Степень числителя не меньше степени знаменателя, поэтому сначала делим многочлены уголком: дробь = целая часть + правильная дробь.', 'The numerator has at least the degree of the denominator, so first divide the polynomials: fraction = polynomial part + proper fraction.'),
            rule: 'division',
        }));
    }
    const factoredD = factorNode(constant, factors, v);
    const simpleDen = factors.length === 1 && factors[0].mult === 1;
    if (!rem.isZero() && !simpleDen) {
        steps.push(step({
            title: T_('Раскладываем знаменатель', 'Factor the denominator'),
            tex: bt((L) => `${tx(D.toNode(v), L)} = ${tx(factoredD, L)}`),
            text: T_('Находим корни знаменателя и раскладываем его на линейные множители и квадратные трёхчлены без действительных корней.', 'Find the roots of the denominator and split it into linear factors and quadratics without real roots.'),
            rule: 'factor',
        }));
        steps.push(step({
            title: T_('Простейшие дроби', 'Partial fractions'),
            tex: bt((L) => `${tx(fracPiece(rem, D.toNode(v), v), L)} = ${pieceNodes.map((n, i) => {
                const s = tx(n, L);
                return i === 0 ? s : (s.startsWith('-') ? ' - ' + s.slice(1) : ' + ' + s);
            }).join('')}`),
            text: T_('Раскладываем правильную дробь в сумму простейших: каждому множителю (x − a)ᵏ соответствуют дроби A/(x − a), …, A/(x − a)ᵏ, а квадратному трёхчлену — (Bx + C)/(…). Коэффициенты находим, приводя к общему знаменателю и приравнивая коэффициенты числителей (метод неопределённых коэффициентов).',
                'Split the proper fraction into partial fractions: a factor (x − a)ᵏ gives A/(x − a), …, A/(x − a)ᵏ, and a quadratic gives (Bx + C)/(…). The coefficients come from bringing everything to the common denominator and matching the numerators (undetermined coefficients).'),
            rule: 'partial-fractions',
        }));
    }
    if (steps.length === 0 && subs.length === 1) {
        // a single simple fraction: its own step says everything
        return { F, method: 'rational', step: { ...subs[0], title: T_('Рациональная дробь', 'Rational function'), rule: 'rational' } };
    }
    steps.push(step({
        title: T_('Интегрируем каждую дробь', 'Integrate each fraction'),
        tex: bt((L) => `${iTex(f, v, L)} = ${tx(simp(F), L)}`),
        rule: 'sum',
        sub: subs,
    }));
    return {
        F,
        method: 'rational',
        step: step({
            title: T_('Рациональная дробь', 'Rational function'),
            tex: bt((L) => `${iTex(f, v, L)} = ${tx(simp(F), L)}`),
            text: T_('Подынтегральная функция — отношение многочленов. Такие интегралы всегда берутся: выделяем целую часть и раскладываем остаток на простейшие дроби.', 'The integrand is a ratio of polynomials. Such integrals can always be done: take out the polynomial part and split the rest into partial fractions.'),
            rule: 'rational',
            sub: steps,
        }),
    };
}

/**
 * (c₂x² + c₀)/(x⁴ + px² + q) with a denominator irreducible over ℚ and without real roots (∫dx/(x⁴ + 1)):
 * write the numerator through x² + r and x² − r (r = √q), divide by x² and substitute t = x ∓ r/x —
 * (1 ± r/x²)dx = dt and (x⁴ + px² + q)/x² = t² + (p ± 2r).
 */
export function mBiquadratic(f, ctx) {
    const { v } = ctx;
    const rf = ratFunctionOf(f, v);
    if (!rf || rf.den.degree !== 4 || rf.num.degree > 2) return null;
    const D = rf.den;
    const P = rf.num;
    if (!D.coeff(1).isZero() || !D.coeff(3).isZero() || !P.coeff(1).isZero()) return null;
    const a4 = D.coeff(4);
    const p = D.coeff(2).div(a4);
    const qq = D.coeff(0).div(a4);
    if (!qq.isPos()) return null;
    const { factors } = D.factor();
    if (factors.length !== 1 || factors[0].poly.degree !== 4) return null; // splits over ℚ: mRational does it
    const X = sym(v);
    const r = simp(pow(qn(qq), HALF));
    const rv = Math.sqrt(qq.toNumber());
    if (!(p.toNumber() > -2 * rv)) return null; // real roots
    const c2 = P.coeff(2).div(a4);
    const c0 = P.coeff(0).div(a4);
    // c₂x² + c₀ = A(x² + r) + B(x² − r)
    const A = simp(div(add(qn(c2), div(qn(c0), r)), N2));
    const B = simp(div(add(qn(c2), neg(div(qn(c0), r))), N2));
    const x2 = pow(X, N2);
    const denNode = D.scale(a4.inv()).toNode(v);
    const isZ = (n) => n.type === 'num' && n.value.isZero();
    const parts = [];
    const subs = [];
    const piece = (coef, sign) => {
        // sign +1: ∫(x² + r)/(…), t = x − r/x;  −1: ∫(x² − r)/(…), t = x + r/x
        const tView = add(X, sign > 0 ? neg(div(r, X)) : div(r, X));
        const m = simp(sign > 0 ? add(qn(p), mul(N2, r)) : add(qn(p), neg(mul(N2, r))));
        const mv = sign > 0 ? p.toNumber() + 2 * rv : p.toNumber() - 2 * rv;
        let G;
        let Gt;
        const T0 = sym('t');
        // back to x without fractions inside: t = (x² ∓ r)/x
        const tTop = add(x2, sign > 0 ? neg(r) : r);
        if (Math.abs(mv) < 1e-12) {
            G = neg(div(X, tTop));
            Gt = neg(div(N1, T0));
        } else if (mv > 0) {
            const sm = simp(pow(m, HALF));
            G = mul(div(N1, sm), fn('atan', div(tTop, mul(sm, X))));
            Gt = mul(div(N1, sm), fn('atan', div(T0, sm)));
        } else {
            const sm = simp(pow(neg(m), HALF));
            const rr = sign > 0 ? neg(r) : r;
            G = mul(div(N1, mul(N2, sm)), fn('ln', fn('abs', div(add(x2, neg(mul(sm, X)), rr), add(x2, mul(sm, X), rr)))));
            Gt = mul(div(N1, mul(N2, sm)), fn('ln', fn('abs', div(add(T0, neg(sm)), add(T0, sm)))));
        }
        parts.push(mul(coef, G));
        const numN = add(x2, sign > 0 ? r : neg(r));
        const one = add(N1, sign > 0 ? div(r, x2) : neg(div(r, x2)));
        const inner = add([x2, ...(p.isZero() ? [] : [qn(p)]), div(qn(qq), x2)]);
        subs.push(step({
            title: sign > 0 ? T_(`Замена $t = ${tx(tView, 'ru')}$`, `Substitute $t = ${tx(tView, 'en')}$`) : T_(`Замена $t = ${tx(tView, 'ru')}$`, `Substitute $t = ${tx(tView, 'en')}$`),
            tex: bt((L) => `\\int \\frac{${tx(numN, L)}}{${tx(denNode, L)}}\\,d${v} = \\int \\frac{${tx(one, L)}}{${tx(inner, L)}}\\,d${v} = \\int \\frac{dt}{${tx(simp(add(pow(T0, N2), m)), L)}} = ${tx(simp(Gt), L)} = ${tx(G, L)}`),
            text: T_(`Делим числитель и знаменатель на $${v}^2$. Тогда $dt = \\left(${tx(one, 'ru')}\\right)d${v}$, а $${tx(inner, 'ru')} = t^2 ${mv >= 0 ? '+' : '-'} ${tx(simp(sign > 0 || mv >= 0 ? m : neg(m)), 'ru')}$.`,
                `Divide the numerator and the denominator by $${v}^2$. Then $dt = \\left(${tx(one, 'en')}\\right)d${v}$ and $${tx(inner, 'en')} = t^2 ${mv >= 0 ? '+' : '-'} ${tx(simp(sign > 0 || mv >= 0 ? m : neg(m)), 'en')}$.`),
            rule: 'substitution',
        }));
    };
    if (!isZ(A)) piece(A, 1);
    if (!isZ(B)) piece(B, -1);
    if (!parts.length) return null;
    const F = add(parts);
    const split = add([...(isZ(A) ? [] : [mul(A, div(add(x2, r), denNode))]), ...(isZ(B) ? [] : [mul(B, div(add(x2, neg(r)), denNode))])]);
    const fNorm = div(P.scale(a4.inv()).toNode(v), denNode);
    const steps = [];
    if (!a4.isOne()) steps.push(step({ title: T_('Выносим старший коэффициент', 'Take out the leading coefficient'), tex: bt((L) => `${tx(f, L)} = ${tx(qn(a4.inv()), L)}\\cdot ${tx(div(P.toNode(v), denNode), L)}`), rule: 'const' }));
    if (subs.length > 1 || !(isZ(B) ? P.coeff(0).isZero() : false)) {
        steps.push(step({
            title: T_(`Раскладываем числитель по $${v}^2 \\pm ${tx(r, 'ru')}$`, `Split the numerator along $${v}^2 \\pm ${tx(r, 'en')}$`),
            tex: bt((L) => `${tx(fNorm, L)} = ${tx(split, L)}`),
            text: T_(`Знаменатель не раскладывается над рациональными числами. Приём: $${tx(denNode, 'ru')}$ делим на $${v}^2$ и замечаем, что $\\left(${v} \\mp \\frac{${tx(r, 'ru')}}{${v}}\\right)^2 = ${v}^2 + \\frac{${tx(qn(qq), 'ru')}}{${v}^2} \\mp ${tx(simp(mul(N2, r)), 'ru')}$, а производные этих скобок — $1 \\pm \\frac{${tx(r, 'ru')}}{${v}^2}$.`,
                `The denominator does not factor over the rationals. The trick: divide $${tx(denNode, 'en')}$ by $${v}^2$ and note that $\\left(${v} \\mp \\frac{${tx(r, 'en')}}{${v}}\\right)^2 = ${v}^2 + \\frac{${tx(qn(qq), 'en')}}{${v}^2} \\mp ${tx(simp(mul(N2, r)), 'en')}$, and the derivatives of the brackets are $1 \\pm \\frac{${tx(r, 'en')}}{${v}^2}$.`),
            rule: 'split',
        }));
    }
    steps.push(...subs);
    steps.push(step({
        title: T_('Собираем ответ', 'Put it together'),
        tex: bt((L) => `${iTex(f, v, L)} = ${tx(simp(mul(qn(a4.inv()), F)), L)} + C`),
        text: T_(`Первообразная годится на каждом из промежутков $${v} < 0$ и $${v} > 0$ (в нуле замена не определена).`, `The antiderivative holds on each of $${v} < 0$ and $${v} > 0$ (the substitution is undefined at zero).`),
        rule: 'sum',
    }));
    return {
        F: mul(qn(a4.inv()), F),
        method: 'biquadratic',
        step: step({ title: T_('Дробь со знаменателем $x^4 + px^2 + q$', 'A fraction over $x^4 + px^2 + q$'), tex: bt((L) => `${iTex(f, v, L)} = ${tx(simp(mul(qn(a4.inv()), F)), L)}`), rule: 'biquadratic', sub: steps }),
    };
}

function factorNode(constant, factors, v) {
    const fs = [];
    if (!constant.isOne()) fs.push(num(constant));
    for (const { poly, mult } of factors) fs.push(mult === 1 ? poly.toNode(v) : pow(poly.toNode(v), num(mult)));
    return fs.length === 1 ? fs[0] : mul(fs);
}

function pieceStep(node, Fp, pc, v) {
    let text;
    if (pc.t.poly.degree === 1) {
        text = pc.t.k === 1
            ? T_('∫A/(ax + b) dx = (A/a)·ln|ax + b| + C.', '∫A/(ax + b) dx = (A/a)·ln|ax + b| + C.')
            : T_('∫A/(ax + b)ᵏ dx = −A/(a(k − 1)(ax + b)ᵏ⁻¹) + C.', '∫A/(ax + b)ᵏ dx = −A/(a(k − 1)(ax + b)ᵏ⁻¹) + C.');
    } else {
        text = pc.t.k === 1
            ? T_('Выделяем в числителе производную знаменателя: (Bx + C) = (B/2a)(2ax + b) + (C − Bb/2a). Первая часть даёт логарифм, вторая после выделения полного квадрата в знаменателе — арктангенс (или логарифм, если у трёхчлена есть действительные корни).',
                'Split off the derivative of the denominator in the numerator: (Bx + C) = (B/2a)(2ax + b) + (C − Bb/2a). The first part gives a logarithm, the second, after completing the square, an arctangent (or a logarithm if the quadratic has real roots).')
            : T_('Выделяем производную знаменателя в числителе и полный квадрат в знаменателе; оставшийся интеграл ∫dt/(t² + m²)ᵏ понижаем формулой приведения.',
                'Split off the derivative of the denominator and complete the square; the remaining ∫dt/(t² + m²)ᵏ is reduced step by step.');
    }
    let middle = null;
    if (pc.t.poly.degree === 2 && pc.t.k === 1) {
        // (Bx + C)/(ax² + bx + c) = (B/2a)·(2ax + b)/(…) + (C − Bb/2a)/(a(x + b/2a)² + …)
        const [c, b, a] = [pc.t.poly.coeff(0), pc.t.poly.coeff(1), pc.t.poly.coeff(2)];
        const M = pc.B.div(a.mul(2));
        const Nn = pc.C.sub(pc.B.mul(b).div(a.mul(2)));
        const X = sym(v);
        const qNode = pc.t.poly.toNode(v);
        const lin2 = new Poly([b, a.mul(2)]).toNode(v);
        const h = b.div(a.mul(2));
        const sq = pow(h.isZero() ? X : add(X, qn(h)), N2);
        const kk = c.sub(b.mul(b).div(a.mul(4)));
        const square = kk.isZero() ? (a.isOne() ? sq : mul(qn(a), sq)) : add(a.isOne() ? sq : mul(qn(a), sq), qn(kk));
        const coef = (q0, L, first) => {
            if (q0.isOne()) return first ? '' : ' + ';
            if (q0.eq(-1)) return first ? '-' : ' - ';
            const t = qn(q0.abs()).value.toTex(L);
            return (q0.isNeg() ? (first ? '-' : ' - ') : first ? '' : ' + ') + t;
        };
        middle = (L) => {
            let out = '';
            if (!M.isZero()) out += `${coef(M, L, true)}\\int \\frac{${tx(lin2, L)}}{${tx(qNode, L)}}\\,d${v}`;
            if (!Nn.isZero()) out += `${coef(Nn, L, !out)}\\int \\frac{d${v}}{${tx(square, L)}}`;
            return out;
        };
    }
    return step({
        title: T_('Простейшая дробь', 'Partial fraction'),
        tex: bt((L) => `${iTex(node, v, L)} = ${middle ? middle(L) + ' = ' : ''}${tx(trySimp(Fp) ?? Fp, L)}`),
        text,
        rule: 'partial-fraction',
    });
}
