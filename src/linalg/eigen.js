// linalg/eigen — the characteristic polynomial, eigenvalues and eigenvectors, diagonalisation, powers.

import { Q } from '../core/rational.js';
import { numPolyRoots } from '../numbers/numeric/index.js';
import { E_, L, R, S, T, fail, qs, qt, qtp, shiftTex } from './common.js';
import { M, Matrix, needSquare, vecTex } from './core.js';
import { matDet } from './det.js';
import { fmatSvd } from './float.js';
import { intPrimitive, padd, pdeg, pdiv, pmul, psub, ptex, ptrim, quadFactor, quadRoots, rationalRootsQ, surdTex, toPoly } from './qpoly.js';
import { nullspaceFrom, reduce } from './reduce.js';
import { PARAMS, matInverse } from './systems.js';

// ---------------------------------------------------------------- characteristic polynomial and eigenvalues

/** det(A − λE) as Q coefficients (ascending), by Faddeev–LeVerrier. */
function charCoefs(A) {
    const n = A.rows;
    // Faddeev–LeVerrier for det(λE − A) = λⁿ + c₁λⁿ⁻¹ + … + cₙ
    const c = new Array(n + 1).fill(Q.ZERO);
    c[n] = Q.ONE; // coefficient of λⁿ (ascending index)
    let Mk = Matrix.zeros(n);
    const I = Matrix.identity(n);
    for (let k = 1; k <= n; k++) {
        Mk = A.mul(Mk).add(I.scale(c[n - k + 1]));
        c[n - k] = A.mul(Mk).trace().neg().div(new Q(BigInt(k)));
    }
    // det(A − λE) = (−1)ⁿ det(λE − A)
    return n % 2 ? c.map((v) => v.neg()) : c;
}

function detPolyMatrix(P) {
    // determinant of a matrix of polynomials (each entry Q[] ascending) by cofactor expansion (n ≤ 4)
    const n = P.length;
    if (n === 1) return P[0][0];
    if (n === 2) return psub(pmul(P[0][0], P[1][1]), pmul(P[0][1], P[1][0]));
    let s = [Q.ZERO];
    for (let j = 0; j < n; j++) {
        const minor = P.slice(1).map((r) => r.filter((_, c) => c !== j));
        const t = pmul(P[0][j], detPolyMatrix(minor));
        s = j % 2 ? psub(s, t) : padd(s, t);
    }
    return s;
}
const entryPolyTex = (p) => {
    // a − λ style for diagonal entries, plain number otherwise
    const t = ptrim(p);
    if (t.length === 1) return qt(t[0]);
    const c = t[0];
    return c.isZero() ? '-\\lambda' : `${qt(c)} - \\lambda`;
};

/**
 * Characteristic polynomial det(A − λE) (for odd n it is −λⁿ + …; the roots are the eigenvalues).
 * Returns a Poly in λ. {steps: true} → {value: Poly, coefs: Q[] (ascending), tex, steps} with the
 * determinant written out for 2×2 and 3×3 (Faddeev–LeVerrier for larger matrices).
 */
export function matCharPoly(A, opts = {}) {
    A = M(A);
    needSquare(A, L('Характеристический многочлен', 'The characteristic polynomial'));
    const n = A.rows;
    const coefs = charCoefs(A);
    const value = toPoly(coefs);
    if (!opts.steps) return value;
    const tex = ptex(coefs);
    const st = [];
    const P = A.a.map((r, i) => r.map((v, j) => (i === j ? [v, Q.MINUS_ONE] : [v])));
    const shifted = `\\begin{vmatrix} ${P.map((r) => r.map(entryPolyTex).join(' & ')).join(' \\\\ ')} \\end{vmatrix}`;
    st.push(S(L('Что ищем', 'What we look for'), T((l) => `\\det(A - \\lambda ${E_(l)}) = ${shifted}`),
        T((l) => (l === 'ru'
            ? 'Собственное значение λ — такое число, что A·v = λ·v для ненулевого вектора v, то есть (A − λE)·v = 0. У однородной системы есть ненулевое решение ровно тогда, когда её определитель равен нулю. Из диагональных элементов вычитаем λ.'
            : 'An eigenvalue λ is a number with A·v = λ·v for a non-zero vector v, that is (A − λI)·v = 0. A homogeneous system has a non-zero solution exactly when its determinant is zero. We subtract λ from the diagonal entries.')),
        { rule: 'charpoly-def' }));
    if (n === 2) {
        const [[a, b], [c, d]] = A.a;
        st.push(S(L('Раскрываем определитель 2×2', 'Expand the 2×2 determinant'),
            `(${entryPolyTex(P[0][0])})(${entryPolyTex(P[1][1])}) - ${qtp(b)} \\cdot ${qtp(c)} = ${tex}`,
            L(`Проверка: коэффициент при λ равен следу со знаком минус (след ${qs(a.add(d))}), а свободный член — определителю (${qs(a.mul(d).sub(b.mul(c)))}).`,
                `Check: the coefficient of λ is minus the trace (the trace is ${qs(a.add(d))}), and the constant term is the determinant (${qs(a.mul(d).sub(b.mul(c)))}).`),
            { rule: 'charpoly-2x2' }));
    } else if (n === 3) {
        const terms = [0, 1, 2].map((j) => {
            const minor = P.slice(1).map((r) => r.filter((_, c) => c !== j));
            return { j, e: P[0][j], minor, det: detPolyMatrix(minor) };
        }).filter((t) => pdeg(t.e) >= 0 && !(t.e.length === 1 && t.e[0].isZero()));
        const signed = (t) => (t.j % 2 ? t.e[0].neg() : t.e[0]);
        const lead = (t, k) => {
            if (t.j === 0) return `${k ? '+ ' : ''}(${entryPolyTex(t.e)})`;
            const c = signed(t);
            const a = c.abs();
            return `${c.isNeg() ? '-' : k ? '+' : ''} ${a.isOne() ? '' : qt(a)}`;
        };
        const expTex = terms.map((t, k) => {
            const mt = `\\begin{vmatrix} ${t.minor.map((r) => r.map(entryPolyTex).join(' & ')).join(' \\\\ ')} \\end{vmatrix}`;
            return `${lead(t, k)} ${mt}`;
        }).join(' ');
        st.push(S(L('Раскладываем по первой строке', 'Expand along the first row'), expTex,
            L('Каждый элемент первой строки умножаем на определитель, оставшийся после вычёркивания его строки и столбца; знаки чередуются: +, −, +.',
                'Each entry of the first row is multiplied by the determinant left after deleting its row and column; the signs alternate: +, −, +.'),
            { rule: 'cofactor' }));
        st.push(S(L('Раскрываем скобки', 'Multiply out'), terms.map((t, k) => `${lead(t, k)}\\left(${ptex(t.det)}\\right)`).join(' ') + ` = ${tex}`,
        L(`Проверка: у λ² стоит след (${qs(A.trace())}), свободный член равен определителю (${qs(coefs[0])}).`, `Check: the coefficient of λ² is the trace (${qs(A.trace())}), the constant term is the determinant (${qs(coefs[0])}).`),
        { rule: 'charpoly-3x3' }));
    } else {
        st.push(S(L('Метод Фаддеева — Леверье', 'The Faddeev–LeVerrier method'), T((l) => `\\det(A - \\lambda ${E_(l)}) = ${tex}`),
            L('Для больших матриц раскрывать определитель долго; коэффициенты считаем по рекуррентным формулам через следы матриц: M₁ = E, cₖ = −tr(A·Mₖ)/k, Mₖ₊₁ = A·Mₖ + cₖE.',
                'For bigger matrices expanding the determinant is slow; the coefficients come from a recurrence with traces: M₁ = I, cₖ = −tr(A·Mₖ)/k, Mₖ₊₁ = A·Mₖ + cₖI.'),
            { rule: 'faddeev-leverrier' }));
    }
    st.push(S(L('Характеристический многочлен', 'The characteristic polynomial'), T((l) => `\\det(A - \\lambda ${E_(l)}) = ${tex}`), null, { rule: 'answer' }));
    return { value, coefs, tex, steps: st };
}

function realNullVector(Af, lambda) {
    // unit vector spanning the (numerical) null space of A − λI: the right singular vector of the smallest singular value
    const B = Af.map((r, i) => r.map((v, j) => (i === j ? v - lambda : v)));
    const { S: s, V } = fmatSvd(B);
    let k = 0;
    for (let i = 1; i < s.length; i++) if (s[i] < s[k]) k = i;
    const v = V.map((row) => row[k]);
    const first = v.find((x) => Math.abs(x) > 1e-12) ?? 1;
    const norm = Math.hypot(...v) || 1;
    return v.map((x) => (x / norm) * Math.sign(first));
}

/**
 * Eigenvalues and eigenvectors. Exact where possible:
 *   {kind: 'rational', value: Q, vectors: Q[][] (eigenspace basis, primitive integer vectors), geometric}
 *   {kind: 'quadratic', exact: {p, q, s, sign} (p ± q√s; s < 0 ⇒ complex), vectorsApprox? (real, simple)}
 *   {kind: 'approx', approx: true} — numeric roots of an irreducible factor of degree ≥ 3
 * Every entry has re, im (numbers), multiplicity, tex. → {charPoly: Poly, coefs, values, steps?}.
 */
export function matEigen(A, opts = {}) {
    A = M(A);
    needSquare(A, L('Собственные значения', 'Eigenvalues'));
    const n = A.rows;
    const coefs = charCoefs(A);
    const { roots, rest } = rationalRootsQ(coefs);
    const values = [];
    const vecSteps = [];
    for (const { root, mult } of roots) {
        const B = A.sub(Matrix.identity(n).scale(root));
        const red = reduce(B.a, { steps: !!opts.steps });
        const vectors = nullspaceFrom(red.W, red.pivots, n, true);
        values.push({ kind: 'rational', value: root, re: root.toNumber(), im: 0, multiplicity: mult, geometric: vectors.length, vectors, tex: qt(root), approx: false });
        if (opts.steps) {
            const general = vectors.length === 1 ? `\\mathbf v = t${vecTex(vectors[0])}` : `\\mathbf v = ${vectors.map((v, k) => `${PARAMS[k] ?? `t_{${k + 1}}`}${vecTex(v)}`).join(' + ')}`;
            vecSteps.push(S(L(`Собственные векторы для λ = ${qs(root)}`, `Eigenvectors for λ = ${qs(root)}`),
                T((l) => `${root.isZero() ? 'A' : `(${shiftTex(root, l)})`}\\mathbf v = 0:\\quad ${B.toTex()} \\;\\Rightarrow\\; ${general}`),
                L(`Решаем однородную систему (A − λE)v = 0 методом Гаусса. ${vectors.length === 1 ? 'Одна свободная неизвестная — собственные векторы лежат на прямой (любое t ≠ 0)' : `Свободных неизвестных ${vectors.length} — собственные векторы заполняют пространство размерности ${vectors.length} (параметры любые, но не все нули)`}.${vectors.length < mult ? ` Кратность корня ${mult}, а независимых векторов только ${vectors.length}.` : ''}`,
                    `We solve the homogeneous system (A − λI)v = 0 by Gaussian elimination. ${vectors.length === 1 ? 'One free unknown: the eigenvectors lie on a line (any t ≠ 0)' : `${vectors.length} free unknowns: the eigenvectors fill a space of dimension ${vectors.length} (any parameters, not all zero)`}.${vectors.length < mult ? ` The root has multiplicity ${mult}, but there are only ${vectors.length} independent vectors.` : ''}`),
                { rule: 'eigenvectors', sub: red.steps }));
        }
    }
    // the rest: quadratic factors over Q, then numeric roots
    const quads = [];
    let R = rest;
    while (pdeg(R) >= 4) {
        const qf = quadFactor(R);
        if (!qf) break;
        const found = quads.find((x) => x.f.every((c, i) => c.eq(qf[i])));
        if (found) found.mult++;
        else quads.push({ f: qf, mult: 1 });
        R = pdiv(R, qf).q;
    }
    if (pdeg(R) === 2) {
        const lead = R[2];
        const f = R.map((c) => c.div(lead));
        const ints = intPrimitive(f);
        const qf = ints.map((x) => new Q(x));
        const found = quads.find((x) => x.f.every((c, i) => c.eq(qf[i])));
        if (found) found.mult++;
        else quads.push({ f: qf, mult: 1 });
        R = [lead];
    }
    const Af = A.toNumbers();
    const quadEntries = quads.map(() => []);
    for (const [qi, { f, mult }] of quads.entries()) {
        const { p, q, s } = quadRoots(f);
        for (const sign of [-1, 1]) {
            const sq = Math.sqrt(Math.abs(Number(s)));
            const re = s < 0n ? p.toNumber() : p.toNumber() + sign * q.toNumber() * sq;
            const im = s < 0n ? sign * q.toNumber() * sq : 0;
            const entry = { kind: 'quadratic', exact: { p, q, s, sign }, re, im, multiplicity: mult, tex: surdTex(p, q, s, sign), approx: false };
            if (im === 0 && mult === 1) entry.vectorsApprox = [realNullVector(Af, re)];
            values.push(entry);
            quadEntries[qi].push(entry);
        }
    }
    const approxVals = [];
    if (pdeg(R) >= 1) {
        const zs = numPolyRoots(R.map((c) => c.toNumber()));
        for (const z of zs) {
            const same = approxVals.find((v) => Math.hypot(v.re - z.re, v.im - z.im) < 1e-9 * Math.max(1, Math.hypot(z.re, z.im)));
            if (same) { same.multiplicity++; continue; }
            approxVals.push({ kind: 'approx', re: z.re, im: z.im, multiplicity: 1, approx: true });
        }
        for (const v of approxVals) {
            const f = (x, l) => { let s = x.toFixed(6).replace(/0+$/, '').replace(/\.$/, ''); if (s === '-0') s = '0'; return l === 'ru' ? s.replace('.', '{,}') : s; };
            v.tex = T((l) => `\\approx ${v.im === 0 ? f(v.re, l) : `${f(v.re, l)} ${v.im < 0 ? '-' : '+'} ${f(Math.abs(v.im), l)}\\,i`}`);
            if (v.im === 0 && v.multiplicity === 1) v.vectorsApprox = [realNullVector(Af, v.re)];
            values.push(v);
        }
    }
    values.sort((a, b) => (a.im === 0) - (b.im === 0) === 0 ? a.re - b.re || a.im - b.im : a.im === 0 ? -1 : 1);
    const out = { charPoly: toPoly(coefs), coefs, values };
    if (!opts.steps) return out;

    const st = [];
    const cp = matCharPoly(A, { steps: true });
    st.push(S(L('Характеристический многочлен', 'The characteristic polynomial'), T((l) => `\\det(A - \\lambda ${E_(l)}) = ${cp.tex}`),
        L('Собственные значения — корни уравнения det(A − λE) = 0.', 'The eigenvalues are the roots of det(A − λI) = 0.'), { rule: 'charpoly', sub: cp.steps }));
    // factorised form
    const lead = ptrim(coefs)[ptrim(coefs).length - 1];
    const factors = [];
    for (const { root, mult } of roots) factors.push(`${root.isZero() ? '\\lambda' : `(\\lambda ${root.isNeg() ? '+' : '-'} ${qt(root.abs())})`}${mult > 1 ? `^{${mult}}` : ''}`);
    for (const { f, mult } of quads) factors.push(`(${ptex(f)})${mult > 1 ? `^{${mult}}` : ''}`);
    if (pdeg(R) >= 1) factors.push(`(${ptex(R.map((c) => c.div(R[R.length - 1])))})`);
    const lc = lead.div(quads.reduce((acc, { f, mult }) => acc.mul(f[2].pow(mult)), Q.ONE));
    const lcTex = lc.isOne() ? '' : lc.eq(Q.MINUS_ONE) ? '-' : qt(lc);
    const rootsText = roots.length
        ? L(`Рациональные корни ищем среди дробей p/q, где p делит свободный член, а q — старший коэффициент (теорема о рациональных корнях), и проверяем подстановкой. Нашлись: ${roots.map((r) => `${qs(r.root)}${r.mult > 1 ? ` (кратность ${r.mult})` : ''}`).join(', ')}.`,
            `Rational roots are among the fractions p/q with p dividing the constant term and q dividing the leading coefficient (the rational root theorem); we test them by substitution. Found: ${roots.map((r) => `${qs(r.root)}${r.mult > 1 ? ` (multiplicity ${r.mult})` : ''}`).join(', ')}.`)
        : L('Рациональных корней нет (проверили все кандидаты p/q по теореме о рациональных корнях).', 'There are no rational roots (all candidates p/q from the rational root theorem fail).');
    st.push(S(L('Раскладываем на множители', 'Factor'), `${lcTex}${factors.join('') || '1'} = 0`, rootsText, { rule: 'factor' }));
    for (const [qi, { f }] of quads.entries()) {
        const { D } = quadRoots(f);
        const entries = quadEntries[qi];
        st.push(S(L('Квадратный множитель', 'A quadratic factor'), `${ptex(f)} = 0:\\quad D = ${qt(D)},\\quad \\lambda = ${entries.map((e) => e.tex).join(',\\ ')}`,
            D.isNeg() ? L('Дискриминант отрицательный: эти собственные значения — комплексно сопряжённая пара.', 'The discriminant is negative: these eigenvalues are a complex-conjugate pair.')
                : L('Корни этого множителя иррациональны, записываем их через квадратный корень.', 'The roots of this factor are irrational; we write them with a square root.'),
            { rule: 'quadratic' }));
    }
    if (approxVals.length) {
        st.push(S(L('Приближённые корни', 'Approximate roots'), T((l) => approxVals.map((v) => `\\lambda ${pickTex(v.tex, l)}`).join(',\\quad ')),
            L(`Оставшийся множитель степени ${pdeg(R)} не раскладывается над рациональными числами, поэтому его корни находим численно (приближённо).`,
                `The remaining factor of degree ${pdeg(R)} does not split over the rationals, so its roots are found numerically (approximately).`),
            { rule: 'numeric-roots' }));
    }
    st.push(...vecSteps);
    st.push(S(L('Ответ', 'Answer'), T((l) => values.map((v, k) => `\\lambda_{${k + 1}} ${v.approx ? pickTex(v.tex, l) : `= ${v.tex}`}${v.multiplicity > 1 ? `\\ (\\times ${v.multiplicity})` : ''}`).join(',\\quad ')),
        L(`Сумма собственных значений (с кратностями) равна следу ${qs(A.trace())}, произведение — определителю ${qs(matDet(A))}.`,
            `The eigenvalues (with multiplicity) add up to the trace ${qs(A.trace())} and multiply to the determinant ${qs(matDet(A))}.`),
        { rule: 'answer' }));
    out.steps = st;
    return out;
}
const pickTex = (t, l) => (typeof t === 'string' ? t : t[l]);

/**
 * Diagonalisation over Q: A = P·D·P⁻¹ → {diagonalizable: true, P, D, Pinv} or
 * {diagonalizable: false, reason: 'defective' | 'irrational', …}. {steps: true} adds steps.
 */
export function matDiagonalize(A, opts = {}) {
    A = M(A);
    needSquare(A, L('Диагонализация', 'Diagonalisation'));
    const n = A.rows;
    const e = matEigen(A, { steps: !!opts.steps });
    const st = opts.steps ? [S(L('Собственные значения и векторы', 'Eigenvalues and eigenvectors'), null, null, { rule: 'eigen', sub: e.steps })] : [];
    const fin = (res) => { if (opts.steps) res.steps = st; return res; };
    if (e.values.some((v) => v.kind !== 'rational')) {
        const allReal = e.values.every((v) => v.im === 0);
        const distinct = e.values.every((v) => v.multiplicity === 1);
        if (opts.steps) {
            st.push(S(L('Над ℚ не диагонализуется', 'Not diagonalisable over ℚ'), null,
                distinct ? L(`Не все собственные значения рациональны. Они различны, поэтому над ${allReal ? 'ℝ' : 'ℂ'} матрица диагонализуема, но матрица P будет содержать иррациональные ${allReal ? '' : 'или комплексные '}числа.`,
                    `Not all eigenvalues are rational. They are distinct, so the matrix is diagonalisable over ${allReal ? 'ℝ' : 'ℂ'}, but P will contain irrational${allReal ? '' : ' or complex'} numbers.`)
                    : L('Не все собственные значения рациональны.', 'Not all eigenvalues are rational.'), { rule: 'answer' }));
        }
        return fin({ diagonalizable: false, reason: 'irrational', overReals: allReal && distinct, overComplex: distinct, eigen: e });
    }
    const total = e.values.reduce((s, v) => s + v.geometric, 0);
    if (total < n) {
        const bad = e.values.find((v) => v.geometric < v.multiplicity);
        if (opts.steps) {
            st.push(S(L('Собственных векторов не хватает', 'Not enough eigenvectors'), null,
                L(`У λ = ${qs(bad.value)} кратность ${bad.multiplicity}, а независимых собственных векторов ${bad.geometric}. Всего независимых векторов ${total} < ${n}, базиса из собственных векторов нет — матрица не диагонализуема (у неё жорданова клетка).`,
                    `λ = ${qs(bad.value)} has multiplicity ${bad.multiplicity} but only ${bad.geometric} independent eigenvector${bad.geometric === 1 ? '' : 's'}. There are ${total} < ${n} independent vectors in total, so no eigenbasis exists and the matrix is not diagonalisable (it has a Jordan block).`),
                { rule: 'answer' }));
        }
        return fin({ diagonalizable: false, reason: 'defective', eigen: e });
    }
    const cols = [], diag = [];
    for (const v of e.values) for (const vec of v.vectors) { cols.push(vec); diag.push(v.value); }
    const P = Matrix.fromColumns(cols), D = Matrix.diag(diag), Pinv = matInverse(P);
    if (opts.steps) {
        st.push(S(L('Матрицы P и D', 'The matrices P and D'), `P = ${P.toTex()},\\quad D = ${D.toTex()},\\quad A = P D P^{-1}`,
            L('Столбцы P — собственные векторы, на диагонали D — соответствующие собственные значения (в том же порядке). В базисе из собственных векторов матрица A действует просто растяжением вдоль каждого вектора.',
                'The columns of P are eigenvectors, and the diagonal of D holds the matching eigenvalues (in the same order). In the eigenbasis A simply stretches along each vector.'),
            { rule: 'answer' }));
        st.push(S(L('Проверка', 'Check'), `P^{-1} A P = ${Pinv.mul(A).mul(P).toTex()} = D`, null, { rule: 'check' }));
    }
    return fin({ diagonalizable: true, P, D, Pinv, eigen: e });
}

/** Aⁿ exactly by repeated squaring (n < 0 uses the inverse; throws for a singular A). */
export function matPower(A, n) {
    A = M(A);
    needSquare(A, L('Степень матрицы', 'A matrix power'));
    let N = BigInt(n);
    let base = A;
    if (N < 0n) {
        base = matInverse(A);
        if (!base) throw fail('Матрица вырожденная: отрицательной степени нет.', 'The matrix is singular: negative powers do not exist.', 'singular');
        N = -N;
    }
    let result = Matrix.identity(A.rows);
    while (N > 0n) {
        if (N & 1n) result = result.mul(base);
        N >>= 1n;
        if (N) base = base.mul(base);
    }
    return result;
}
