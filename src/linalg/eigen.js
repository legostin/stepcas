// linalg/eigen — the characteristic polynomial, eigenvalues and eigenvectors, diagonalisation, powers.

import { Q } from '../core/rational.js';
import { numPolyRoots } from '../numbers/numeric/index.js';
import { E_, fail, qs, qt, qtp, shiftTex } from './common.js';
import { M, Matrix, needSquare, vecTex } from './core.js';
import { matDet } from './det.js';
import { fmatSvd } from './float.js';
import { intPrimitive, padd, pdeg, pdiv, pmul, psub, ptex, ptrim, quadFactor, quadRoots, rationalRootsQ, surdTex, toPoly } from './qpoly.js';
import { nullspaceFrom, reduce } from './reduce.js';
import { PARAMS, matInverse } from './systems.js';
import { msg, eachLanguage, decimalIn } from '../i18n/index.js';
import { step } from '../core/steps.js';

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
        c[n - k] = A.mul(Mk)
            .trace()
            .neg()
            .div(new Q(BigInt(k)));
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
    needSquare(A, msg('linalg.eigen.characteristic_polynomial'));
    const n = A.rows;
    const coefs = charCoefs(A);
    const value = toPoly(coefs);
    if (!opts.steps) return value;
    const tex = ptex(coefs);
    const st = [];
    const P = A.a.map((r, i) => r.map((v, j) => (i === j ? [v, Q.MINUS_ONE] : [v])));
    const shifted = `\\begin{vmatrix} ${P.map((r) => r.map(entryPolyTex).join(' & ')).join(' \\\\ ')} \\end{vmatrix}`;
    st.push(
        step({
            title: msg('linalg.eigen.what_we_look_for'),
            tex: eachLanguage((l) => `\\det(A - \\lambda ${E_(l)}) = ${shifted}`),
            text: msg('linalg.eigen.eigenvalue_is_number_with_v_v'),
            rule: 'charpoly-def',
        }),
    );
    if (n === 2) {
        const [[a, b], [c, d]] = A.a;
        st.push(
            step({
                title: msg('linalg.eigen.expand_2_2_determinant'),
                tex: `(${entryPolyTex(P[0][0])})(${entryPolyTex(P[1][1])}) - ${qtp(b)} \\cdot ${qtp(c)} = ${tex}`,
                text: msg('linalg.eigen.check_coefficient_of_is_minus_trace', { p: qs(a.add(d)), p2: qs(a.mul(d).sub(b.mul(c))) }),
                rule: 'charpoly-2x2',
            }),
        );
    } else if (n === 3) {
        const terms = [0, 1, 2]
            .map((j) => {
                const minor = P.slice(1).map((r) => r.filter((_, c) => c !== j));
                return { j, e: P[0][j], minor, det: detPolyMatrix(minor) };
            })
            .filter((t) => pdeg(t.e) >= 0 && !(t.e.length === 1 && t.e[0].isZero()));
        const signed = (t) => (t.j % 2 ? t.e[0].neg() : t.e[0]);
        const lead = (t, k) => {
            if (t.j === 0) return `${k ? '+ ' : ''}(${entryPolyTex(t.e)})`;
            const c = signed(t);
            const a = c.abs();
            return `${c.isNeg() ? '-' : k ? '+' : ''} ${a.isOne() ? '' : qt(a)}`;
        };
        const expTex = terms
            .map((t, k) => {
                const mt = `\\begin{vmatrix} ${t.minor.map((r) => r.map(entryPolyTex).join(' & ')).join(' \\\\ ')} \\end{vmatrix}`;
                return `${lead(t, k)} ${mt}`;
            })
            .join(' ');
        st.push(
            step({ title: msg('linalg.eigen.expand_along_first_row'), tex: expTex, text: msg('linalg.eigen.each_entry_of_first_row_is'), rule: 'cofactor' }),
        );
        st.push(
            step({
                title: msg('linalg.eigen.multiply_out'),
                tex: terms.map((t, k) => `${lead(t, k)}\\left(${ptex(t.det)}\\right)`).join(' ') + ` = ${tex}`,
                text: msg('linalg.eigen.check_coefficient_of_is_trace_constant', { p: qs(A.trace()), p2: qs(coefs[0]) }),
                rule: 'charpoly-3x3',
            }),
        );
    } else {
        st.push(
            step({
                title: msg('linalg.eigen.faddeev_leverrier_method'),
                tex: eachLanguage((l) => `\\det(A - \\lambda ${E_(l)}) = ${tex}`),
                text: msg('linalg.eigen.for_bigger_matrices_expanding_determinant_is'),
                rule: 'faddeev-leverrier',
            }),
        );
    }
    st.push(step({ title: msg('linalg.eigen.characteristic_polynomial'), tex: eachLanguage((l) => `\\det(A - \\lambda ${E_(l)}) = ${tex}`), rule: 'answer' }));
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
    needSquare(A, msg('linalg.eigen.eigenvalues'));
    const n = A.rows;
    const coefs = charCoefs(A);
    const { roots, rest } = rationalRootsQ(coefs);
    const values = [];
    const vecSteps = [];
    for (const { root, mult } of roots) {
        const B = A.sub(Matrix.identity(n).scale(root));
        const red = reduce(B.a, { steps: !!opts.steps });
        const vectors = nullspaceFrom(red.W, red.pivots, n, true);
        values.push({
            kind: 'rational',
            value: root,
            re: root.toNumber(),
            im: 0,
            multiplicity: mult,
            geometric: vectors.length,
            vectors,
            tex: qt(root),
            approx: false,
        });
        if (opts.steps) {
            const general =
                vectors.length === 1
                    ? `\\mathbf v = t${vecTex(vectors[0])}`
                    : `\\mathbf v = ${vectors.map((v, k) => `${PARAMS[k] ?? `t_{${k + 1}}`}${vecTex(v)}`).join(' + ')}`;
            vecSteps.push(
                step({
                    title: msg('linalg.eigen.eigenvectors_for', { root: qs(root) }),
                    tex: eachLanguage(
                        (l) => `${root.isZero() ? 'A' : `(${shiftTex(root, l)})`}\\mathbf v = 0:\\quad ${B.toTex()} \\;\\Rightarrow\\; ${general}`,
                    ),
                    text: msg('linalg.eigen.we_solve_homogeneous_system_i_v', {
                        p: (lng) =>
                            vectors.length === 1
                                ? msg('linalg.eigen.one_free_unknown_eigenvectors_lie_on').in(lng)
                                : msg('linalg.eigen.free_unknowns_eigenvectors_fill_space_of', { length: vectors.length }).in(lng),
                        p2: (lng) =>
                            vectors.length < mult ? msg('linalg.eigen.root_has_multiplicity_but_there_are', { mult, length: vectors.length }).in(lng) : '',
                    }),
                    rule: 'eigenvectors',
                    sub: red.steps,
                }),
            );
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
            if (same) {
                same.multiplicity++;
                continue;
            }
            approxVals.push({ kind: 'approx', re: z.re, im: z.im, multiplicity: 1, approx: true });
        }
        for (const v of approxVals) {
            const f = (x, l) => {
                let s = x.toFixed(6).replace(/0+$/, '').replace(/\.$/, '');
                if (s === '-0') s = '0';
                return decimalIn(s, l);
            };
            v.tex = eachLanguage((l) => `\\approx ${v.im === 0 ? f(v.re, l) : `${f(v.re, l)} ${v.im < 0 ? '-' : '+'} ${f(Math.abs(v.im), l)}\\,i`}`);
            if (v.im === 0 && v.multiplicity === 1) v.vectorsApprox = [realNullVector(Af, v.re)];
            values.push(v);
        }
    }
    values.sort((a, b) => ((a.im === 0) - (b.im === 0) === 0 ? a.re - b.re || a.im - b.im : a.im === 0 ? -1 : 1));
    const out = { charPoly: toPoly(coefs), coefs, values };
    if (!opts.steps) return out;

    const st = [];
    const cp = matCharPoly(A, { steps: true });
    st.push(
        step({
            title: msg('linalg.eigen.characteristic_polynomial'),
            tex: eachLanguage((l) => `\\det(A - \\lambda ${E_(l)}) = ${cp.tex}`),
            text: msg('linalg.eigen.eigenvalues_are_roots_of_det_i'),
            rule: 'charpoly',
            sub: cp.steps,
        }),
    );
    // factorised form
    const lead = ptrim(coefs)[ptrim(coefs).length - 1];
    const factors = [];
    for (const { root, mult } of roots)
        factors.push(`${root.isZero() ? '\\lambda' : `(\\lambda ${root.isNeg() ? '+' : '-'} ${qt(root.abs())})`}${mult > 1 ? `^{${mult}}` : ''}`);
    for (const { f, mult } of quads) factors.push(`(${ptex(f)})${mult > 1 ? `^{${mult}}` : ''}`);
    if (pdeg(R) >= 1) factors.push(`(${ptex(R.map((c) => c.div(R[R.length - 1])))})`);
    const lc = lead.div(quads.reduce((acc, { f, mult }) => acc.mul(f[2].pow(mult)), Q.ONE));
    const lcTex = lc.isOne() ? '' : lc.eq(Q.MINUS_ONE) ? '-' : qt(lc);
    const rootsText = roots.length
        ? msg('linalg.eigen.rational_roots_are_among_fractions_p', {
              p: (lng) => roots.map((r) => `${qs(r.root)}${r.mult > 1 ? msg('linalg.eigen.multiplicity', { mult: r.mult }).in(lng) : ''}`).join(', '),
          })
        : msg('linalg.eigen.there_are_no_rational_roots_all');
    st.push(step({ title: msg('linalg.eigen.factor'), tex: `${lcTex}${factors.join('') || '1'} = 0`, text: rootsText, rule: 'factor' }));
    for (const [qi, { f }] of quads.entries()) {
        const { D } = quadRoots(f);
        const entries = quadEntries[qi];
        st.push(
            step({
                title: msg('linalg.eigen.quadratic_factor'),
                tex: `${ptex(f)} = 0:\\quad D = ${qt(D)},\\quad \\lambda = ${entries.map((e) => e.tex).join(',\\ ')}`,
                text: D.isNeg() ? msg('linalg.eigen.discriminant_is_negative_these_eigenvalues_are') : msg('linalg.eigen.roots_of_this_factor_are_irrational'),
                rule: 'quadratic',
            }),
        );
    }
    if (approxVals.length) {
        st.push(
            step({
                title: msg('linalg.eigen.approximate_roots'),
                tex: eachLanguage((l) => approxVals.map((v) => `\\lambda ${pickTex(v.tex, l)}`).join(',\\quad ')),
                text: msg('linalg.eigen.remaining_factor_of_degree_does_not', { R: pdeg(R) }),
                rule: 'numeric-roots',
            }),
        );
    }
    st.push(...vecSteps);
    st.push(
        step({
            title: msg('linalg.eigen.answer'),
            tex: eachLanguage((l) =>
                values
                    .map(
                        (v, k) =>
                            `\\lambda_{${k + 1}} ${v.approx ? pickTex(v.tex, l) : `= ${v.tex}`}${v.multiplicity > 1 ? `\\ (\\times ${v.multiplicity})` : ''}`,
                    )
                    .join(',\\quad '),
            ),
            text: msg('linalg.eigen.eigenvalues_with_multiplicity_add_up_to', { p: qs(A.trace()), p2: qs(matDet(A)) }),
            rule: 'answer',
        }),
    );
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
    needSquare(A, msg('linalg.eigen.diagonalisation'));
    const n = A.rows;
    const e = matEigen(A, { steps: !!opts.steps });
    const st = opts.steps ? [step({ title: msg('linalg.eigen.eigenvalues_and_eigenvectors'), rule: 'eigen', sub: e.steps })] : [];
    const fin = (res) => {
        if (opts.steps) res.steps = st;
        return res;
    };
    if (e.values.some((v) => v.kind !== 'rational')) {
        const allReal = e.values.every((v) => v.im === 0);
        const distinct = e.values.every((v) => v.multiplicity === 1);
        if (opts.steps) {
            st.push(
                step({
                    title: msg('linalg.eigen.not_diagonalisable_over'),
                    text: distinct
                        ? msg('linalg.eigen.not_all_eigenvalues_are_rational_they', {
                              p: allReal ? 'ℝ' : 'ℂ',
                              p2: (lng) => (allReal ? '' : msg('linalg.eigen.or_complex').in(lng)),
                          })
                        : msg('linalg.eigen.not_all_eigenvalues_are_rational'),
                    rule: 'answer',
                }),
            );
        }
        return fin({ diagonalizable: false, reason: 'irrational', overReals: allReal && distinct, overComplex: distinct, eigen: e });
    }
    const total = e.values.reduce((s, v) => s + v.geometric, 0);
    if (total < n) {
        const bad = e.values.find((v) => v.geometric < v.multiplicity);
        if (opts.steps) {
            st.push(
                step({
                    title: msg('linalg.eigen.not_enough_eigenvectors'),
                    text: msg('linalg.eigen.has_multiplicity_but_only_independent_eigenvector', {
                        p: qs(bad.value),
                        multiplicity: bad.multiplicity,
                        geometric: bad.geometric,
                        total,
                        n,
                    }),
                    rule: 'answer',
                }),
            );
        }
        return fin({ diagonalizable: false, reason: 'defective', eigen: e });
    }
    const cols = [],
        diag = [];
    for (const v of e.values)
        for (const vec of v.vectors) {
            cols.push(vec);
            diag.push(v.value);
        }
    const P = Matrix.fromColumns(cols),
        D = Matrix.diag(diag),
        Pinv = matInverse(P);
    if (opts.steps) {
        st.push(
            step({
                title: msg('linalg.eigen.matrices_p_and_d'),
                tex: `P = ${P.toTex()},\\quad D = ${D.toTex()},\\quad A = P D P^{-1}`,
                text: msg('linalg.eigen.columns_of_p_are_eigenvectors_and'),
                rule: 'answer',
            }),
        );
        st.push(step({ title: msg('linalg.eigen.check'), tex: `P^{-1} A P = ${Pinv.mul(A).mul(P).toTex()} = D`, rule: 'check' }));
    }
    return fin({ diagonalizable: true, P, D, Pinv, eigen: e });
}

/** Aⁿ exactly by repeated squaring (n < 0 uses the inverse; throws for a singular A). */
export function matPower(A, n) {
    A = M(A);
    needSquare(A, msg('linalg.eigen.matrix_power'));
    let N = BigInt(n);
    let base = A;
    if (N < 0n) {
        base = matInverse(A);
        if (!base) throw fail(msg('linalg.eigen.matrix_is_singular_negative_powers_do'), 'singular');
        N = -N;
    }
    return base.pow(N);
}
