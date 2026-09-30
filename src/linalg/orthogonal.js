// linalg/orthogonal — Gram–Schmidt, projections and least squares.

import { Q } from '../core/rational.js';
import { S, fail, qt, sub } from './common.js';
import { M, Matrix, toQ, vecTex } from './core.js';
import { matSolve } from './systems.js';
import { msg } from '../i18n/index.js';

// ---------------------------------------------------------------- orthogonality

const dot = (u, v) => u.reduce((s, x, i) => s.add(x.mul(v[i])), Q.ZERO);

/**
 * Gram–Schmidt over Q: {orthogonal: Q[][] (exact, not normalised — norms are square roots),
 * normalized: number[][] (unit vectors in floats), dropped: indices of dependent vectors, steps?}.
 */
export function matGramSchmidt(vectors, opts = {}) {
    const vs = vectors.map((v) => v.map(toQ));
    const us = [], dropped = [], st = [];
    const vt = (v) => vecTex(v);
    vs.forEach((v, k) => {
        let u = v.slice();
        const parts = [];
        for (const w of us) {
            const c = dot(v, w).div(dot(w, w));
            if (!c.isZero()) u = u.map((x, i) => x.sub(c.mul(w[i])));
            parts.push({ c, w });
        }
        if (u.every((x) => x.isZero())) {
            dropped.push(k);
            if (opts.steps) {
                st.push(S(msg('linalg.orthogonal.vector_is_dependent', { p: k + 1 }), null,
                    msg('linalg.orthogonal.subtracting_projections_leaves_zero_vector_v', { p: sub(k + 1) }),
                    { rule: 'dependent' }));
            }
            return;
        }
        us.push(u);
        if (opts.steps) {
            const j = us.length;
            const proj = parts.map(({ c }, i) => `${c.isNeg() ? '+' : '-'} ${c.abs().isOne() ? '' : qt(c.abs())}\\mathbf u_{${i + 1}}`).join(' ');
            st.push(S(msg('linalg.orthogonal.vector_u', { j: sub(j) }),
                `\\mathbf u_{${j}} = \\mathbf v_{${k + 1}} ${parts.length ? proj : ''} = ${vt(u)}`,
                parts.length ? msg('linalg.orthogonal.from_v_we_subtract_its_projections', { p: sub(k + 1) })
                    : msg('linalg.orthogonal.first_vector_is_taken_as_it'),
                { rule: 'gram-schmidt' }));
        }
    });
    const normalized = us.map((u) => { const f = u.map((x) => x.toNumber()); const n = Math.hypot(...f); return f.map((x) => x / n); });
    const res = { orthogonal: us, normalized, dropped };
    if (opts.steps) {
        st.push(S(msg('linalg.orthogonal.normalise'), us.map((u, i) => `\\|\\mathbf u_{${i + 1}}\\| = \\sqrt{${qt(dot(u, u))}}`).join(',\\quad '),
            msg('linalg.orthogonal.for_orthonormal_basis_divide_each_vector'),
            { rule: 'normalize' }));
        res.steps = st;
    }
    return res;
}

/** Orthogonal projection of v onto a vector or onto the span of several vectors (exact) → Q[]. */
export function matProjection(v, onto) {
    const vv = v.map(toQ);
    const basis = Array.isArray(onto[0]) ? onto.map((u) => u.map(toQ)) : [onto.map(toQ)];
    const A = Matrix.fromColumns(basis);
    const At = A.transpose();
    const sol = matSolve(At.mul(A), At.mul(vv));
    if (sol.kind === 'none') throw fail(msg('linalg.orthogonal.could_not_find_projection'), 'degenerate');
    return A.mul(sol.x);
}

/**
 * Least squares for an overdetermined system: solves the normal equations AᵀA·x = Aᵀb exactly →
 * {kind, x, params, basis, residual: Q[], steps?}.
 */
export function matLeastSquares(A, b, opts = {}) {
    A = M(A);
    const bv = b.map((v) => toQ(Array.isArray(v) ? v[0] : v));
    const At = A.transpose();
    const N = At.mul(A), rhs = At.mul(bv);
    const sol = matSolve(N, rhs, { steps: !!opts.steps, vars: opts.vars });
    const res = { ...sol };
    delete res.steps;
    if (sol.x) res.residual = A.mul(sol.x).map((v, i) => bv[i].sub(v));
    if (opts.steps) {
        res.steps = [
            S(msg('linalg.orthogonal.normal_equations'), `A^{\\mathsf T}A\\,\\mathbf x = A^{\\mathsf T}\\mathbf b:\\quad ${N.toTex()}\\mathbf x = ${vecTex(rhs)}`,
                msg('linalg.orthogonal.there_is_no_exact_solution_more'),
                { rule: 'normal-equations' }),
            S(msg('linalg.orthogonal.solve'), sol.tex, null, { rule: 'answer', sub: sol.steps }),
        ];
    }
    return res;
}
