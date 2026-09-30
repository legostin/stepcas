// linalg/orthogonal — Gram–Schmidt, projections and least squares.

import { Q } from '../core/rational.js';
import { L, S, fail, qt, sub } from './common.js';
import { M, Matrix, toQ, vecTex } from './core.js';
import { matSolve } from './systems.js';

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
                st.push(S(L(`Вектор ${k + 1} — лишний`, `Vector ${k + 1} is dependent`), null,
                    L(`После вычитания проекций остался нулевой вектор: v${sub(k + 1)} — линейная комбинация предыдущих. Пропускаем его.`,
                        `Subtracting the projections leaves the zero vector: v${sub(k + 1)} is a combination of the previous ones. We skip it.`),
                    { rule: 'dependent' }));
            }
            return;
        }
        us.push(u);
        if (opts.steps) {
            const j = us.length;
            const proj = parts.map(({ c }, i) => `${c.isNeg() ? '+' : '-'} ${c.abs().isOne() ? '' : qt(c.abs())}\\mathbf u_{${i + 1}}`).join(' ');
            st.push(S(L(`Вектор u${sub(j)}`, `Vector u${sub(j)}`),
                `\\mathbf u_{${j}} = \\mathbf v_{${k + 1}} ${parts.length ? proj : ''} = ${vt(u)}`,
                parts.length ? L(`Из v${sub(k + 1)} вычитаем его проекции на уже построенные векторы: коэффициент проекции на u равен (v·u)/(u·u). Остаток перпендикулярен всем предыдущим.`,
                    `From v${sub(k + 1)} we subtract its projections onto the vectors built so far: the coefficient for u is (v·u)/(u·u). What remains is perpendicular to all of them.`)
                    : L('Первый вектор берём как есть.', 'The first vector is taken as it is.'),
                { rule: 'gram-schmidt' }));
        }
    });
    const normalized = us.map((u) => { const f = u.map((x) => x.toNumber()); const n = Math.hypot(...f); return f.map((x) => x / n); });
    const res = { orthogonal: us, normalized, dropped };
    if (opts.steps) {
        st.push(S(L('Нормируем', 'Normalise'), us.map((u, i) => `\\|\\mathbf u_{${i + 1}}\\| = \\sqrt{${qt(dot(u, u))}}`).join(',\\quad '),
            L('Чтобы получить ортонормированный базис, делим каждый вектор на его длину (обычно это корень — поэтому точные векторы оставляем ненормированными).',
                'For an orthonormal basis divide each vector by its length (usually a square root, which is why the exact vectors are left unnormalised).'),
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
    if (sol.kind === 'none') throw fail('Не удалось найти проекцию.', 'Could not find the projection.', 'degenerate');
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
            S(L('Нормальные уравнения', 'The normal equations'), `A^{\\mathsf T}A\\,\\mathbf x = A^{\\mathsf T}\\mathbf b:\\quad ${N.toTex()}\\mathbf x = ${vecTex(rhs)}`,
                L('Точного решения нет (уравнений больше, чем неизвестных), поэтому ищем x, при котором вектор ошибок Ax − b самый короткий. Он должен быть перпендикулярен столбцам A — отсюда AᵀA·x = Aᵀb.',
                    'There is no exact solution (more equations than unknowns), so we look for the x that makes the error vector Ax − b as short as possible. It must be perpendicular to the columns of A, which gives AᵀA·x = Aᵀb.'),
                { rule: 'normal-equations' }),
            S(L('Решаем', 'Solve'), sol.tex, null, { rule: 'answer', sub: sol.steps }),
        ];
    }
    return res;
}
