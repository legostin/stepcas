// linalg/float — the float toolkit on number[][]: products, solving, eigenvalues of symmetric matrices, SVD, QR.

// ---------------------------------------------------------------- float toolkit (number[][])

/** Product of float matrices (or matrix × vector). */
export function fmatMul(A, B) {
    if (!Array.isArray(B[0]) && !ArrayBuffer.isView(B[0])) return A.map((r) => r.reduce((s, x, j) => s + x * B[j], 0));
    const m = A.length,
        n = B[0].length,
        p = B.length;
    const out = Array.from({ length: m }, () => new Array(n).fill(0));
    for (let i = 0; i < m; i++) {
        const Ai = A[i],
            Oi = out[i];
        for (let k = 0; k < p; k++) {
            const a = Ai[k];
            if (a === 0) continue;
            const Bk = B[k];
            for (let j = 0; j < n; j++) Oi[j] += a * Bk[j];
        }
    }
    return out;
}

/** Transpose of a float matrix. */
export function fmatTranspose(A) {
    return A[0].map((_, j) => A.map((r) => r[j]));
}

/** Solve A·x = b (partial pivoting); null for a (numerically) singular A. b may be a vector or a matrix. */
export function fmatSolve(A, b) {
    const n = A.length;
    const multi = Array.isArray(b[0]) || ArrayBuffer.isView(b[0]);
    const W = A.map((r, i) => [...r, ...(multi ? b[i] : [b[i]])]);
    const w = W[0].length;
    const scale = Math.max(...A.map((r) => Math.max(...r.map(Math.abs)))) || 1;
    for (let c = 0; c < n; c++) {
        let p = c;
        for (let i = c + 1; i < n; i++) if (Math.abs(W[i][c]) > Math.abs(W[p][c])) p = i;
        if (Math.abs(W[p][c]) <= 1e-13 * scale) return null;
        [W[c], W[p]] = [W[p], W[c]];
        for (let i = 0; i < n; i++) {
            if (i === c || W[i][c] === 0) continue;
            const f = W[i][c] / W[c][c];
            for (let j = c; j < w; j++) W[i][j] -= f * W[c][j];
        }
    }
    const X = W.map((r, i) => r.slice(n).map((v) => v / W[i][i]));
    return multi ? X : X.map((r) => r[0]);
}

/** Inverse of a float matrix (Gauss–Jordan with partial pivoting); null if singular. */
export function fmatInv(A) {
    const n = A.length;
    return fmatSolve(
        A,
        Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 1 : 0))),
    );
}

/**
 * Symmetric eigenproblem by cyclic Jacobi rotations → {values (descending), vectors: vectors[k] is the
 * unit eigenvector for values[k]}.
 */
export function fmatEigSym(A, opts = {}) {
    const n = A.length;
    const a = A.map((r) => Array.from(r));
    const V = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 1 : 0)));
    const maxSweeps = opts.maxSweeps ?? 100;
    for (let sweep = 0; sweep < maxSweeps; sweep++) {
        let off = 0,
            diag = 0;
        for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) i === j ? (diag += a[i][j] ** 2) : (off += a[i][j] ** 2);
        if (off <= 1e-30 * Math.max(diag, 1e-300)) break;
        for (let p = 0; p < n - 1; p++) {
            for (let q = p + 1; q < n; q++) {
                if (Math.abs(a[p][q]) < 1e-300) continue;
                const theta = (a[q][q] - a[p][p]) / (2 * a[p][q]);
                const t = (theta >= 0 ? 1 : -1) / (Math.abs(theta) + Math.sqrt(theta * theta + 1));
                const c = 1 / Math.sqrt(t * t + 1),
                    s = t * c;
                for (let k = 0; k < n; k++) {
                    const akp = a[k][p],
                        akq = a[k][q];
                    a[k][p] = c * akp - s * akq;
                    a[k][q] = s * akp + c * akq;
                }
                for (let k = 0; k < n; k++) {
                    const apk = a[p][k],
                        aqk = a[q][k];
                    a[p][k] = c * apk - s * aqk;
                    a[q][k] = s * apk + c * aqk;
                }
                for (let k = 0; k < n; k++) {
                    const vkp = V[k][p],
                        vkq = V[k][q];
                    V[k][p] = c * vkp - s * vkq;
                    V[k][q] = s * vkp + c * vkq;
                }
            }
        }
    }
    const order = Array.from({ length: n }, (_, i) => i).sort((i, j) => a[j][j] - a[i][i]);
    return { values: order.map((i) => a[i][i]), vectors: order.map((i) => V.map((r) => r[i])) };
}

/** One-sided Jacobi SVD on columns (Float64Array each) of an m×n matrix, m ≥ n. */
function jacobiSvdCols(cols, m, sweepsMax = 60) {
    const n = cols.length;
    const V = Array.from({ length: n }, (_, i) => {
        const v = new Float64Array(n);
        v[i] = 1;
        return v;
    });
    for (let sweep = 0; sweep < sweepsMax; sweep++) {
        let rotated = false;
        for (let p = 0; p < n - 1; p++) {
            const up = cols[p];
            for (let q = p + 1; q < n; q++) {
                const uq = cols[q];
                let alpha = 0,
                    beta = 0,
                    gamma = 0;
                for (let i = 0; i < m; i++) {
                    alpha += up[i] * up[i];
                    beta += uq[i] * uq[i];
                    gamma += up[i] * uq[i];
                }
                if (gamma === 0 || Math.abs(gamma) <= 1e-15 * Math.sqrt(alpha * beta)) continue;
                rotated = true;
                const zeta = (beta - alpha) / (2 * gamma);
                const t = (zeta >= 0 ? 1 : -1) / (Math.abs(zeta) + Math.sqrt(1 + zeta * zeta));
                const c = 1 / Math.sqrt(1 + t * t),
                    s = c * t;
                for (let i = 0; i < m; i++) {
                    const x = up[i],
                        y = uq[i];
                    up[i] = c * x - s * y;
                    uq[i] = s * x + c * y;
                }
                const vp = V[p],
                    vq = V[q];
                for (let i = 0; i < n; i++) {
                    const x = vp[i],
                        y = vq[i];
                    vp[i] = c * x - s * y;
                    vq[i] = s * x + c * y;
                }
            }
        }
        if (!rotated) break;
    }
    const sv = cols.map((c) => Math.sqrt(c.reduce((s, x) => s + x * x, 0)));
    const order = Array.from({ length: n }, (_, i) => i).sort((i, j) => sv[j] - sv[i]);
    return {
        S: order.map((i) => sv[i]),
        Ucols: order.map((i) => (sv[i] > 0 ? cols[i].map((x) => x / sv[i]) : cols[i])),
        Vcols: order.map((i) => V[i]),
    };
}
const colsToRows = (cols, m) => Array.from({ length: m }, (_, i) => cols.map((c) => c[i]));

/** Thin SVD A = U·diag(S)·Vᵀ (one-sided Jacobi, accurate; fine up to ~200×200) → {U (m×r rows), S, V (n×r rows)}. */
export function fmatSvd(A) {
    const m = A.length,
        n = A[0].length;
    if (m < n) {
        const t = fmatSvd(fmatTranspose(A));
        return { U: t.V, S: t.S, V: t.U };
    }
    const cols = Array.from({ length: n }, (_, j) => Float64Array.from(A, (r) => r[j]));
    const { S: s, Ucols, Vcols } = jacobiSvdCols(cols, m);
    return { U: colsToRows(Ucols, m), S: s, V: colsToRows(Vcols, n) };
}

function orthonormalize(cols, m) {
    // modified Gram–Schmidt, twice for stability; drops (numerically) dependent columns
    const out = [];
    for (const c0 of cols) {
        const c = Float64Array.from(c0);
        for (let pass = 0; pass < 2; pass++) {
            for (const q of out) {
                let d = 0;
                for (let i = 0; i < m; i++) d += q[i] * c[i];
                for (let i = 0; i < m; i++) c[i] -= d * q[i];
            }
        }
        const nrm = Math.sqrt(c.reduce((s, x) => s + x * x, 0));
        if (nrm > 1e-12) out.push(c.map((x) => x / nrm));
    }
    return out;
}

/**
 * Randomised truncated SVD (Halko–Martinsson–Tropp) for image compression and the like:
 * the k largest singular triplets of an m×n matrix → {U (m×k rows), S (k), V (n×k rows)}.
 * {oversample = 10, powerIters = 2, seed = 1}.
 */
export function fmatSvdTruncated(A, k, opts = {}) {
    const m = A.length,
        n = A[0].length;
    const l = Math.min(n, m, k + (opts.oversample ?? 10));
    const q = opts.powerIters ?? 2;
    let seed = (opts.seed ?? 1) >>> 0 || 1;
    const rnd = () => {
        seed ^= seed << 13;
        seed >>>= 0;
        seed ^= seed >>> 17;
        seed ^= seed << 5;
        seed >>>= 0;
        return seed / 4294967296;
    };
    const gauss = () => {
        const u = rnd() || 1e-12,
            v = rnd();
        return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
    };
    const Af = A.map((r) => Float64Array.from(r));
    const mulA = (cols) =>
        cols.map((c) => {
            const y = new Float64Array(m);
            for (let i = 0; i < m; i++) {
                const r = Af[i];
                let s = 0;
                for (let j = 0; j < n; j++) s += r[j] * c[j];
                y[i] = s;
            }
            return y;
        });
    const mulAt = (cols) =>
        cols.map((c) => {
            const y = new Float64Array(n);
            for (let i = 0; i < m; i++) {
                const r = Af[i],
                    ci = c[i];
                if (ci === 0) continue;
                for (let j = 0; j < n; j++) y[j] += r[j] * ci;
            }
            return y;
        });
    let Qc = orthonormalize(mulA(Array.from({ length: l }, () => Float64Array.from({ length: n }, gauss))), m);
    for (let it = 0; it < q; it++) {
        const Z = orthonormalize(mulAt(Qc), n);
        Qc = orthonormalize(mulA(Z), m);
    }
    // B = Qᵀ A (l × n); SVD of Bᵀ (n × l): Bᵀ = U'·S·V'ᵀ ⇒ B = V'·S·U'ᵀ
    const Bt = mulAt(Qc); // columns: Aᵀ q_i → the rows of B, i.e. the columns of Bᵀ
    const {
        S: s,
        Ucols,
        Vcols,
    } = jacobiSvdCols(
        Bt.map((c) => Float64Array.from(c)),
        n,
    );
    const kk = Math.min(k, s.length);
    const Ucols2 = Vcols.slice(0, kk).map((v) => {
        const u = new Float64Array(m);
        v.forEach((w, i) => {
            const qi = Qc[i];
            for (let r = 0; r < m; r++) u[r] += w * qi[r];
        });
        return u;
    });
    return { U: colsToRows(Ucols2, m), S: s.slice(0, kk), V: colsToRows(Ucols.slice(0, kk), n) };
}

/** Rebuild the rank-k approximation U·diag(S)·Vᵀ (k defaults to all) → m×n number[][]. */
export function fmatLowRank(svd, k = svd.S.length) {
    const m = svd.U.length,
        n = svd.V.length;
    const out = Array.from({ length: m }, () => new Array(n).fill(0));
    for (let t = 0; t < Math.min(k, svd.S.length); t++) {
        const s = svd.S[t];
        for (let i = 0; i < m; i++) {
            const u = svd.U[i][t] * s;
            if (u === 0) continue;
            const row = out[i];
            for (let j = 0; j < n; j++) row[j] += u * svd.V[j][t];
        }
    }
    return out;
}

/** Householder QR: A (m×n) = Q·R with Q m×r orthonormal columns and R r×n upper triangular, r = min(m, n). */
export function fmatQr(A) {
    const m = A.length,
        n = A[0].length,
        r = Math.min(m, n);
    const Rm = A.map((row) => Array.from(row));
    const vs = [];
    for (let k = 0; k < r; k++) {
        let norm = 0;
        for (let i = k; i < m; i++) norm += Rm[i][k] ** 2;
        norm = Math.sqrt(norm);
        const v = new Float64Array(m);
        if (norm === 0) {
            vs.push(null);
            continue;
        }
        const alpha = Rm[k][k] > 0 ? -norm : norm;
        for (let i = k; i < m; i++) v[i] = Rm[i][k];
        v[k] -= alpha;
        const vv = v.reduce((s, x) => s + x * x, 0);
        if (vv === 0) {
            vs.push(null);
            continue;
        }
        for (let j = k; j < n; j++) {
            let s = 0;
            for (let i = k; i < m; i++) s += v[i] * Rm[i][j];
            s = (2 * s) / vv;
            for (let i = k; i < m; i++) Rm[i][j] -= s * v[i];
        }
        vs.push({ v, vv });
    }
    // Q = H₁H₂…H_r applied to the first r columns of the identity
    const Qm = Array.from({ length: m }, (_, i) => Array.from({ length: r }, (_, j) => (i === j ? 1 : 0)));
    for (let k = r - 1; k >= 0; k--) {
        const h = vs[k];
        if (!h) continue;
        for (let j = 0; j < r; j++) {
            let s = 0;
            for (let i = k; i < m; i++) s += h.v[i] * Qm[i][j];
            s = (2 * s) / h.vv;
            for (let i = k; i < m; i++) Qm[i][j] -= s * h.v[i];
        }
    }
    const Rt = Rm.slice(0, r).map((row, i) => row.map((x, j) => (j < i ? 0 : x)));
    return { Q: Qm, R: Rt };
}
