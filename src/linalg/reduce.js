// linalg/reduce — row reduction (Gauss–Jordan) with every elementary operation explained; rank and null space.

import { Q, bigGcd } from '../core/rational.js';
import { R, S, qs, qt } from './common.js';
import { M, Matrix } from './core.js';
import { msg } from '../i18n/index.js';

// ---------------------------------------------------------------- row reduction

/**
 * Pivot choice (keeps the numbers small): an entry equal to 1, else −1; else an entry that divides its
 * whole row (dividing keeps integers); else the smallest |entry|. Ties keep the current row (no swap).
 */
function pickPivot(W, r, c, m) {
    let best = -1, bestKey = null;
    for (let i = r; i < m; i++) {
        const v = W[i][c];
        if (v.isZero()) continue;
        const cls = v.isOne() ? 0 : v.eq(Q.MINUS_ONE) ? 1 : W[i].every((x) => x.div(v).isInt()) ? 2 : 3;
        const key = [cls, cls >= 2 ? v.abs() : Q.ZERO, i === r ? 0 : 1, i];
        const better = !bestKey || key[0] < bestKey[0] || (key[0] === bestKey[0] && (key[1].lt(bestKey[1]) || (key[1].eq(bestKey[1]) && (key[2] < bestKey[2] || (key[2] === bestKey[2] && key[3] < bestKey[3])))));
        if (better) { best = i; bestKey = key; }
    }
    return best;
}

function opTex(op) {
    if (op.op === 'swap') return `${R(op.i)} \\leftrightarrow ${R(op.j)}`;
    if (op.op === 'scale') return op.k.eq(Q.MINUS_ONE) ? `${R(op.i)} \\to -${R(op.i)}` : `${R(op.i)} \\to ${qt(op.k)}\\,${R(op.i)}`;
    const a = op.k.abs();
    return `${R(op.i)} \\to ${R(op.i)} ${op.k.isNeg() ? '-' : '+'} ${a.isOne() ? '' : `${qt(a)}\\,`}${R(op.j)}`;
}
export function arrowLabel(op) {
    if (op.op === 'swap') return `${R(op.i)} \\leftrightarrow ${R(op.j)}`;
    if (op.op === 'scale') return op.k.eq(Q.MINUS_ONE) ? `-${R(op.i)}` : `${qt(op.k)}\\,${R(op.i)}`;
    const a = op.k.abs();
    return `${R(op.i)} ${op.k.isNeg() ? '-' : '+'} ${a.isOne() ? '' : `${qt(a)}\\,`}${R(op.j)}`;
}

export function opText(op, phase, why) {
    if (op.op === 'swap') {
        return why;
    }
    if (op.op === 'scale') {
        const p = op.pivot;
        if (p.eq(Q.MINUS_ONE)) return msg('linalg.reduce.multiply_row_by_1_so_that', { i: op.i + 1 });
        if (p.isInt()) return msg('linalg.reduce.divide_row_by_so_that_pivot', { i: op.i + 1, k: qs(p) });
        return msg('linalg.reduce.multiply_row_by_so_that_pivot', { i: op.i + 1, k: qs(op.k), pivot: qs(p) });
    }
    const a = op.k.abs();
    const times = a.isOne() ? '' : msg('linalg.reduce.times', { a: qs(a) });
    const where = phase === 'backward' ? msg('linalg.reduce.above') : msg('linalg.reduce.below');
    const rows = { target: op.i + 1, source: op.j + 1, times };
    const act = op.k.isNeg() ? msg('linalg.reduce.subtract_row_from_row', rows) : msg('linalg.reduce.add_row_to_row', rows);
    return msg('linalg.reduce.clear_entry_pivot', { where, act });
}

function applyOp(W, op) {
    if (op.op === 'swap') [W[op.i], W[op.j]] = [W[op.j], W[op.i]];
    else if (op.op === 'scale') W[op.i] = W[op.i].map((v) => v.mul(op.k));
    else W[op.i] = W[op.i].map((v, c) => v.add(op.k.mul(W[op.j][c])));
}

/**
 * Gauss–Jordan elimination on a copy of W (Q[][]). Pivots are searched only in the first
 * cols − augmented columns. Returns {W, pivots, ops, steps}.
 */
export function reduce(W0, { augmented = 0, steps = false, jordan = true, stopOnSingular = false } = {}) {
    const W = W0.map((r) => r.slice());
    const m = W.length, n = W[0].length, lim = n - augmented;
    const ops = [], st = [];
    const tex = () => new Matrix(W).toTex({ augmented });
    const record = (op, phase, title, why) => {
        applyOp(W, op);
        ops.push({ op: op.op, i: op.i, j: op.j, k: op.k, phase });
        if (steps) {
            const mt = tex();
            st.push(S(title, `\\xrightarrow{${arrowLabel(op)}} ${mt}`, opText(op, phase, why),
                { rule: `row-${op.op}`, op: op.op, i: op.i, j: op.j, k: op.k, phase, opTex: opTex(op), matrixTex: mt }));
        }
    };
    const pivots = [];
    let r = 0;
    let singularAt = -1;
    for (let c = 0; c < lim && r < m; c++) {
        const p = pickPivot(W, r, c, m);
        if (p < 0) {
            if (stopOnSingular) { singularAt = c; break; }
            if (steps && W.some((row, i) => i >= r && !row[c].isZero()) === false && r > 0) {
                st.push(S(msg('linalg.reduce.column_no_pivot', { p: c + 1 }), null,
                    msg('linalg.reduce.below_pivots_found_so_far_column', { p: c + 1 }),
                    { rule: 'no-pivot', col: c }));
            }
            continue;
        }
        if (p !== r) {
            const v = W[p][c], cur = W[r][c];
            const why = cur.isZero()
                ? msg('linalg.reduce.pivot_position_in_column_holds_0', { col: c + 1, v: qs(v), from: p + 1, to: r + 1 })
                : v.isOne() || v.eq(Q.MINUS_ONE)
                    ? msg('linalg.reduce.pivot_of_is_handier_it_sits', { unit: v.isOne() ? 1 : -1, v: qs(v), from: p + 1, to: r + 1 })
                    : msg('linalg.reduce.we_take_in_row_as_pivot', { v: qs(v), from: p + 1, to: r + 1 });
            record({ op: 'swap', i: r, j: p }, 'forward', msg('linalg.reduce.swap_rows'), why);
        }
        const piv = W[r][c];
        if (!piv.isOne()) record({ op: 'scale', i: r, k: piv.inv(), pivot: piv }, 'forward', msg('linalg.reduce.make_pivot_1'));
        for (let i = r + 1; i < m; i++) {
            if (!W[i][c].isZero()) record({ op: 'add', i, j: r, k: W[i][c].neg() }, 'forward', msg('linalg.reduce.clear_below_pivot'));
        }
        pivots.push(c);
        r++;
    }
    if (jordan && singularAt < 0) {
        for (let t = pivots.length - 1; t >= 0; t--) {
            const c = pivots[t];
            for (let i = 0; i < t; i++) {
                if (!W[i][c].isZero()) record({ op: 'add', i, j: t, k: W[i][c].neg() }, 'backward', msg('linalg.reduce.clear_above_pivot'));
            }
        }
    }
    return { W, pivots, ops, steps: st, singularAt };
}

export const STRATEGY = msg('linalg.reduce.we_pick_pivots_so_as_to');

/**
 * Reduced row echelon form by Gauss–Jordan elimination. {steps, augmented: k} (pivots only in the
 * first cols − k columns) → {matrix, pivots, rank, ops: [{op: 'swap'|'scale'|'add', i, j, k, phase}], steps?}.
 * Each step is one elementary row operation with opTex (R₂ → R₂ − 3R₁), matrixTex (the matrix after) and a why-text.
 */
export function matRref(A, opts = {}) {
    A = M(A);
    const augmented = opts.augmented ?? 0;
    const res = reduce(A.a, { augmented, steps: !!opts.steps });
    const out = { matrix: new Matrix(res.W), pivots: res.pivots, rank: res.pivots.length, ops: res.ops };
    if (opts.steps) {
        const st = [S(msg('linalg.reduce.row_reduce'), A.toTex({ augmented }),
            msg('linalg.reduce.forward_pass_go_through_columns_left', { p: STRATEGY }),
            { rule: 'rref-plan' }), ...res.steps];
        st.push(S(msg('linalg.reduce.reduced_row_echelon_form'), out.matrix.toTex({ augmented }),
            res.pivots.length
                ? msg('linalg.reduce.leading_ones_sit_in_column_their', { p: (lng) => res.pivots.length === 1 ? msg('linalg.reduce.formula').in(lng) : msg('linalg.reduce.s').in(lng), p2: res.pivots.map((c) => c + 1).join(', '), length: res.pivots.length })
                : msg('linalg.reduce.matrix_is_zero_its_rank_is'),
            { rule: 'answer' }));
        out.steps = st;
    }
    return out;
}

/** Rank (a number). */
export function matRank(A) {
    return reduce(M(A).a, { jordan: false }).pivots.length;
}

function primitiveVector(v) {
    // clear denominators, divide by the gcd, first non-zero entry positive
    let den = 1n;
    for (const x of v) den = (den / bigGcd(den, x.d)) * x.d;
    let ints = v.map((x) => x.n * (den / x.d));
    let g = 0n;
    for (const x of ints) g = bigGcd(g, x);
    if (g > 1n) ints = ints.map((x) => x / g);
    const first = ints.find((x) => x !== 0n);
    if (first !== undefined && first < 0n) ints = ints.map((x) => -x);
    return ints.map((x) => new Q(x));
}

export function nullspaceFrom(W, pivots, n, integer = true) {
    const free = [];
    for (let c = 0; c < n; c++) if (!pivots.includes(c)) free.push(c);
    return free.map((f) => {
        const v = new Array(n).fill(Q.ZERO);
        v[f] = Q.ONE;
        pivots.forEach((c, r) => { v[c] = W[r][f].neg(); });
        return integer ? primitiveVector(v) : v;
    });
}

/**
 * Basis of the null space {x : A·x = 0} → Q[][] (each vector cleared of denominators and made
 * primitive: integer entries without a common factor, first non-zero entry positive). {integer: false}
 * keeps the raw vectors (free variable = 1).
 */
export function matNullspace(A, opts = {}) {
    A = M(A);
    const r = reduce(A.a, {});
    return nullspaceFrom(r.W, r.pivots, A.cols, opts.integer ?? true);
}
