// linalg/core — the Matrix class over Q: construction, arithmetic, TeX.

import { Q } from '../core/rational.js';
import { fail, qt } from './common.js';
import { msg } from '../i18n/index.js';

// ---------------------------------------------------------------- the Matrix class

export function toQ(v) {
    return v instanceof Q ? v : Q.of(v);
}
function sameShape(A, B) {
    if (B.rows !== A.rows || B.cols !== A.cols) {
        throw fail(msg('linalg.core.sizes_differ_and', { rows: A.rows, cols: A.cols, rows2: B.rows, cols2: B.cols }), 'shape');
    }
}

export class Matrix {
    /** Trusted constructor: `rows` is a rectangular Q[][] (use Matrix.from for anything else). */
    constructor(rows) {
        this.a = rows;
        this.rows = rows.length;
        this.cols = rows.length ? rows[0].length : 0;
    }

    /** From [[1, 2], ['1/2', 3]] (numbers, strings, BigInt, Q) or another Matrix. A flat array is a column. */
    static from(x) {
        if (x instanceof Matrix) return x;
        if (!Array.isArray(x) || !x.length) throw fail(msg('linalg.core.matrix_is_non_empty_array_of'), 'shape');
        const rows = x.map((r) => (Array.isArray(r) ? r.map(toQ) : [toQ(r)]));
        const c = rows[0].length;
        if (!c || rows.some((r) => r.length !== c)) throw fail(msg('linalg.core.all_rows_of_matrix_must_have'), 'shape');
        return new Matrix(rows);
    }

    static identity(n) {
        return new Matrix(Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? Q.ONE : Q.ZERO))));
    }

    static zeros(r, c = r) {
        return new Matrix(Array.from({ length: r }, () => new Array(c).fill(Q.ZERO)));
    }

    static fromColumns(cols) {
        const cs = cols.map((c) => c.map(toQ));
        return new Matrix(cs[0].map((_, i) => cs.map((c) => c[i])));
    }

    static diag(values) {
        const v = values.map(toQ);
        return new Matrix(v.map((d, i) => v.map((_, j) => (i === j ? d : Q.ZERO))));
    }

    get(i, j) {
        return this.a[i][j];
    }

    /** A copy with entry (i, j) replaced. */
    set(i, j, v) {
        const rows = this.a.map((r) => r.slice());
        rows[i][j] = toQ(v);
        return new Matrix(rows);
    }

    row(i) {
        return this.a[i].slice();
    }

    col(j) {
        return this.a.map((r) => r[j]);
    }

    isSquare() {
        return this.rows === this.cols;
    }

    isZero() {
        return this.a.every((r) => r.every((v) => v.isZero()));
    }

    isSymmetric() {
        return this.isSquare() && this.a.every((r, i) => r.every((v, j) => v.eq(this.a[j][i])));
    }

    add(B) {
        B = Matrix.from(B);
        sameShape(this, B);
        return new Matrix(this.a.map((r, i) => r.map((v, j) => v.add(B.a[i][j]))));
    }

    sub(B) {
        B = Matrix.from(B);
        sameShape(this, B);
        return new Matrix(this.a.map((r, i) => r.map((v, j) => v.sub(B.a[i][j]))));
    }

    scale(k) {
        k = toQ(k);
        return new Matrix(this.a.map((r) => r.map((v) => v.mul(k))));
    }

    neg() {
        return this.scale(Q.MINUS_ONE);
    }

    /** Matrix product; a flat array is treated as a vector (returns Q[]); a number/Q scales. */
    mul(B) {
        if (!(B instanceof Matrix) && !Array.isArray(B)) return this.scale(B);
        if (Array.isArray(B) && !Array.isArray(B[0])) {
            const v = B.map(toQ);
            if (v.length !== this.cols) throw fail(msg('linalg.core.vector_length_differs_from_number_of'), 'shape');
            return this.a.map((r) => r.reduce((s, x, j) => s.add(x.mul(v[j])), Q.ZERO));
        }
        B = Matrix.from(B);
        if (this.cols !== B.rows) {
            throw fail(msg('linalg.core.cannot_multiply_matrix_by_one_columns', { rows: this.rows, cols: this.cols, rows2: B.rows, cols2: B.cols }), 'shape');
        }
        const out = [];
        for (let i = 0; i < this.rows; i++) {
            const row = [];
            for (let j = 0; j < B.cols; j++) {
                let s = Q.ZERO;
                for (let k = 0; k < this.cols; k++) if (!this.a[i][k].isZero() && !B.a[k][j].isZero()) s = s.add(this.a[i][k].mul(B.a[k][j]));
                row.push(s);
            }
            out.push(row);
        }
        return new Matrix(out);
    }

    transpose() {
        return new Matrix(this.a[0].map((_, j) => this.a.map((r) => r[j])));
    }

    equals(B) {
        try {
            B = Matrix.from(B);
        } catch {
            return false;
        }
        return B.rows === this.rows && B.cols === this.cols && this.a.every((r, i) => r.every((v, j) => v.eq(B.a[i][j])));
    }

    trace() {
        if (!this.isSquare()) throw fail(msg('linalg.core.trace_is_defined_for_square_matrices'), 'shape');
        return this.a.reduce((s, r, i) => s.add(r[i]), Q.ZERO);
    }

    /** Aⁿ for a whole n ≥ 0 by repeated squaring (a negative power needs the inverse: matPower). */
    pow(n) {
        if (!this.isSquare()) throw fail(msg('linalg.core.power_is_defined_for_square_matrices'), 'shape');
        let N = BigInt(n);
        if (N < 0n) throw fail(msg('linalg.core.negative_power_needs_inverse'), 'domain');
        let base = this;
        let result = Matrix.identity(this.rows);
        while (N > 0n) {
            if (N & 1n) result = result.mul(base);
            N >>= 1n;
            if (N) base = base.mul(base);
        }
        return result;
    }

    /** [A | B] */
    augment(B) {
        B = Matrix.from(B);
        if (B.rows !== this.rows) throw fail(msg('linalg.core.matrices_have_different_numbers_of_rows'), 'shape');
        return new Matrix(this.a.map((r, i) => [...r, ...B.a[i]]));
    }

    /** The matrix without row i and column j. */
    minor(i, j) {
        return new Matrix(this.a.filter((_, r) => r !== i).map((row) => row.filter((_, c) => c !== j)));
    }

    /** Q[][] (a copy). */
    toArray() {
        return this.a.map((r) => r.slice());
    }

    toNumbers() {
        return this.a.map((r) => r.map((v) => v.toNumber()));
    }

    toStrings() {
        return this.a.map((r) => r.map((v) => v.toString()));
    }

    toString() {
        return `[${this.toStrings()
            .map((r) => `[${r.join(', ')}]`)
            .join(', ')}]`;
    }

    /**
     * TeX: pmatrix (or {env: 'vmatrix' | 'bmatrix'}); {augmented: k} draws a bar before the last k
     * columns: \left(\begin{array}{cc|c} … \end{array}\right). {boxed: [[i, j], …]} frames entries.
     */
    toTex(opts = {}) {
        const k = opts.augmented ?? 0;
        const boxed = new Set((opts.boxed ?? []).map(([i, j]) => `${i},${j}`));
        const body = this.a.map((r, i) => r.map((v, j) => (boxed.has(`${i},${j}`) ? `\\boxed{${qt(v)}}` : qt(v))).join(' & ')).join(' \\\\ ');
        if (k > 0 && k < this.cols) {
            const spec = 'c'.repeat(this.cols - k) + '|' + 'c'.repeat(k);
            return `\\left(\\begin{array}{${spec}} ${body} \\end{array}\\right)`;
        }
        const env = opts.env ?? 'pmatrix';
        return `\\begin{${env}} ${body} \\end{${env}}`;
    }
}

export function M(x) {
    return Matrix.from(x);
}
export function needSquare(A, what) {
    if (!A.isSquare()) throw fail(msg('linalg.core.is_defined_for_square_matrices_only', { p: what }), 'shape');
}
export const vecTex = (v) => `\\begin{pmatrix} ${v.map(qt).join(' \\\\ ')} \\end{pmatrix}`;
