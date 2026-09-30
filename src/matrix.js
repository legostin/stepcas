// matrix — exact linear algebra over Q with step-by-step explanations, plus a float toolkit for widgets.
//
//   const A = Matrix.from([[2, 1], [1, 2]]);        entries: numbers, strings ('1/2', '0,5'), BigInt or Q
//   matRref(A, {steps: true}) → {matrix, pivots, rank, ops, steps}
//   matEigen(A) → {charPoly, values: [{kind: 'rational', value: Q, vectors, …}, …]}
//
// Convention as in the rest of the engine: a function returns its bare value; {steps: true} returns
// {value, steps, …} (functions whose result is already an object just gain `steps`). Rows and columns
// are 0-based in data (i, j) and 1-based in explanations (R₁, R₂; x₁, x₂). RU uses E for the identity
// matrix, EN uses I.

import { MathError, Q, bigGcd, rootExtract } from './rational.js';
import { ntDivisors } from './numtheory.js';
import { numPolyRoots } from './numeric.js';
import { Poly } from './poly.js';

// ---------------------------------------------------------------- tiny internal helpers

const L = (ru, en) => ({ ru, en });
const T = (f) => ({ ru: f('ru'), en: f('en') });
const fail = (ru, en, code = null) => new MathError({ ru, en }, null, null, code);
function S(title, tex, text, extra) {
    const s = { title };
    if (tex != null) s.tex = tex;
    if (text != null) s.text = text;
    if (extra) Object.assign(s, extra);
    if (Array.isArray(s.sub) && !s.sub.length) delete s.sub;
    return s;
}
const qs = (x) => x.toString().replace('-', '\u2212');
const qt = (x) => x.toTex();
/** Q as a TeX factor: parenthesised when negative. */
const qtp = (x) => (x.isNeg() ? `\\left(${qt(x)}\\right)` : qt(x));
const E_ = (l) => (l === 'ru' ? 'E' : 'I');
/** A − λE with a concrete λ: A - E, A + 2E, A - \frac{1}{2}E, A. */
const shiftTex = (lam, l) => (lam.isZero() ? 'A' : `A ${lam.isNeg() ? '+' : '-'} ${lam.abs().isOne() ? '' : qt(lam.abs())}${E_(l)}`);

const ORD_GEN = ['первой', 'второй', 'третьей', 'четвёртой', 'пятой', 'шестой', 'седьмой', 'восьмой', 'девятой', 'десятой'];
const ORD_ACC = ['первую', 'вторую', 'третью', 'четвёртую', 'пятую', 'шестую', 'седьмую', 'восьмую', 'девятую', 'десятую'];
const rowGen = (i) => (i < 10 ? `${ORD_GEN[i]} строки` : `строки ${i + 1}`); // из второй строки
const rowAcc = (i) => (i < 10 ? `${ORD_ACC[i]} строку` : `строку ${i + 1}`); // делим вторую строку
const rowAccShort = (i) => (i < 10 ? ORD_ACC[i] : `строку ${i + 1}`); // вычитаем первую
const rowDat = (i) => (i < 10 ? `${i === 1 ? 'ко' : 'к'} ${ORD_GEN[i]} строке` : `к строке ${i + 1}`); // ко второй строке
const rowLoc = (i) => (i < 10 ? `${i === 1 ? 'во' : 'в'} ${ORD_GEN[i]} строке` : `в строке ${i + 1}`); // во второй строке
const R = (i) => `R_{${i + 1}}`;
const SUBS = '₀₁₂₃₄₅₆₇₈₉';
const sub = (n) => String(n).split('').map((c) => SUBS[+c]).join('');

// ---------------------------------------------------------------- the Matrix class

function toQ(v) {
    return v instanceof Q ? v : Q.of(v);
}
function sameShape(A, B) {
    if (B.rows !== A.rows || B.cols !== A.cols) {
        throw fail(`Размеры не совпадают: ${A.rows}×${A.cols} и ${B.rows}×${B.cols}.`, `Sizes differ: ${A.rows}×${A.cols} and ${B.rows}×${B.cols}.`, 'shape');
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
        if (!Array.isArray(x) || !x.length) throw fail('Матрица задаётся непустым массивом строк.', 'A matrix is a non-empty array of rows.', 'shape');
        const rows = x.map((r) => (Array.isArray(r) ? r.map(toQ) : [toQ(r)]));
        const c = rows[0].length;
        if (!c || rows.some((r) => r.length !== c)) throw fail('Во всех строках матрицы должно быть одинаковое число элементов.', 'All rows of a matrix must have the same length.', 'shape');
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
            if (v.length !== this.cols) throw fail('Длина вектора не равна числу столбцов матрицы.', 'The vector length differs from the number of columns.', 'shape');
            return this.a.map((r) => r.reduce((s, x, j) => s.add(x.mul(v[j])), Q.ZERO));
        }
        B = Matrix.from(B);
        if (this.cols !== B.rows) {
            throw fail(`Нельзя умножить матрицу ${this.rows}×${this.cols} на ${B.rows}×${B.cols}: число столбцов первой должно равняться числу строк второй.`,
                `Cannot multiply a ${this.rows}×${this.cols} matrix by a ${B.rows}×${B.cols} one: the columns of the first must match the rows of the second.`, 'shape');
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
        try { B = Matrix.from(B); } catch { return false; }
        return B.rows === this.rows && B.cols === this.cols && this.a.every((r, i) => r.every((v, j) => v.eq(B.a[i][j])));
    }

    trace() {
        if (!this.isSquare()) throw fail('След определён только для квадратной матрицы.', 'The trace is defined for square matrices only.', 'shape');
        return this.a.reduce((s, r, i) => s.add(r[i]), Q.ZERO);
    }

    pow(n) {
        return matPower(this, n);
    }

    /** [A | B] */
    augment(B) {
        B = Matrix.from(B);
        if (B.rows !== this.rows) throw fail('У матриц разное число строк.', 'The matrices have different numbers of rows.', 'shape');
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
        return `[${this.toStrings().map((r) => `[${r.join(', ')}]`).join(', ')}]`;
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

function M(x) {
    return Matrix.from(x);
}
function needSquare(A, what) {
    if (!A.isSquare()) throw fail(`${what.ru} определён только для квадратной матрицы.`, `${what.en} is defined for square matrices only.`, 'shape');
}
const vecTex = (v) => `\\begin{pmatrix} ${v.map(qt).join(' \\\\ ')} \\end{pmatrix}`;

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
function arrowLabel(op) {
    if (op.op === 'swap') return `${R(op.i)} \\leftrightarrow ${R(op.j)}`;
    if (op.op === 'scale') return op.k.eq(Q.MINUS_ONE) ? `-${R(op.i)}` : `${qt(op.k)}\\,${R(op.i)}`;
    const a = op.k.abs();
    return `${R(op.i)} ${op.k.isNeg() ? '-' : '+'} ${a.isOne() ? '' : `${qt(a)}\\,`}${R(op.j)}`;
}

function opText(op, phase, why) {
    if (op.op === 'swap') {
        return why;
    }
    if (op.op === 'scale') {
        const p = op.pivot;
        if (p.eq(Q.MINUS_ONE)) return L(`Умножаем ${rowAcc(op.i)} на −1, чтобы ведущий элемент стал равен 1.`, `Multiply row ${op.i + 1} by −1 so that the pivot becomes 1.`);
        if (p.isInt()) return L(`Делим ${rowAcc(op.i)} на ${qs(p)}, чтобы ведущий элемент стал равен 1.`, `Divide row ${op.i + 1} by ${qs(p)} so that the pivot becomes 1.`);
        return L(`Умножаем ${rowAcc(op.i)} на ${qs(op.k)}, чтобы ведущий элемент ${qs(p)} стал равен 1.`, `Multiply row ${op.i + 1} by ${qs(op.k)} so that the pivot ${qs(p)} becomes 1.`);
    }
    const a = op.k.abs();
    const times = L(a.isOne() ? '' : `, умноженную на ${qs(a)}`, a.isOne() ? '' : `${qs(a)} times `);
    const where = phase === 'backward' ? L('над', 'above') : L('под', 'below');
    const act = op.k.isNeg()
        ? L(`из ${rowGen(op.i)} вычитаем ${rowAccShort(op.j)}${times.ru}`, `subtract ${times.en}row ${op.j + 1} from row ${op.i + 1}`)
        : L(`${rowDat(op.i)} прибавляем ${rowAccShort(op.j)}${times.ru}`, `add ${times.en}row ${op.j + 1} to row ${op.i + 1}`);
    return L(`Обнуляем элемент ${where.ru} ведущим: ${act.ru}.`, `Clear the entry ${where.en} the pivot: ${act.en}.`);
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
function reduce(W0, { augmented = 0, steps = false, jordan = true, stopOnSingular = false } = {}) {
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
                st.push(S(L(`Столбец ${c + 1}: ведущего нет`, `Column ${c + 1}: no pivot`), null,
                    L(`Ниже уже найденных ведущих в столбце ${c + 1} одни нули — переходим к следующему столбцу.`, `Below the pivots found so far column ${c + 1} has only zeros, so we move on to the next column.`),
                    { rule: 'no-pivot', col: c }));
            }
            continue;
        }
        if (p !== r) {
            const v = W[p][c], cur = W[r][c];
            const why = cur.isZero()
                ? L(`На месте ведущего элемента в столбце ${c + 1} стоит 0, а ${rowLoc(p)} — ${qs(v)}. Меняем местами ${rowAccShort(r)} и ${rowAccShort(p)} строки.`,
                    `The pivot position in column ${c + 1} holds 0, while row ${p + 1} has ${qs(v)}. Swap rows ${r + 1} and ${p + 1}.`)
                : v.isOne() || v.eq(Q.MINUS_ONE)
                    ? L(`Удобнее, чтобы ведущим элементом была ${v.isOne() ? 'единица' : 'минус единица'}: она стоит ${rowLoc(p)}. Меняем местами ${rowAccShort(r)} и ${rowAccShort(p)} строки — так не появятся дроби.`,
                        `A pivot of ${qs(v)} is handier: it sits in row ${p + 1}. Swap rows ${r + 1} and ${p + 1} — this way no fractions appear.`)
                    : L(`Берём ведущим элемент ${qs(v)} ${rowLoc(p)}: с ним получается меньше дробей. Меняем местами ${rowAccShort(r)} и ${rowAccShort(p)} строки.`,
                        `We take ${qs(v)} in row ${p + 1} as the pivot: it gives fewer fractions. Swap rows ${r + 1} and ${p + 1}.`);
            record({ op: 'swap', i: r, j: p }, 'forward', L('Меняем строки местами', 'Swap rows'), why);
        }
        const piv = W[r][c];
        if (!piv.isOne()) record({ op: 'scale', i: r, k: piv.inv(), pivot: piv }, 'forward', L('Делаем ведущий элемент единицей', 'Make the pivot 1'));
        for (let i = r + 1; i < m; i++) {
            if (!W[i][c].isZero()) record({ op: 'add', i, j: r, k: W[i][c].neg() }, 'forward', L('Обнуляем под ведущим', 'Clear below the pivot'));
        }
        pivots.push(c);
        r++;
    }
    if (jordan && singularAt < 0) {
        for (let t = pivots.length - 1; t >= 0; t--) {
            const c = pivots[t];
            for (let i = 0; i < t; i++) {
                if (!W[i][c].isZero()) record({ op: 'add', i, j: t, k: W[i][c].neg() }, 'backward', L('Обнуляем над ведущим', 'Clear above the pivot'));
            }
        }
    }
    return { W, pivots, ops, steps: st, singularAt };
}

const STRATEGY = L('Ведущий элемент выбираем так, чтобы не плодить дроби: сначала ищем в столбце 1 или −1, потом число, на которое делится вся его строка, иначе берём наименьшее по модулю.',
    'We pick pivots so as to avoid fractions: first a 1 or −1 in the column, then a number that divides its whole row, otherwise the entry of smallest absolute value.');

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
        const st = [S(L('Приводим к ступенчатому виду', 'Row reduce'), A.toTex({ augmented }),
            L(`Прямой ход: идём по столбцам слева направо, в каждом выбираем ведущий элемент, делаем его единицей и обнуляем всё под ним. Обратный ход: обнуляем элементы над ведущими. ${STRATEGY.ru}`,
                `Forward pass: go through the columns left to right; in each, choose a pivot, make it 1 and clear everything below it. Backward pass: clear the entries above the pivots. ${STRATEGY.en}`),
            { rule: 'rref-plan' }), ...res.steps];
        st.push(S(L('Приведённый ступенчатый вид', 'Reduced row echelon form'), out.matrix.toTex({ augmented }),
            res.pivots.length
                ? L(`Ведущие единицы стоят в ${res.pivots.length === 1 ? 'столбце' : 'столбцах'} ${res.pivots.map((c) => c + 1).join(', ')}. Их число — ранг матрицы: ${res.pivots.length}.`,
                    `The leading ones sit in column${res.pivots.length === 1 ? '' : 's'} ${res.pivots.map((c) => c + 1).join(', ')}. Their number is the rank: ${res.pivots.length}.`)
                : L('Матрица нулевая, её ранг равен 0.', 'The matrix is zero; its rank is 0.'),
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

function nullspaceFrom(W, pivots, n, integer = true) {
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

// ---------------------------------------------------------------- determinants

function det2Tex(A) {
    const [[a, b], [c, d]] = A.a;
    return `${qtp(a)} \\cdot ${qtp(d)} - ${qtp(b)} \\cdot ${qtp(c)}`;
}

function detGauss(A, withSteps) {
    const W = A.a.map((r) => r.slice());
    const n = W.length;
    let sign = 1;
    const st = [];
    if (withSteps) {
        st.push(S(L('Метод Гаусса', 'Gaussian elimination'), `\\det A = ${A.toTex({ env: 'vmatrix' })}`,
            L('Приводим матрицу к треугольному виду. Если к строке прибавить другую строку, умноженную на число, определитель не меняется; перестановка двух строк меняет его знак. У треугольной матрицы определитель равен произведению диагональных элементов.',
                'We bring the matrix to triangular form. Adding a multiple of one row to another does not change the determinant; swapping two rows flips its sign. The determinant of a triangular matrix is the product of its diagonal entries.'),
            { rule: 'det-gauss' }));
    }
    for (let c = 0; c < n; c++) {
        let p = -1, key = null;
        for (let i = c; i < n; i++) {
            const v = W[i][c];
            if (v.isZero()) continue;
            const k2 = [v.isOne() || v.eq(Q.MINUS_ONE) ? 0 : 1, v.abs(), i === c ? 0 : 1];
            if (!key || k2[0] < key[0] || (k2[0] === key[0] && (k2[1].lt(key[1]) || (k2[1].eq(key[1]) && k2[2] < key[2])))) { p = i; key = k2; }
        }
        if (p < 0) {
            if (withSteps) {
                st.push(S(L(`В столбце ${c + 1} одни нули`, `Column ${c + 1} is zero below the diagonal`), `\\det A = 0`,
                    L(`На диагонали и под ней в столбце ${c + 1} стоят нули: у треугольной матрицы на диагонали будет 0, значит, определитель равен 0.`,
                        `Column ${c + 1} has only zeros on and below the diagonal, so the triangular form has a 0 on the diagonal and the determinant is 0.`),
                    { rule: 'answer' }));
            }
            return { value: Q.ZERO, steps: st };
        }
        if (p !== c) {
            [W[c], W[p]] = [W[p], W[c]];
            sign = -sign;
            if (withSteps) {
                const mt = new Matrix(W).toTex({ env: 'vmatrix' });
                st.push(S(L('Меняем строки местами', 'Swap rows'), `\\xrightarrow{${R(c)} \\leftrightarrow ${R(p)}} -${mt}`,
                    L(`Удобнее ведущий элемент ${qs(W[c][c])}: меняем местами ${rowAccShort(c)} и ${rowAccShort(p)} строки. Определитель при этом меняет знак.`,
                        `The pivot ${qs(W[c][c])} is handier: swap rows ${c + 1} and ${p + 1}. This flips the sign of the determinant.`),
                    { rule: 'row-swap', op: 'swap', i: c, j: p }));
            }
        }
        for (let i = c + 1; i < n; i++) {
            if (W[i][c].isZero()) continue;
            const k = W[i][c].div(W[c][c]).neg();
            W[i] = W[i].map((v, j) => v.add(k.mul(W[c][j])));
            if (withSteps) {
                const op = { op: 'add', i, j: c, k };
                const mt = new Matrix(W).toTex({ env: 'vmatrix' });
                st.push(S(L('Обнуляем под диагональю', 'Clear below the diagonal'), `\\xrightarrow{${arrowLabel(op)}} ${sign < 0 ? '-' : ''}${mt}`,
                    opText(op, 'forward'), { rule: 'row-add', op: 'add', i, j: c, k }));
            }
        }
    }
    let value = sign < 0 ? Q.MINUS_ONE : Q.ONE;
    for (let i = 0; i < n; i++) value = value.mul(W[i][i]);
    if (withSteps) {
        st.push(S(L('Произведение диагонали', 'Multiply the diagonal'), `\\det A = ${sign < 0 ? '-' : ''}${W.map((r, i) => qtp(r[i])).join(' \\cdot ')} = ${qt(value)}`,
            sign < 0 ? L('Строки переставляли нечётное число раз, поэтому перед произведением стоит минус.', 'We swapped rows an odd number of times, hence the minus sign.') : null,
            { rule: 'answer' }));
    }
    return { value, steps: st };
}

function detSarrus(A, withSteps) {
    const a = A.a;
    const plus = [[0, 0, 1, 1, 2, 2], [0, 1, 1, 2, 2, 0], [0, 2, 1, 0, 2, 1]];
    const minus = [[0, 2, 1, 1, 2, 0], [0, 0, 1, 2, 2, 1], [0, 1, 1, 0, 2, 2]];
    const prod = (t) => a[t[0]][t[1]].mul(a[t[2]][t[3]]).mul(a[t[4]][t[5]]);
    const value = plus.reduce((s, t) => s.add(prod(t)), Q.ZERO).sub(minus.reduce((s, t) => s.add(prod(t)), Q.ZERO));
    if (!withSteps) return { value, steps: [] };
    const tt = (t) => `${qtp(a[t[0]][t[1]])} \\cdot ${qtp(a[t[2]][t[3]])} \\cdot ${qtp(a[t[4]][t[5]])}`;
    const sym = (t) => `a_{${t[0] + 1}${t[1] + 1}}a_{${t[2] + 1}${t[3] + 1}}a_{${t[4] + 1}${t[5] + 1}}`;
    const signed = (vals) => vals.map((v, i) => (i === 0 ? qt(v) : v.isNeg() ? `- ${qt(v.neg())}` : `+ ${qt(v)}`)).join(' ');
    const pv = plus.map(prod), mv = minus.map(prod);
    return {
        value,
        steps: [
            S(L('Правило треугольников (Саррюса)', 'The rule of Sarrus'), `\\det A = ${plus.map(sym).join(' + ')} - ${minus.map(sym).join(' - ')}`,
                L('Три произведения по главной диагонали и по «треугольникам» вдоль неё берём со знаком плюс, три по побочной диагонали и вдоль неё — со знаком минус.',
                    'Three products along the main diagonal and the "triangles" parallel to it come with a plus sign; three along the other diagonal come with a minus sign.'),
                { rule: 'sarrus' }),
            S(L('Подставляем числа', 'Substitute the numbers'), `\\det A = ${plus.map(tt).join(' + ')} - ${minus.map((t) => `${tt(t)}`).join(' - ')}`, null, { rule: 'substitute' }),
            S(L('Считаем', 'Compute'), `\\det A = (${signed(pv)}) - (${signed(mv)}) = ${qt(value)}`, null, { rule: 'answer' }),
        ],
    };
}

function detCofactor(A, withSteps, depth = 0, label = '\\det A') {
    const n = A.rows;
    if (n === 1) return { value: A.a[0][0], steps: withSteps ? [S(L('Матрица 1×1', 'A 1×1 matrix'), `${label} = ${qt(A.a[0][0])}`, null)] : [] };
    if (n === 2) {
        const [[a, b], [c, d]] = A.a;
        const value = a.mul(d).sub(b.mul(c));
        return { value, steps: withSteps ? [S(L('Определитель 2×2', 'A 2×2 determinant'), `${depth ? `${label} = ` : ''}${A.toTex({ env: 'vmatrix' })} = ${det2Tex(A)} = ${qt(value)}`,
            depth === 0 ? L('Произведение элементов главной диагонали минус произведение элементов побочной.', 'The product of the main diagonal minus the product of the other diagonal.') : null, { rule: 'det2' })] : [] };
    }
    // the row or column with the most zeros
    let best = { kind: 'row', idx: 0, zeros: -1 };
    for (let i = 0; i < n; i++) {
        const zr = A.a[i].filter((v) => v.isZero()).length;
        if (zr > best.zeros) best = { kind: 'row', idx: i, zeros: zr };
    }
    for (let j = 0; j < n; j++) {
        const zc = A.a.filter((r) => r[j].isZero()).length;
        if (zc > best.zeros) best = { kind: 'col', idx: j, zeros: zc };
    }
    const terms = [];
    for (let k = 0; k < n; k++) {
        const [i, j] = best.kind === 'row' ? [best.idx, k] : [k, best.idx];
        const v = A.a[i][j];
        if (v.isZero()) continue;
        const minor = A.minor(i, j);
        const md = detCofactor(minor, withSteps, depth + 1, `M_{${i + 1}${j + 1}}`);
        terms.push({ i, j, v, sign: (i + j) % 2 ? -1 : 1, minor, md });
    }
    const value = terms.reduce((s, t) => s.add(t.v.mul(t.md.value).mul(t.sign < 0 ? Q.MINUS_ONE : Q.ONE)), Q.ZERO);
    if (!withSteps) return { value, steps: [] };
    const which = best.kind === 'row'
        ? L(`${['первой', 'второй', 'третьей', 'четвёртой', 'пятой', 'шестой'][best.idx] ?? best.idx + 1} строке`, `row ${best.idx + 1}`)
        : L(`${['первому', 'второму', 'третьему', 'четвёртому', 'пятому', 'шестому'][best.idx] ?? best.idx + 1} столбцу`, `column ${best.idx + 1}`);
    const lineWord = L('по', 'along');
    const expansion = terms.length
        ? terms.map((t, k) => {
            const coef = t.sign < 0 ? t.v.neg() : t.v;
            const s = coef.isNeg() ? '-' : k ? '+' : '';
            const c = coef.abs();
            return `${s} ${c.isOne() ? '' : `${qt(c)} \\cdot `}${t.minor.toTex({ env: 'vmatrix' })}`;
        }).join(' ')
        : '0';
    const why = depth === 0
        ? L(`Разложение по строке или столбцу: каждый элемент умножаем на его алгебраическое дополнение (−1)^(i+j)·M_ij, где M_ij — определитель без строки i и столбца j.${best.zeros ? ` Берём ${best.kind === 'row' ? 'строку' : 'столбец'}, где больше всего нулей (${best.zeros}): нулевые слагаемые можно не писать.` : ''}`,
            `Cofactor expansion: each entry is multiplied by its cofactor (−1)^(i+j)·M_ij, where M_ij is the determinant without row i and column j.${best.zeros ? ` We take the ${best.kind === 'row' ? 'row' : 'column'} with the most zeros (${best.zeros}): zero terms can be dropped.` : ''}`)
        : best.zeros ? L(`Здесь больше всего нулей (${best.zeros}).`, `It has the most zeros (${best.zeros}).`) : null;
    const st = [S(L(`Раскладываем ${lineWord.ru} ${which.ru}`, `Expand ${lineWord.en} ${which.en}`),
        `${label} = ${expansion}`, why, { rule: 'cofactor' })];
    for (const t of terms) {
        st.push(S(L(`Минор M${sub(t.i + 1)}${sub(t.j + 1)}`, `Minor M${sub(t.i + 1)}${sub(t.j + 1)}`), `M_{${t.i + 1}${t.j + 1}} = ${qt(t.md.value)}`, null,
            { rule: 'minor', sub: t.md.steps }));
    }
    const nums = terms.map((t, k) => {
        const coef = t.sign < 0 ? t.v.neg() : t.v;
        const s = coef.isNeg() ? '-' : k ? '+' : '';
        return `${s} ${qt(coef.abs())} \\cdot ${qtp(t.md.value)}`;
    }).join(' ');
    st.push(S(L('Собираем', 'Put it together'), `${label} = ${nums || '0'} = ${qt(value)}`, null, { rule: 'answer' }));
    return { value, steps: st };
}

/**
 * Determinant (Q). {method: 'gauss' | 'cofactor' | 'sarrus'}: the default is the formula for 2×2,
 * Sarrus for 3×3 and Gaussian elimination from 4×4 on; cofactor expansion is allowed up to 6×6.
 * {steps: true} → {value, steps}.
 */
export function matDet(A, opts = {}) {
    A = M(A);
    needSquare(A, L('Определитель', 'The determinant'));
    const n = A.rows;
    let method = opts.method ?? (n <= 2 ? 'cofactor' : n === 3 ? 'sarrus' : 'gauss');
    if (method === 'sarrus' && n !== 3) {
        throw fail('Правило Саррюса работает только для матриц 3×3.', 'The rule of Sarrus works for 3×3 matrices only.', 'method');
    }
    if (method === 'cofactor' && n > 6) method = 'gauss';
    const r = method === 'gauss' ? detGauss(A, !!opts.steps) : method === 'sarrus' ? detSarrus(A, !!opts.steps) : detCofactor(A, !!opts.steps);
    return opts.steps ? { value: r.value, steps: r.steps, method } : r.value;
}

// ---------------------------------------------------------------- inverse and linear systems

/** Inverse by Gauss–Jordan on [A | E]; null for a singular matrix. {steps: true} → {value, steps}. */
export function matInverse(A, opts = {}) {
    A = M(A);
    needSquare(A, L('Обратная матрица', 'The inverse'));
    const n = A.rows;
    const W = A.augment(Matrix.identity(n)).a;
    const res = reduce(W, { augmented: n, steps: !!opts.steps, stopOnSingular: true });
    const singular = res.singularAt >= 0;
    const value = singular ? null : new Matrix(res.W.map((r) => r.slice(n)));
    if (!opts.steps) return value;
    const st = [];
    st.push(S(T((l) => (l === 'ru' ? 'Приписываем справа единичную матрицу' : 'Append the identity matrix')),
        T((l) => `(A \\mid ${E_(l)}) = ${A.augment(Matrix.identity(n)).toTex({ augmented: n })}`),
        T((l) => (l === 'ru'
            ? `Элементарными преобразованиями строк превращаем левую половину в единичную матрицу E. Те же действия превращают правую половину в A⁻¹: они равносильны умножению слева на A⁻¹. ${STRATEGY.ru}`
            : `Using row operations we turn the left half into the identity matrix I. The same operations turn the right half into A⁻¹, because together they amount to multiplying by A⁻¹ on the left. ${STRATEGY.en}`)),
        { rule: 'inverse-plan' }));
    if (n === 2 && !singular) {
        const [[a, b], [c, d]] = A.a;
        const det = a.mul(d).sub(b.mul(c));
        st.push(S(L('Для 2×2 есть готовая формула', 'For 2×2 there is a ready formula'),
            `A^{-1} = \\frac{1}{ad - bc}\\begin{pmatrix} d & -b \\\\ -c & a \\end{pmatrix} = \\frac{1}{${qt(det)}}${new Matrix([[d, b.neg()], [c.neg(), a]]).toTex()}`,
            L('Меняем местами элементы главной диагонали, у побочной меняем знаки и делим на определитель. Ниже — тот же ответ методом Гаусса.',
                'Swap the entries on the main diagonal, negate the other two and divide by the determinant. Below is the same answer by Gauss–Jordan.'),
            { rule: 'inverse-2x2' }));
    }
    st.push(...res.steps);
    if (singular) {
        st.push(S(L('Обратной матрицы нет', 'There is no inverse'), '\\det A = 0',
            L(`В столбце ${res.singularAt + 1} на месте ведущего и ниже — одни нули: левую половину нельзя превратить в единичную матрицу. Ранг A меньше ${n}, определитель равен 0 — матрица вырожденная, обратной у неё нет.`,
                `Column ${res.singularAt + 1} has only zeros at and below the pivot position, so the left half cannot become the identity. The rank of A is less than ${n} and det A = 0: the matrix is singular and has no inverse.`),
            { rule: 'answer' }));
        return { value: null, steps: st };
    }
    st.push(S(L('Ответ', 'Answer'), `A^{-1} = ${value.toTex()}`,
        T((l) => (l === 'ru' ? 'Слева получилась единичная матрица — значит, справа стоит A⁻¹.' : 'The left half is now the identity, so the right half is A⁻¹.')),
        { rule: 'answer' }));
    st.push(S(L('Проверка', 'Check'), T((l) => `A \\cdot A^{-1} = ${A.mul(value).toTex()} = ${E_(l)}`), null, { rule: 'check' }));
    return { value, steps: st };
}

const PARAMS = ['t', 's', 'u', 'v', 'w'];
function varTex(names, j) {
    return names ? names[j] : `x_{${j + 1}}`;
}
function varText(names, j) {
    return names ? names[j] : `x${sub(j + 1)}`;
}
function linComb(c, terms) {
    // c + Σ k·name  in TeX
    let s = c.isZero() && terms.some(([k]) => !k.isZero()) ? '' : qt(c);
    for (const [k, name] of terms) {
        if (k.isZero()) continue;
        const a = k.abs();
        const body = `${a.isOne() ? '' : qt(a)}${name}`;
        s += s === '' ? (k.isNeg() ? `-${body}` : body) : ` ${k.isNeg() ? '-' : '+'} ${body}`;
    }
    return s || '0';
}

/**
 * Solve A·x = b by Gauss–Jordan → {kind: 'unique' | 'none' | 'infinite', x, params, basis, rank,
 * rankAug, tex, steps?}. For 'infinite', x is the particular solution with all parameters 0,
 * params = [{name: 't', index: j}] (the free variables), basis — the matching null-space vectors,
 * so every solution is x + Σ paramₖ·basisₖ. {vars: ['x', 'y', 'z']} renames the unknowns.
 */
export function matSolve(A, b, opts = {}) {
    A = M(A);
    const bv = b instanceof Matrix ? b.col(0) : Array.isArray(b) ? b.map((v) => (Array.isArray(v) ? toQ(v[0]) : toQ(v))) : null;
    if (!bv || bv.length !== A.rows) throw fail('Столбец правых частей должен иметь столько же чисел, сколько строк в матрице.', 'The right-hand side must have as many numbers as the matrix has rows.', 'shape');
    const n = A.cols;
    const names = opts.vars ?? null;
    const Aug = A.augment(bv.map((v) => [v]));
    const res = reduce(Aug.a, { augmented: 1, steps: !!opts.steps });
    const W = res.W;
    const rank = res.pivots.length;
    const badRow = W.findIndex((r) => r.slice(0, n).every((v) => v.isZero()) && !r[n].isZero());
    const out = { kind: null, x: null, params: [], basis: [], rank, rankAug: badRow >= 0 ? rank + 1 : rank };
    if (badRow >= 0) out.kind = 'none';
    else {
        const x = new Array(n).fill(Q.ZERO);
        res.pivots.forEach((c, r) => { x[c] = W[r][n]; });
        out.x = x;
        if (rank === n) out.kind = 'unique';
        else {
            out.kind = 'infinite';
            const free = [];
            for (let c = 0; c < n; c++) if (!res.pivots.includes(c)) free.push(c);
            out.params = free.map((j, k) => ({ name: free.length <= PARAMS.length ? PARAMS[k] : `t_{${k + 1}}`, index: j }));
            out.basis = nullspaceFrom(W, res.pivots, n, false);
        }
    }
    // the answer in TeX
    if (out.kind === 'unique') out.tex = out.x.map((v, j) => `${varTex(names, j)} = ${qt(v)}`).join(',\\quad ');
    else if (out.kind === 'infinite') {
        out.tex = out.x.map((v, j) => {
            const p = out.params.find((pp) => pp.index === j);
            if (p) return `${varTex(names, j)} = ${p.name}`;
            return `${varTex(names, j)} = ${linComb(v, out.params.map((pp, k) => [out.basis[k][j], pp.name]))}`;
        }).join(',\\quad ');
        out.vectorTex = `${vecTex(out.x)} + ${out.params.map((p, k) => `${p.name}${vecTex(out.basis[k])}`).join(' + ')}`;
    } else out.tex = '\\varnothing';
    if (!opts.steps) return out;

    const st = [];
    const sysTex = `\\begin{cases} ${A.a.map((r, i) => `${linComb(Q.ZERO, r.map((k, j) => [k, varTex(names, j)]))} = ${qt(bv[i])}`).join(' \\\\ ')} \\end{cases}`;
    st.push(S(L('Расширенная матрица', 'The augmented matrix'), `${sysTex} \\quad\\Longrightarrow\\quad ${Aug.toTex({ augmented: 1 })}`,
        L(`Записываем коэффициенты при неизвестных и, за чертой, правые части. Преобразования строк матрицы — это те же действия с уравнениями (переставить, умножить на число, прибавить одно к другому), поэтому решения не меняются. ${STRATEGY.ru}`,
            `Write the coefficients and, after the bar, the right-hand sides. Row operations are exactly the operations on the equations (swap, multiply by a number, add one to another), so the solutions do not change. ${STRATEGY.en}`),
        { rule: 'augmented' }));
    st.push(...res.steps);
    if (out.kind === 'none') {
        st.push(S(L('Противоречие', 'A contradiction'), `0 = ${qt(W[badRow][n])}`,
            L(`В строке ${badRow + 1} слева одни нули, а справа ${qs(W[badRow][n])}: получилось уравнение 0 = ${qs(W[badRow][n])}. Система несовместна — решений нет. (Ранг матрицы коэффициентов ${rank}, а расширенной — ${rank + 1}: по теореме Кронекера — Капелли решений нет.)`,
                `Row ${badRow + 1} has zeros on the left and ${qs(W[badRow][n])} on the right: the equation 0 = ${qs(W[badRow][n])}. The system is inconsistent — no solutions. (The coefficient matrix has rank ${rank}, the augmented one ${rank + 1}; by the Rouché–Capelli theorem there are no solutions.)`),
            { rule: 'answer' }));
    } else if (out.kind === 'unique') {
        st.push(S(L('Читаем ответ', 'Read off the answer'), out.tex,
            L(`Слева получилась единичная матрица: каждая строка — это уже готовое уравнение вида x = число. Ранг равен числу неизвестных (${n}), поэтому решение единственное.`,
                `The left part is the identity: each row is now an equation "x = number". The rank equals the number of unknowns (${n}), so the solution is unique.`),
            { rule: 'answer' }));
        const checks = A.a.map((r, i) => `${r.map((k, j) => `${qtp(k)} \\cdot ${qtp(out.x[j])}`).join(' + ')} = ${qt(bv[i])}`);
        st.push(S(L('Проверка', 'Check'), checks.length <= 4 ? `\\begin{aligned} ${checks.map((c) => `& ${c}`).join(' \\\\ ')} \\end{aligned}` : null,
            L('Подставляем найденные значения в каждое уравнение — все равенства верны.', 'Substitute the values into every equation: all of them hold.'), { rule: 'check' }));
    } else {
        const freeNames = out.params.map((p) => varTex(names, p.index));
        const fn = out.params.map((p) => varText(names, p.index)).join(', ');
        const pn = out.params.map((p) => p.name).join(', ');
        const one = out.params.length === 1;
        st.push(S(L('Свободные неизвестные', 'Free unknowns'), out.params.map((p, k) => `${freeNames[k]} = ${p.name}`).join(',\\quad '),
            L(`Ведущих единиц ${rank}, а неизвестных ${n}. ${one ? `Неизвестной ${fn} ведущий элемент не достался: она свободная, её можно взять любой. Обозначим её параметром ${pn}` : `Неизвестным ${fn} ведущие элементы не достались: они свободные, их можно взять любыми. Обозначим их параметрами ${pn}`}, а остальные неизвестные выразим через ${one ? 'него' : 'них'}.`,
                `There are ${rank} leading ones but ${n} unknowns. ${one ? `The unknown ${fn} got no pivot: it is free and can take any value. Call it ${pn}` : `The unknowns ${fn} got no pivots: they are free and can take any values. Call them ${pn}`} and express the other unknowns through ${one ? 'it' : 'them'}.`),
            { rule: 'free-vars' }));
        st.push(S(L('Общее решение', 'The general solution'), out.tex,
            L(`Бесконечно много решений: при любых значениях ${out.params.map((p) => p.name).join(', ')}. В векторной записи — частное решение плюс линейная комбинация решений однородной системы.`,
                `Infinitely many solutions, one for every choice of ${out.params.map((p) => p.name).join(', ')}. In vector form: a particular solution plus a combination of solutions of the homogeneous system.`),
            { rule: 'answer', vectorTex: out.vectorTex }));
    }
    out.steps = st;
    return out;
}

/** Cramer's rule for n ≤ 3 (n ≤ 6 without steps): {kind: 'unique', x, dets} or {kind: 'singular'} when det A = 0. */
export function matSolveCramer(A, b, opts = {}) {
    A = M(A);
    needSquare(A, L('Правило Крамера', "Cramer's rule"));
    const n = A.rows;
    if (n > 6 || (opts.steps && n > 3)) throw fail('Правило Крамера показываем для систем до 3×3.', "Cramer's rule is shown for systems up to 3×3.", 'too-big');
    const bv = (Array.isArray(b) ? b : b.col(0)).map((v) => toQ(Array.isArray(v) ? v[0] : v));
    const Ai = (i) => new Matrix(A.a.map((r, k) => r.map((v, j) => (j === i ? bv[k] : v))));
    const d = matDet(A, { steps: !!opts.steps });
    const D = opts.steps ? d.value : d;
    const st = [];
    const names = opts.vars ?? null;
    if (opts.steps) {
        st.push(S(L('Главный определитель', 'The main determinant'), `\\Delta = \\det A = ${qt(D)}`,
            L('Правило Крамера работает, когда главный определитель не равен нулю.', "Cramer's rule works when the main determinant is not zero."), { rule: 'cramer-main', sub: d.steps }));
    }
    if (D.isZero()) {
        const res = { kind: 'singular', x: null, dets: { main: D } };
        if (opts.steps) {
            st.push(S(L('Правило Крамера не применимо', "Cramer's rule does not apply"), '\\Delta = 0',
                L('Главный определитель равен нулю: система либо несовместна, либо имеет бесконечно много решений. Разобраться поможет метод Гаусса.',
                    'The main determinant is zero: the system has either no solutions or infinitely many. Gaussian elimination will tell which.'), { rule: 'answer' }));
            res.steps = st;
        }
        return res;
    }
    const dets = [];
    for (let i = 0; i < n; i++) {
        const di = matDet(Ai(i), { steps: !!opts.steps });
        const v = opts.steps ? di.value : di;
        dets.push(v);
        if (opts.steps) {
            st.push(S(L(`Определитель Δ${sub(i + 1)}`, `Determinant Δ${sub(i + 1)}`), `\\Delta_{${i + 1}} = ${Ai(i).toTex({ env: 'vmatrix' })} = ${qt(v)}`,
                i === 0 ? L('Заменяем столбец коэффициентов при этой неизвестной столбцом правых частей.', 'Replace the column of this unknown by the right-hand sides.') : null,
                { rule: 'cramer-minor', sub: di.steps }));
        }
    }
    const x = dets.map((v) => v.div(D));
    const res = { kind: 'unique', x, dets: { main: D, parts: dets } };
    if (opts.steps) {
        const fr = (i) => { const f = `\\frac{${qt(dets[i])}}{${qt(D)}}`; return f === qt(x[i]) ? f : `${f} = ${qt(x[i])}`; };
        st.push(S(L('Ответ', 'Answer'), x.map((v, i) => `${varTex(names, i)} = \\frac{\\Delta_{${i + 1}}}{\\Delta} = ${fr(i)}`).join(',\\quad '),
            L('Каждая неизвестная равна своему определителю, делённому на главный.', 'Each unknown is its determinant divided by the main one.'), { rule: 'answer' }));
        res.steps = st;
    }
    return res;
}

// ---------------------------------------------------------------- polynomials over Q (internal)

const ptrim = (a) => {
    const b = a.slice();
    while (b.length > 1 && b[b.length - 1].isZero()) b.pop();
    return b;
};
const padd = (a, b) => ptrim(Array.from({ length: Math.max(a.length, b.length) }, (_, i) => (a[i] ?? Q.ZERO).add(b[i] ?? Q.ZERO)));
const psub = (a, b) => padd(a, b.map((c) => c.neg()));
function pmul(a, b) {
    const out = new Array(a.length + b.length - 1).fill(Q.ZERO);
    for (let i = 0; i < a.length; i++) {
        if (a[i].isZero()) continue;
        for (let j = 0; j < b.length; j++) out[i + j] = out[i + j].add(a[i].mul(b[j]));
    }
    return ptrim(out);
}
const pdeg = (a) => {
    const t = ptrim(a);
    return t.length === 1 && t[0].isZero() ? -1 : t.length - 1;
};
const peval = (a, x) => a.reduceRight((acc, c) => acc.mul(x).add(c), Q.ZERO);
function pdiv(a, b) {
    let r = ptrim(a);
    const d = ptrim(b);
    const db = d.length - 1;
    const lead = d[db];
    const q = new Array(Math.max(1, r.length - db)).fill(Q.ZERO);
    while (pdeg(r) >= db && pdeg(r) >= 0) {
        const k = r.length - 1 - db;
        const c = r[r.length - 1].div(lead);
        q[k] = c;
        for (let i = 0; i <= db; i++) r[k + i] = r[k + i].sub(c.mul(d[i]));
        r = ptrim(r.slice(0, r.length - 1).length ? r.slice(0, r.length - 1) : [Q.ZERO]);
        if (r.length === 1 && r[0].isZero()) break;
    }
    return { q: ptrim(q), r };
}
/** Polynomial TeX in descending powers: \lambda^{3} - 6\lambda^{2} + 11\lambda - 6. */
function ptex(a, v = '\\lambda') {
    const t = ptrim(a);
    let s = '';
    for (let k = t.length - 1; k >= 0; k--) {
        const c = t[k];
        if (c.isZero()) continue;
        const ac = c.abs();
        const coef = k > 0 && ac.isOne() ? '' : qt(ac);
        const mon = k === 0 ? '' : k === 1 ? v : `${v}^{${k}}`;
        const term = `${coef}${mon}`;
        s += s === '' ? (c.isNeg() ? `-${term}` : term) : ` ${c.isNeg() ? '-' : '+'} ${term}`;
    }
    return s || '0';
}
function intPrimitive(a) {
    let den = 1n;
    for (const c of a) den = (den / bigGcd(den, c.d)) * c.d;
    let ints = a.map((c) => c.n * (den / c.d));
    let g = 0n;
    for (const x of ints) g = bigGcd(g, x);
    if (g > 1n) ints = ints.map((x) => x / g);
    return ints;
}
const babs = (x) => (x < 0n ? -x : x);

/** Rational roots with multiplicities and the remaining factor: {roots: [{root, mult}], rest}. */
function rationalRootsQ(a) {
    let rest = ptrim(a);
    const roots = [];
    let zero = 0;
    while (pdeg(rest) > 0 && rest[0].isZero()) { rest = rest.slice(1); zero++; }
    if (zero) roots.push({ root: Q.ZERO, mult: zero });
    if (pdeg(rest) >= 1) {
        const ints = intPrimitive(rest);
        const a0 = babs(ints[0]), an = babs(ints[ints.length - 1]);
        let cands = [];
        if (a0 < 10n ** 15n && an < 10n ** 15n) {
            const P = ntDivisors(a0), Qd = ntDivisors(an);
            if (P.length * Qd.length <= 50000) {
                const seen = new Set();
                for (const p of P) for (const q of Qd) {
                    for (const s of [1n, -1n]) {
                        const r = new Q(s * p, q);
                        const key = r.toString();
                        if (!seen.has(key)) { seen.add(key); cands.push(r); }
                    }
                }
            }
        }
        if (!cands.length) {
            // numeric guidance for huge coefficients: round approximate real roots to p/q with q | an
            const approx = numPolyRoots(rest.map((c) => c.toNumber())).filter((z) => z.im === 0);
            const dens = an < 10n ** 6n ? ntDivisors(an) : [1n];
            for (const z of approx) for (const q of dens) cands.push(new Q(BigInt(Math.round(z.re * Number(q))), q));
        }
        cands.sort((x, y) => x.cmp(y));
        for (const r of cands) {
            let mult = 0;
            while (pdeg(rest) >= 1 && peval(rest, r).isZero()) {
                rest = pdiv(rest, [r.neg(), Q.ONE]).q;
                mult++;
            }
            if (mult) roots.push({ root: r, mult });
        }
    }
    roots.sort((x, y) => x.root.cmp(y.root));
    return { roots, rest };
}

/** A quadratic factor over Z of a primitive integer polynomial of degree ≥ 4, or null. */
function quadFactor(rest) {
    const ints = intPrimitive(rest);
    const deg = ints.length - 1;
    if (deg < 4) return null;
    const ev = (x) => ints.reduceRight((acc, c) => acc * x + c, 0n);
    const v0 = ev(0n), v1 = ev(1n), vm = ev(-1n), v2 = ev(2n);
    if ([v0, v1, vm].some((v) => v === 0n || babs(v) > 10n ** 12n)) return null;
    const lead = babs(ints[deg]);
    const signed = (v) => { const d = ntDivisors(babs(v)); return [...d, ...d.map((x) => -x)]; };
    const D0 = signed(v0), D1 = signed(v1), Dm = signed(vm);
    if (D0.length * D1.length * Dm.length > 400000) return null;
    for (const c of D0) {
        for (const u of D1) {
            for (const w of Dm) {
                // Q(0) = c, Q(1) = u, Q(−1) = w  ⇒  a = (u + w)/2 − c, b = (u − w)/2
                if ((u + w) % 2n !== 0n) continue;
                const a = (u + w) / 2n - c, b = (u - w) / 2n;
                if (a <= 0n || lead % a !== 0n) continue;
                const q2 = 4n * a + 2n * b + c;
                if (q2 === 0n || v2 % q2 !== 0n) continue;
                const cand = [new Q(c), new Q(b), new Q(a)];
                const dv = pdiv(ints.map((x) => new Q(x)), cand);
                if (dv.r.every((x) => x.isZero())) return cand;
            }
        }
    }
    return null;
}

/** Roots of a quadratic a₂x² + a₁x + a₀ over Q: p ± q·√s (s squarefree, may be negative). */
function quadRoots(qf) {
    const [c, b, a] = qf;
    const D = b.mul(b).sub(new Q(4n).mul(a).mul(c));
    const p = b.neg().div(a.mul(new Q(2n)));
    // √D = √(n/d) = √(n·d)/d = out·√in / d
    const nd = D.n * D.d;
    const { out, in: inn } = rootExtract(nd, 2);
    const qq = new Q(babs(out), D.d).div(a.mul(new Q(2n)).abs());
    return { p, q: qq, s: inn, D };
}
function surdTex(p, q, s, sign) {
    // p + sign·q·√s, s squarefree (negative → imaginary)
    const imag = s < 0n;
    const rad = babs(s);
    const den = (p.d / bigGcd(p.d, q.d)) * q.d;
    const P = p.n * (den / p.d), Rr = q.n * (den / q.d);
    const root = `${Rr === 1n ? '' : Rr.toString()}${rad === 1n ? '' : `\\sqrt{${rad}}`}${imag ? (rad === 1n ? 'i' : '\\,i') : ''}` || '1';
    const num = P === 0n ? `${sign < 0 ? '-' : ''}${root}` : `${P} ${sign < 0 ? '-' : '+'} ${root}`;
    if (den === 1n) return num;
    if (P === 0n) return `${sign < 0 ? '-' : ''}\\frac{${root}}{${den}}`;
    return `\\frac{${num}}{${den}}`;
}

const toPoly = (coefs) => Poly.fromCoeffs(coefs);

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

// ---------------------------------------------------------------- float toolkit (number[][])

/** Product of float matrices (or matrix × vector). */
export function fmatMul(A, B) {
    if (!Array.isArray(B[0]) && !ArrayBuffer.isView(B[0])) return A.map((r) => r.reduce((s, x, j) => s + x * B[j], 0));
    const m = A.length, n = B[0].length, p = B.length;
    const out = Array.from({ length: m }, () => new Array(n).fill(0));
    for (let i = 0; i < m; i++) {
        const Ai = A[i], Oi = out[i];
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
    return fmatSolve(A, Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 1 : 0))));
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
        let off = 0, diag = 0;
        for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) (i === j ? (diag += a[i][j] ** 2) : (off += a[i][j] ** 2));
        if (off <= 1e-30 * Math.max(diag, 1e-300)) break;
        for (let p = 0; p < n - 1; p++) {
            for (let q = p + 1; q < n; q++) {
                if (Math.abs(a[p][q]) < 1e-300) continue;
                const theta = (a[q][q] - a[p][p]) / (2 * a[p][q]);
                const t = (theta >= 0 ? 1 : -1) / (Math.abs(theta) + Math.sqrt(theta * theta + 1));
                const c = 1 / Math.sqrt(t * t + 1), s = t * c;
                for (let k = 0; k < n; k++) {
                    const akp = a[k][p], akq = a[k][q];
                    a[k][p] = c * akp - s * akq;
                    a[k][q] = s * akp + c * akq;
                }
                for (let k = 0; k < n; k++) {
                    const apk = a[p][k], aqk = a[q][k];
                    a[p][k] = c * apk - s * aqk;
                    a[q][k] = s * apk + c * aqk;
                }
                for (let k = 0; k < n; k++) {
                    const vkp = V[k][p], vkq = V[k][q];
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
    const V = Array.from({ length: n }, (_, i) => { const v = new Float64Array(n); v[i] = 1; return v; });
    for (let sweep = 0; sweep < sweepsMax; sweep++) {
        let rotated = false;
        for (let p = 0; p < n - 1; p++) {
            const up = cols[p];
            for (let q = p + 1; q < n; q++) {
                const uq = cols[q];
                let alpha = 0, beta = 0, gamma = 0;
                for (let i = 0; i < m; i++) { alpha += up[i] * up[i]; beta += uq[i] * uq[i]; gamma += up[i] * uq[i]; }
                if (gamma === 0 || Math.abs(gamma) <= 1e-15 * Math.sqrt(alpha * beta)) continue;
                rotated = true;
                const zeta = (beta - alpha) / (2 * gamma);
                const t = (zeta >= 0 ? 1 : -1) / (Math.abs(zeta) + Math.sqrt(1 + zeta * zeta));
                const c = 1 / Math.sqrt(1 + t * t), s = c * t;
                for (let i = 0; i < m; i++) { const x = up[i], y = uq[i]; up[i] = c * x - s * y; uq[i] = s * x + c * y; }
                const vp = V[p], vq = V[q];
                for (let i = 0; i < n; i++) { const x = vp[i], y = vq[i]; vp[i] = c * x - s * y; vq[i] = s * x + c * y; }
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
    const m = A.length, n = A[0].length;
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
    const m = A.length, n = A[0].length;
    const l = Math.min(n, m, k + (opts.oversample ?? 10));
    const q = opts.powerIters ?? 2;
    let seed = (opts.seed ?? 1) >>> 0 || 1;
    const rnd = () => { seed ^= seed << 13; seed >>>= 0; seed ^= seed >>> 17; seed ^= seed << 5; seed >>>= 0; return seed / 4294967296; };
    const gauss = () => { const u = rnd() || 1e-12, v = rnd(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); };
    const Af = A.map((r) => Float64Array.from(r));
    const mulA = (cols) => cols.map((c) => { const y = new Float64Array(m); for (let i = 0; i < m; i++) { const r = Af[i]; let s = 0; for (let j = 0; j < n; j++) s += r[j] * c[j]; y[i] = s; } return y; });
    const mulAt = (cols) => cols.map((c) => { const y = new Float64Array(n); for (let i = 0; i < m; i++) { const r = Af[i], ci = c[i]; if (ci === 0) continue; for (let j = 0; j < n; j++) y[j] += r[j] * ci; } return y; });
    let Qc = orthonormalize(mulA(Array.from({ length: l }, () => Float64Array.from({ length: n }, gauss))), m);
    for (let it = 0; it < q; it++) {
        const Z = orthonormalize(mulAt(Qc), n);
        Qc = orthonormalize(mulA(Z), m);
    }
    // B = Qᵀ A (l × n); SVD of Bᵀ (n × l): Bᵀ = U'·S·V'ᵀ ⇒ B = V'·S·U'ᵀ
    const Bt = mulAt(Qc); // columns: Aᵀ q_i → the rows of B, i.e. the columns of Bᵀ
    const { S: s, Ucols, Vcols } = jacobiSvdCols(Bt.map((c) => Float64Array.from(c)), n);
    const kk = Math.min(k, s.length);
    const Ucols2 = Vcols.slice(0, kk).map((v) => { const u = new Float64Array(m); v.forEach((w, i) => { const qi = Qc[i]; for (let r = 0; r < m; r++) u[r] += w * qi[r]; }); return u; });
    return { U: colsToRows(Ucols2, m), S: s.slice(0, kk), V: colsToRows(Ucols.slice(0, kk), n) };
}

/** Rebuild the rank-k approximation U·diag(S)·Vᵀ (k defaults to all) → m×n number[][]. */
export function fmatLowRank(svd, k = svd.S.length) {
    const m = svd.U.length, n = svd.V.length;
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
    const m = A.length, n = A[0].length, r = Math.min(m, n);
    const Rm = A.map((row) => Array.from(row));
    const vs = [];
    for (let k = 0; k < r; k++) {
        let norm = 0;
        for (let i = k; i < m; i++) norm += Rm[i][k] ** 2;
        norm = Math.sqrt(norm);
        const v = new Float64Array(m);
        if (norm === 0) { vs.push(null); continue; }
        const alpha = Rm[k][k] > 0 ? -norm : norm;
        for (let i = k; i < m; i++) v[i] = Rm[i][k];
        v[k] -= alpha;
        const vv = v.reduce((s, x) => s + x * x, 0);
        if (vv === 0) { vs.push(null); continue; }
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
