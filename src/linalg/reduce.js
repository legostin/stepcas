// linalg/reduce — row reduction (Gauss–Jordan) with every elementary operation explained; rank and null space.

import { Q, bigGcd } from '../core/rational.js';
import { L, R, S, qs, qt, rowAcc, rowAccShort, rowDat, rowGen, rowLoc } from './common.js';
import { M, Matrix } from './core.js';

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

export const STRATEGY = L('Ведущий элемент выбираем так, чтобы не плодить дроби: сначала ищем в столбце 1 или −1, потом число, на которое делится вся его строка, иначе берём наименьшее по модулю.',
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
