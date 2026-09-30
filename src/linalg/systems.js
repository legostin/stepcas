// linalg/systems — the inverse and linear systems (Gauss, Cramer), with steps.

import { Q } from '../core/rational.js';
import { E_, L, S, T, fail, qs, qt, qtp, sub } from './common.js';
import { M, Matrix, needSquare, toQ, vecTex } from './core.js';
import { matDet } from './det.js';
import { STRATEGY, nullspaceFrom, reduce } from './reduce.js';

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

export const PARAMS = ['t', 's', 'u', 'v', 'w'];
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
