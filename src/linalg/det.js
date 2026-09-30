// linalg/det — determinants: small formulas, cofactor expansion, elimination.

import { Q } from '../core/rational.js';
import { L, R, S, fail, qs, qt, qtp, rowAccShort, sub } from './common.js';
import { M, Matrix, needSquare } from './core.js';
import { arrowLabel, opText } from './reduce.js';

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
