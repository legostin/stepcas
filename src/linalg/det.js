// linalg/det — determinants: small formulas, cofactor expansion, elimination.

import { Q } from '../core/rational.js';
import { L, R, S, fail, qs, qt, qtp, rowAccShort, sub } from './common.js';
import { M, Matrix, needSquare } from './core.js';
import { arrowLabel, opText } from './reduce.js';
import { msg } from '../i18n/index.js';

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
        st.push(S(msg('linalg.det.gaussian_elimination'), `\\det A = ${A.toTex({ env: 'vmatrix' })}`,
            msg('linalg.det.we_bring_matrix_to_triangular_form'),
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
                st.push(S(msg('linalg.det.column_is_zero_below_diagonal', { p: c + 1 }), `\\det A = 0`,
                    msg('linalg.det.column_has_only_zeros_on_and', { p: c + 1 }),
                    { rule: 'answer' }));
            }
            return { value: Q.ZERO, steps: st };
        }
        if (p !== c) {
            [W[c], W[p]] = [W[p], W[c]];
            sign = -sign;
            if (withSteps) {
                const mt = new Matrix(W).toTex({ env: 'vmatrix' });
                st.push(S(msg('linalg.det.swap_rows'), `\\xrightarrow{${R(c)} \\leftrightarrow ${R(p)}} -${mt}`,
                    msg('linalg.det.pivot_is_handier_swap_rows_and', { p: qs(W[c][c]), c: rowAccShort(c), p2: rowAccShort(p), p3: c + 1, p4: p + 1 }),
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
                st.push(S(msg('linalg.det.clear_below_diagonal'), `\\xrightarrow{${arrowLabel(op)}} ${sign < 0 ? '-' : ''}${mt}`,
                    opText(op, 'forward'), { rule: 'row-add', op: 'add', i, j: c, k }));
            }
        }
    }
    let value = sign < 0 ? Q.MINUS_ONE : Q.ONE;
    for (let i = 0; i < n; i++) value = value.mul(W[i][i]);
    if (withSteps) {
        st.push(S(msg('linalg.det.multiply_diagonal'), `\\det A = ${sign < 0 ? '-' : ''}${W.map((r, i) => qtp(r[i])).join(' \\cdot ')} = ${qt(value)}`,
            sign < 0 ? msg('linalg.det.we_swapped_rows_odd_number_of') : null,
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
            S(msg('linalg.det.rule_of_sarrus'), `\\det A = ${plus.map(sym).join(' + ')} - ${minus.map(sym).join(' - ')}`,
                msg('linalg.det.three_products_along_main_diagonal_and'),
                { rule: 'sarrus' }),
            S(msg('linalg.det.substitute_numbers'), `\\det A = ${plus.map(tt).join(' + ')} - ${minus.map((t) => `${tt(t)}`).join(' - ')}`, null, { rule: 'substitute' }),
            S(msg('linalg.det.compute'), `\\det A = (${signed(pv)}) - (${signed(mv)}) = ${qt(value)}`, null, { rule: 'answer' }),
        ],
    };
}

function detCofactor(A, withSteps, depth = 0, label = '\\det A') {
    const n = A.rows;
    if (n === 1) return { value: A.a[0][0], steps: withSteps ? [S(msg('linalg.det.1_1_matrix'), `${label} = ${qt(A.a[0][0])}`, null)] : [] };
    if (n === 2) {
        const [[a, b], [c, d]] = A.a;
        const value = a.mul(d).sub(b.mul(c));
        return { value, steps: withSteps ? [S(msg('linalg.det.2_2_determinant'), `${depth ? `${label} = ` : ''}${A.toTex({ env: 'vmatrix' })} = ${det2Tex(A)} = ${qt(value)}`,
            depth === 0 ? msg('linalg.det.product_of_main_diagonal_minus_product') : null, { rule: 'det2' })] : [] };
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
        ? msg('linalg.det.row', { p: ['первой', 'второй', 'третьей', 'четвёртой', 'пятой', 'шестой'][best.idx] ?? best.idx + 1, p2: best.idx + 1 })
        : msg('linalg.det.column', { p: ['первому', 'второму', 'третьему', 'четвёртому', 'пятому', 'шестому'][best.idx] ?? best.idx + 1, p2: best.idx + 1 });
    const lineWord = msg('linalg.det.along');
    const expansion = terms.length
        ? terms.map((t, k) => {
            const coef = t.sign < 0 ? t.v.neg() : t.v;
            const s = coef.isNeg() ? '-' : k ? '+' : '';
            const c = coef.abs();
            return `${s} ${c.isOne() ? '' : `${qt(c)} \\cdot `}${t.minor.toTex({ env: 'vmatrix' })}`;
        }).join(' ')
        : '0';
    const why = depth === 0
        ? msg('linalg.det.cofactor_expansion_each_entry_is_multiplied', { p: (lng) => best.zeros ? msg('linalg.det.we_take_with_most_zeros_zero', { p: (lng) => best.kind === 'row' ? msg('linalg.det.row_2').in(lng) : msg('linalg.det.column_2').in(lng), zeros: best.zeros }).in(lng) : '' })
        : best.zeros ? msg('linalg.det.it_has_most_zeros', { zeros: best.zeros }) : null;
    const st = [S(msg('linalg.det.expand', { p: (lng) => lineWord[lng], p2: (lng) => which[lng] }),
        `${label} = ${expansion}`, why, { rule: 'cofactor' })];
    for (const t of terms) {
        st.push(S(msg('linalg.det.minor_m', { p: sub(t.i + 1), p2: sub(t.j + 1) }), `M_{${t.i + 1}${t.j + 1}} = ${qt(t.md.value)}`, null,
            { rule: 'minor', sub: t.md.steps }));
    }
    const nums = terms.map((t, k) => {
        const coef = t.sign < 0 ? t.v.neg() : t.v;
        const s = coef.isNeg() ? '-' : k ? '+' : '';
        return `${s} ${qt(coef.abs())} \\cdot ${qtp(t.md.value)}`;
    }).join(' ');
    st.push(S(msg('linalg.det.put_it_together'), `${label} = ${nums || '0'} = ${qt(value)}`, null, { rule: 'answer' }));
    return { value, steps: st };
}

/**
 * Determinant (Q). {method: 'gauss' | 'cofactor' | 'sarrus'}: the default is the formula for 2×2,
 * Sarrus for 3×3 and Gaussian elimination from 4×4 on; cofactor expansion is allowed up to 6×6.
 * {steps: true} → {value, steps}.
 */
export function matDet(A, opts = {}) {
    A = M(A);
    needSquare(A, msg('linalg.det.determinant'));
    const n = A.rows;
    let method = opts.method ?? (n <= 2 ? 'cofactor' : n === 3 ? 'sarrus' : 'gauss');
    if (method === 'sarrus' && n !== 3) {
        throw fail(msg('linalg.det.rule_of_sarrus_works_for_3'), 'method');
    }
    if (method === 'cofactor' && n > 6) method = 'gauss';
    const r = method === 'gauss' ? detGauss(A, !!opts.steps) : method === 'sarrus' ? detSarrus(A, !!opts.steps) : detCofactor(A, !!opts.steps);
    return opts.steps ? { value: r.value, steps: r.steps, method } : r.value;
}
