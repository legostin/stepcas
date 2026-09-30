// linalg/systems — the inverse and linear systems (Gauss, Cramer), with steps.

import { Q } from '../core/rational.js';
import { E_, S, fail, qs, qt, qtp, sub } from './common.js';
import { M, Matrix, needSquare, toQ, vecTex } from './core.js';
import { matDet } from './det.js';
import { STRATEGY, nullspaceFrom, reduce } from './reduce.js';
import { msg, eachLanguage } from '../i18n/index.js';

// ---------------------------------------------------------------- inverse and linear systems

/** Inverse by Gauss–Jordan on [A | E]; null for a singular matrix. {steps: true} → {value, steps}. */
export function matInverse(A, opts = {}) {
    A = M(A);
    needSquare(A, msg('linalg.systems.inverse'));
    const n = A.rows;
    const W = A.augment(Matrix.identity(n)).a;
    const res = reduce(W, { augmented: n, steps: !!opts.steps, stopOnSingular: true });
    const singular = res.singularAt >= 0;
    const value = singular ? null : new Matrix(res.W.map((r) => r.slice(n)));
    if (!opts.steps) return value;
    const st = [];
    st.push(S(eachLanguage((l) => (msg('linalg.systems.append_identity_matrix').in(l))),
        eachLanguage((l) => `(A \\mid ${E_(l)}) = ${A.augment(Matrix.identity(n)).toTex({ augmented: n })}`),
        msg('linalg.systems.using_row_operations_we_turn_left', { p: STRATEGY }),
        { rule: 'inverse-plan' }));
    if (n === 2 && !singular) {
        const [[a, b], [c, d]] = A.a;
        const det = a.mul(d).sub(b.mul(c));
        st.push(S(msg('linalg.systems.for_2_2_there_is_ready'),
            `A^{-1} = \\frac{1}{ad - bc}\\begin{pmatrix} d & -b \\\\ -c & a \\end{pmatrix} = \\frac{1}{${qt(det)}}${new Matrix([[d, b.neg()], [c.neg(), a]]).toTex()}`,
            msg('linalg.systems.swap_entries_on_main_diagonal_negate'),
            { rule: 'inverse-2x2' }));
    }
    st.push(...res.steps);
    if (singular) {
        st.push(S(msg('linalg.systems.there_is_no_inverse'), '\\det A = 0',
            msg('linalg.systems.column_has_only_zeros_at_and', { p: res.singularAt + 1, n }),
            { rule: 'answer' }));
        return { value: null, steps: st };
    }
    st.push(S(msg('linalg.systems.answer'), `A^{-1} = ${value.toTex()}`,
        eachLanguage((l) => (msg('linalg.systems.left_half_is_now_identity_so').in(l))),
        { rule: 'answer' }));
    st.push(S(msg('linalg.systems.check'), eachLanguage((l) => `A \\cdot A^{-1} = ${A.mul(value).toTex()} = ${E_(l)}`), null, { rule: 'check' }));
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
    if (!bv || bv.length !== A.rows) throw fail(msg('linalg.systems.right_hand_side_must_have_as'), 'shape');
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
    st.push(S(msg('linalg.systems.augmented_matrix'), `${sysTex} \\quad\\Longrightarrow\\quad ${Aug.toTex({ augmented: 1 })}`,
        msg('linalg.systems.write_coefficients_and_after_bar_right', { p: STRATEGY }),
        { rule: 'augmented' }));
    st.push(...res.steps);
    if (out.kind === 'none') {
        st.push(S(msg('linalg.systems.contradiction'), `0 = ${qt(W[badRow][n])}`,
            msg('linalg.systems.row_has_zeros_on_left_and', { p: badRow + 1, p2: qs(W[badRow][n]), rank, p3: rank + 1 }),
            { rule: 'answer' }));
    } else if (out.kind === 'unique') {
        st.push(S(msg('linalg.systems.read_off_answer'), out.tex,
            msg('linalg.systems.left_part_is_identity_each_row', { n }),
            { rule: 'answer' }));
        const checks = A.a.map((r, i) => `${r.map((k, j) => `${qtp(k)} \\cdot ${qtp(out.x[j])}`).join(' + ')} = ${qt(bv[i])}`);
        st.push(S(msg('linalg.systems.check'), checks.length <= 4 ? `\\begin{aligned} ${checks.map((c) => `& ${c}`).join(' \\\\ ')} \\end{aligned}` : null,
            msg('linalg.systems.substitute_values_into_every_equation_all'), { rule: 'check' }));
    } else {
        const freeNames = out.params.map((p) => varTex(names, p.index));
        const fn = out.params.map((p) => varText(names, p.index)).join(', ');
        const pn = out.params.map((p) => p.name).join(', ');
        const one = out.params.length === 1;
        st.push(S(msg('linalg.systems.free_unknowns'), out.params.map((p, k) => `${freeNames[k]} = ${p.name}`).join(',\\quad '),
            msg('linalg.systems.there_are_leading_ones_but_unknowns', { rank, n, p: (lng) => one ? msg('linalg.systems.unknown_got_no_pivot_it_is', { fn, pn }).in(lng) : msg('linalg.systems.unknowns_got_no_pivots_they_are', { fn, pn }).in(lng), p2: (lng) => one ? msg('linalg.systems.it').in(lng) : msg('linalg.systems.them').in(lng) }),
            { rule: 'free-vars' }));
        st.push(S(msg('linalg.systems.general_solution'), out.tex,
            msg('linalg.systems.infinitely_many_solutions_one_for_every', { p: out.params.map((p) => p.name).join(', ') }),
            { rule: 'answer', vectorTex: out.vectorTex }));
    }
    out.steps = st;
    return out;
}

/** Cramer's rule for n ≤ 3 (n ≤ 6 without steps): {kind: 'unique', x, dets} or {kind: 'singular'} when det A = 0. */
export function matSolveCramer(A, b, opts = {}) {
    A = M(A);
    needSquare(A, msg('linalg.systems.cramer_s_rule'));
    const n = A.rows;
    if (n > 6 || (opts.steps && n > 3)) throw fail(msg('linalg.systems.cramer_s_rule_is_shown_for'), 'too-big');
    const bv = (Array.isArray(b) ? b : b.col(0)).map((v) => toQ(Array.isArray(v) ? v[0] : v));
    const Ai = (i) => new Matrix(A.a.map((r, k) => r.map((v, j) => (j === i ? bv[k] : v))));
    const d = matDet(A, { steps: !!opts.steps });
    const D = opts.steps ? d.value : d;
    const st = [];
    const names = opts.vars ?? null;
    if (opts.steps) {
        st.push(S(msg('linalg.systems.main_determinant'), `\\Delta = \\det A = ${qt(D)}`,
            msg('linalg.systems.cramer_s_rule_works_when_main'), { rule: 'cramer-main', sub: d.steps }));
    }
    if (D.isZero()) {
        const res = { kind: 'singular', x: null, dets: { main: D } };
        if (opts.steps) {
            st.push(S(msg('linalg.systems.cramer_s_rule_does_not_apply'), '\\Delta = 0',
                msg('linalg.systems.main_determinant_is_zero_system_has'), { rule: 'answer' }));
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
            st.push(S(msg('linalg.systems.determinant', { p: sub(i + 1) }), `\\Delta_{${i + 1}} = ${Ai(i).toTex({ env: 'vmatrix' })} = ${qt(v)}`,
                i === 0 ? msg('linalg.systems.replace_column_of_this_unknown_by') : null,
                { rule: 'cramer-minor', sub: di.steps }));
        }
    }
    const x = dets.map((v) => v.div(D));
    const res = { kind: 'unique', x, dets: { main: D, parts: dets } };
    if (opts.steps) {
        const fr = (i) => { const f = `\\frac{${qt(dets[i])}}{${qt(D)}}`; return f === qt(x[i]) ? f : `${f} = ${qt(x[i])}`; };
        st.push(S(msg('linalg.systems.answer'), x.map((v, i) => `${varTex(names, i)} = \\frac{\\Delta_{${i + 1}}}{\\Delta} = ${fr(i)}`).join(',\\quad '),
            msg('linalg.systems.each_unknown_is_its_determinant_divided'), { rule: 'answer' }));
        res.steps = st;
    }
    return res;
}
