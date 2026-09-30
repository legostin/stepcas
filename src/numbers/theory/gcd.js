// theory/gcd — gcd and lcm (Euclid with steps), the extended Euclid algorithm and linear Diophantine equations.

import { Q } from '../../core/rational.js';
import { G, L, Lc, S, T, babs, big, bmod, fail, gT, gcdCore, sn, tn, tp } from './common.js';
import { factorMap, mapToList, ntFactorTex } from './primes.js';
import { msg } from '../../i18n/index.js';

// ---------------------------------------------------------------- gcd / lcm

function euclidRows(x, y) {
    const rows = [];
    while (y !== 0n) {
        const q = x / y, r = x % y;
        rows.push({ a: x, b: y, q, r });
        x = y;
        y = r;
    }
    return rows;
}

export function gcdSteps(A, B) {
    const st = [];
    let x = babs(A), y = babs(B);
    if (x === 0n && y === 0n) {
        st.push(S(msg('numbers.theory.gcd.gcd_of_two_zeros'), T((l) => `${G(l, 0, 0)} = 0`),
            msg('numbers.theory.gcd.zero_is_divisible_by_every_number'),
            { rule: 'gcd-zero' }));
        return { st, rows: [], g: 0n };
    }
    if (A < 0n || B < 0n) {
        st.push(S(msg('numbers.theory.gcd.signs_do_not_matter'), T((l) => `${G(l, A, B)} = ${G(l, x, y)}`),
            msg('numbers.theory.gcd.number_and_its_negative_have_same'),
            { rule: 'gcd-abs' }));
    }
    if (x === 0n || y === 0n) {
        const n = x || y;
        st.push(S(msg('numbers.theory.gcd.one_of_numbers_is_zero'), T((l) => `${G(l, x, y)} = ${tn(n)}`),
            msg('numbers.theory.gcd.zero_is_divisible_by_anything_so', { n: sn(n) }),
            { rule: 'gcd-zero' }));
        return { st, rows: [], g: n };
    }
    const swapped = x < y;
    if (swapped) [x, y] = [y, x];
    const rows = euclidRows(x, y);
    const g = rows[rows.length - 1].b;
    st.push(S(msg('numbers.theory.gcd.euclid_s_algorithm'),
        T((l) => `a = q \\cdot b + r \\;\\Rightarrow\\; ${msg('numbers.theory.gcd.b_b_r').in(l)}`),
        msg('numbers.theory.gcd.if_q_b_r_pairs_b', { p: (lng) => swapped ? msg('numbers.theory.gcd.we_start_with_larger_number', { x: sn(x) }).in(lng) : '' }),
        { rule: 'euclid' }));
    for (const { a, b, q, r } of rows) {
        st.push(S(msg('numbers.theory.gcd.divide_by', { a: sn(a), b: sn(b) }),
            `${tn(a)} = ${tn(q)} \\cdot ${tn(b)} + ${tn(r)}`,
            r > 0n
                ? msg('numbers.theory.gcd.quotient_remainder_so_gcd_gcd', { q: sn(q), r: sn(r), a: sn(a), b: sn(b) })
                : msg('numbers.theory.gcd.it_divides_exactly_quotient_remainder_0', { q: sn(q) }),
            { rule: 'division', row: { a, b, q, r } }));
    }
    return { st, rows, g };
}

function gcdAnswer(A, B, g) {
    return S(msg('numbers.theory.gcd.answer'), T((l) => `${G(l, A, B)} = ${tn(g)}`),
        g === 1n
            ? msg('numbers.theory.gcd.last_non_zero_remainder_is_1')
            : msg('numbers.theory.gcd.gcd_is_last_non_zero_remainder', { g: sn(g) }),
        { rule: 'answer' });
}

/** Greatest common divisor (≥ 0). {steps: true} → {value, rows: [{a, b, q, r}], steps}. */
export function ntGcd(a, b, opts = {}) {
    const A = big(a), B = big(b);
    if (!opts.steps) return gcdCore(A, B);
    const { st, rows, g } = gcdSteps(A, B);
    if (rows.length) st.push(gcdAnswer(A, B, g));
    return { value: g, rows, steps: st };
}

/** Least common multiple (≥ 0; the lcm with 0 is 0). {steps: true} → {value, steps}. */
export function ntLcm(a, b, opts = {}) {
    const A = big(a), B = big(b);
    const g = gcdCore(A, B);
    const value = A === 0n || B === 0n ? 0n : babs((A / g) * B);
    if (!opts.steps) return value;
    const st = [];
    if (value === 0n) {
        st.push(S(msg('numbers.theory.gcd.one_of_numbers_is_zero'), T((l) => `${Lc(l, A, B)} = 0`),
            msg('numbers.theory.gcd.only_multiple_of_zero_is_zero'), { rule: 'lcm-zero' }));
        return { value, steps: st };
    }
    const x = babs(A), y = babs(B);
    const gs = gcdSteps(x, y);
    st.push(S(msg('numbers.theory.gcd.first_gcd', { p: (lng) => gT(lng, x, y), g: sn(g) }),
        T((l) => `${G(l, x, y)} = ${tn(g)}`),
        msg('numbers.theory.gcd.we_find_it_by_euclid_s'),
        { rule: 'gcd', sub: [...gs.st, ...(gs.rows.length ? [gcdAnswer(x, y, g)] : [])] }));
    st.push(S(msg('numbers.theory.gcd.divide_product_by_gcd'),
        T((l) => `${Lc(l, x, y)} = \\frac{${tn(x)} \\cdot ${tn(y)}}{${tn(g)}}${g === 1n ? '' : ` = ${tn(x / g)} \\cdot ${tn(y)}`} = ${tn(value)}`),
        msg('numbers.theory.gcd.product_b_contains_common_factors_twice'),
        { rule: 'lcm-formula' }));
    if (x <= 10n ** 15n && y <= 10n ** 15n && x > 1n && y > 1n) {
        const fx = factorMap(x), fy = factorMap(y);
        const all = new Map(fx);
        for (const [p, e] of fy) all.set(p, Math.max(all.get(p) ?? 0, e));
        const sorted = [...all.entries()].sort((u, v) => (u[0] < v[0] ? -1 : 1)).map(([p, e]) => ({ p, e }));
        st.push(S(msg('numbers.theory.gcd.check_by_factorisation'),
            T((l) => `${tn(x)} = ${ntFactorTex(mapToList(fx))},\\quad ${tn(y)} = ${ntFactorTex(mapToList(fy))},\\quad ${Lc(l, x, y)} = ${ntFactorTex(sorted)} = ${tn(value)}`),
            msg('numbers.theory.gcd.another_way_factor_both_numbers_into'),
            { rule: 'lcm-factor' }));
    }
    return { value, steps: st };
}

function splitArgs(args) {
    let opts = {};
    const last = args[args.length - 1];
    if (args.length > 1 && last && typeof last === 'object' && !Array.isArray(last) && !(last instanceof Q)) {
        opts = last;
        args = args.slice(0, -1);
    }
    const list = args.length === 1 && Array.isArray(args[0]) ? args[0] : args;
    if (!list.length) throw fail(msg('numbers.theory.gcd.at_least_one_number_is_required'));
    return [list.map((v) => big(v)), opts];
}

/** gcd of several numbers: ntGcdMany([a, b, c], {steps}) or ntGcdMany(a, b, c). */
export function ntGcdMany(...args) {
    const [xs, opts] = splitArgs(args);
    let acc = babs(xs[0]);
    const st = [];
    for (let i = 1; i < xs.length; i++) {
        const prev = acc;
        acc = gcdCore(acc, xs[i]);
        if (opts.steps) {
            const gs = gcdSteps(prev, xs[i]);
            st.push(S(msg('numbers.theory.gcd.add_gcd', { p: sn(xs[i]), prev: sn(prev), acc: sn(acc) }),
                T((l) => `${G(l, prev, xs[i])} = ${tn(acc)}`),
                i === 1 ? msg('numbers.theory.gcd.for_several_numbers_we_chain_gcd') : null,
                { rule: 'gcd-chain', sub: [...gs.st, ...(gs.rows.length ? [gcdAnswer(prev, xs[i], acc)] : [])] }));
        }
    }
    if (!opts.steps) return acc;
    if (xs.length === 1) st.push(S(msg('numbers.theory.gcd.single_number'), tn(acc), msg('numbers.theory.gcd.gcd_of_one_number_is_its')));
    return { value: acc, steps: st };
}

/** lcm of several numbers: ntLcmMany([a, b, c], {steps}) or ntLcmMany(a, b, c). */
export function ntLcmMany(...args) {
    const [xs, opts] = splitArgs(args);
    let acc = babs(xs[0]);
    const st = [];
    for (let i = 1; i < xs.length; i++) {
        const prev = acc;
        acc = ntLcm(acc, xs[i]);
        if (opts.steps) {
            const r = ntLcm(prev, xs[i], { steps: true });
            st.push(S(msg('numbers.theory.gcd.add_lcm', { p: sn(xs[i]), prev: sn(prev), acc: sn(acc) }),
                T((l) => `${Lc(l, prev, xs[i])} = ${tn(acc)}`),
                i === 1 ? msg('numbers.theory.gcd.for_several_numbers_we_chain_lcm') : null,
                { rule: 'lcm-chain', sub: r.steps }));
        }
    }
    if (!opts.steps) return acc;
    return { value: acc, steps: st };
}

// ---------------------------------------------------------------- extended Euclid

function termTex(c, v, first) {
    // c·v as a TeX summand; v is a non-negative BigInt
    if (c === 0n) return '';
    const sign = c < 0n ? '-' : first ? '' : '+';
    const a = babs(c);
    const body = a === 1n ? tn(v) : `${tn(a)} \\cdot ${tn(v)}`;
    return first ? `${sign}${body}` : ` ${sign} ${body}`;
}
function linTex(s, X, t, Y) {
    const a = termTex(s, X, true);
    const b = termTex(t, Y, a === '');
    return (a + b) || '0';
}

/** Extended Euclid: {g, x, y} with a·x + b·y = g = gcd(a, b). {steps: true} adds rows and steps. */
export function ntEgcd(a, b, opts = {}) {
    const A = big(a), B = big(b);
    let X = babs(A), Y = babs(B);
    const swapped = X < Y;
    if (swapped) [X, Y] = [Y, X];
    const rows = euclidRows(X, Y);
    let s, t, g; // g = s·X + t·Y
    const back = [];
    if (X === 0n) { g = 0n; s = 0n; t = 0n; }
    else if (rows.length === 0) { g = X; s = 1n; t = 0n; }
    else if (rows.length === 1) { g = Y; s = 0n; t = 1n; }
    else {
        let j = rows.length - 2;
        g = rows[j].r;
        s = 1n;
        t = -rows[j].q;
        back.push({ j, s, t, first: true });
        while (j > 0) {
            const q = rows[j - 1].q;
            const ns = t, nt = s - t * q;
            back.push({ j: j - 1, from: { s, t }, s: ns, t: nt });
            s = ns;
            t = nt;
            j--;
        }
    }
    let x = swapped ? t : s, y = swapped ? s : t;
    if (A < 0n) x = -x;
    if (B < 0n) y = -y;
    const res = { g, x, y };
    if (!opts.steps) return res;

    const st = [];
    const gs = gcdSteps(A, B);
    st.push(S(msg('numbers.theory.gcd.first_euclid_s_algorithm'), T((l) => `${G(l, A, B)} = ${tn(g)}`),
        msg('numbers.theory.gcd.we_write_down_every_division_with'),
        { rule: 'euclid', sub: gs.st }));
    if (X === 0n) {
        st.push(S(msg('numbers.theory.gcd.both_numbers_are_zero'), '0 \\cdot 0 + 0 \\cdot 0 = 0', msg('numbers.theory.gcd.any_pair_works_we_take_x')));
        return { ...res, rows, steps: st };
    }
    if (rows.length <= 1) {
        st.push(S(msg('numbers.theory.gcd.representation_is_immediate'),
            `${tn(g)} = ${tp(A)} \\cdot ${tp(x)} + ${tp(B)} \\cdot ${tp(y)}`,
            msg('numbers.theory.gcd.gcd_equals_one_of_numbers_so', { g: sn(g) }),
            { rule: 'bezout' }));
    } else {
        st.push(S(msg('numbers.theory.gcd.work_backwards'), null,
            msg('numbers.theory.gcd.we_express_gcd_from_second_to'),
            { rule: 'back-substitution' }));
        for (const bk of back) {
            const row = rows[bk.j];
            if (bk.first) {
                st.push(S(msg('numbers.theory.gcd.express_from_dividing_by', { g: sn(g), p: sn(row.a), p2: sn(row.b) }),
                    `${tn(g)} = ${linTex(1n, row.a, -row.q, row.b)}`,
                    msg('numbers.theory.gcd.from_we_move_product_to_other', { p: sn(row.a), p2: sn(row.q), p3: sn(row.b), g: sn(g) }),
                    { rule: 'bezout' }));
            } else {
                const nxt = rows[bk.j + 1]; // gcd = fs·nxt.a + ft·nxt.b, nxt.a = row.b, nxt.b = row.r = row.a − row.q·row.b
                const { s: fs, t: ft } = bk.from;
                const inner = row.q === 1n ? `${tn(row.a)} - ${tn(row.b)}` : `${tn(row.a)} - ${tn(row.q)} \\cdot ${tn(row.b)}`;
                const mid = `${termTex(fs, row.b, true)} ${ft < 0n ? '-' : '+'} ${babs(ft) === 1n ? '' : `${tn(babs(ft))} \\cdot `}(${inner})`;
                st.push(S(msg('numbers.theory.gcd.substitute', { p: sn(row.r) }),
                    `${tn(g)} = ${linTex(fs, nxt.a, ft, nxt.b)} = ${mid} = ${linTex(bk.s, row.a, bk.t, row.b)}`,
                    msg('numbers.theory.gcd.from_dividing_by_substitute_and_collect', { p: sn(row.a), p2: sn(row.b), p3: sn(row.r), p4: sn(row.q) }),
                    { rule: 'bezout' }));
            }
        }
    }
    if (A < 0n || B < 0n) {
        st.push(S(msg('numbers.theory.gcd.put_signs_back'), null,
            msg('numbers.theory.gcd.we_worked_with_absolute_values_for')));
    }
    st.push(S(msg('numbers.theory.gcd.answer_and_check'),
        `${tp(A)} \\cdot ${tp(x)} + ${tp(B)} \\cdot ${tp(y)} = ${tn(A * x)} ${B * y < 0n ? '-' : '+'} ${tn(babs(B * y))} = ${tn(g)}`,
        msg('numbers.theory.gcd.we_found_x_y_such_numbers', { x: sn(x), y: sn(y), p: sn(B / g), p2: sn(A / g) }),
        { rule: 'answer' }));
    return { ...res, rows, steps: st };
}

/**
 * Linear Diophantine equation a·x + b·y = c → {solvable, g, x0, y0, dx, dy}:
 * all solutions are x = x0 + dx·k, y = y0 + dy·k (x0 is the smallest non-negative x).
 */
export function ntDiophantine(a, b, c, opts = {}) {
    const A = big(a), B = big(b), C = big(c);
    const st = [];
    if (A === 0n && B === 0n) {
        const res = { solvable: C === 0n, any: C === 0n, g: 0n, x0: 0n, y0: 0n, dx: 0n, dy: 0n };
        if (opts.steps) {
            st.push(S(msg('numbers.theory.gcd.both_coefficients_are_zero'), `0 \\cdot x + 0 \\cdot y = ${tn(C)}`,
                C === 0n ? msg('numbers.theory.gcd.every_pair_x_y_works') : msg('numbers.theory.gcd.left_side_is_always_0_and')));
            res.steps = st;
        }
        return res;
    }
    const e = ntEgcd(A, B, { steps: !!opts.steps });
    const g = e.g;
    if (C % g !== 0n) {
        const res = { solvable: false, g };
        if (opts.steps) {
            st.push(S(msg('numbers.theory.gcd.gcd', { A: sn(A), B: sn(B), g: sn(g) }), T((l) => `${G(l, A, B)} = ${tn(g)}`), null, { rule: 'gcd', sub: e.steps[0].sub }));
            st.push(S(msg('numbers.theory.gcd.no_solutions'), `${tn(g)} \\nmid ${tn(C)}`,
                msg('numbers.theory.gcd.for_all_integers_x_and_y', { g: sn(g), C: sn(C) }), { rule: 'answer' }));
            res.steps = st;
        }
        return res;
    }
    const k = C / g;
    let x0 = e.x * k, y0 = e.y * k;
    const dx = B / g, dy = -A / g;
    if (dx !== 0n) {
        const nx = bmod(x0, babs(dx));
        const shift = (nx - x0) / dx;
        x0 = nx;
        y0 += dy * shift;
    }
    const res = { solvable: true, g, x0, y0, dx, dy };
    if (!opts.steps) return res;
    st.push(S(msg('numbers.theory.gcd.gcd_and_b_zout_coefficients'),
        `${tp(A)} \\cdot ${tp(e.x)} + ${tp(B)} \\cdot ${tp(e.y)} = ${tn(g)}`,
        msg('numbers.theory.gcd.extended_euclidean_algorithm_details_inside'), { rule: 'egcd', sub: e.steps }));
    st.push(S(msg('numbers.theory.gcd.multiply_by', { k: sn(k) }),
        `${tp(A)} \\cdot ${tp(e.x * k)} + ${tp(B)} \\cdot ${tp(e.y * k)} = ${tn(C)}`,
        g === 1n ? msg('numbers.theory.gcd.gcd_is_1_so_there_are', { C: sn(C) })
            : msg('numbers.theory.gcd.is_divisible_by_gcd_so_solutions', { C: sn(C), g: sn(g), k: sn(k) }), { rule: 'scale' }));
    const part = (v0, dv) => `${tn(v0)} ${dv < 0n ? '-' : '+'} ${babs(dv) === 1n ? '' : tn(babs(dv))}k`;
    st.push(S(msg('numbers.theory.gcd.all_solutions'),
        `x = ${part(x0, dx)},\\quad y = ${part(y0, dy)},\\quad k \\in \\mathbb Z`,
        msg('numbers.theory.gcd.adding_to_x_and_y_does', { p: dx < 0n ? `прибавить ${sn(dx)}` : `прибавить ${sn(dx)}`, p2: (lng) => dy < 0n ? msg('numbers.theory.gcd.subtracting_from_2', { p: sn(-dy) }).in(lng) : msg('numbers.theory.gcd.adding_to_2', { dy: sn(dy) }).in(lng), A: sn(A), dx: sn(dx), B: sn(B), dy: sn(dy), x0: sn(x0) }),
        { rule: 'answer' }));
    res.steps = st;
    return res;
}
