// numbers/theory/modular — modular arithmetic: powers, inverses, congruences, the Chinese remainder theorem, orders,
// primitive roots, RSA keys.

import { G, big, bmod, coefX, fail, gcdCore, invCore, powmod, sn, tn, tp } from './common.js';
import { gcdSteps, ntEgcd } from './gcd.js';
import { factorMap, isPrimeBig, ntPhi } from './primes.js';
import { msg, eachLanguage } from '../../i18n/index.js';
import { step } from '../../core/steps.js';

// ---------------------------------------------------------------- modular arithmetic

function needModulus(m) {
    const M = big(m, msg('numbers.theory.modular.modulus'));
    if (M <= 0n) throw fail(msg('numbers.theory.modular.modulus_must_be_positive_integer'), 'modulus');
    return M;
}
const eqv = (m) => `\\pmod{${tn(m)}}`;

/**
 * a^e mod m by repeated squaring (result in [0, m)). A negative e uses the inverse (null if none).
 * {steps: true} → {value, rows: [{k, power, value, bit}], steps}.
 */
export function ntModPow(a, e, m, opts = {}) {
    const A = big(a),
        E = big(e),
        M = needModulus(m);
    if (E < 0n) {
        const inv = invCore(A, M);
        const value = inv === null ? null : powmod(inv, -E, M);
        if (!opts.steps) return value;
        const st = [
            step({
                title: msg('numbers.theory.modular.negative_exponent'),
                tex: `${tp(A)}^{${tn(E)}} = \\left(${tp(A)}^{-1}\\right)^{${tn(-E)}}`,
                text:
                    inv === null
                        ? msg('numbers.theory.modular.has_no_inverse_modulo_so_negative', { A: sn(A), M: sn(M) })
                        : msg('numbers.theory.modular.first_inverse_mod_then_raise_it', { A: sn(A), inv: sn(inv), M: sn(M), p: sn(-E) }),
                rule: 'negative-power',
            }),
        ];
        if (inv === null) return { value, rows: [], steps: st };
        const r = ntModPow(inv, -E, M, { steps: true });
        return { value, rows: r.rows, steps: [...st, ...r.steps] };
    }
    const value = powmod(A, E, M);
    if (!opts.steps) return value;
    const st = [];
    const rows = [];
    if (M === 1n) {
        st.push(
            step({
                title: msg('numbers.theory.modular.modulus_1'),
                tex: `${tp(A)}^{${tn(E)}} \\equiv 0 \\pmod{1}`,
                text: msg('numbers.theory.modular.every_number_is_congruent_to_0'),
                rule: 'answer',
            }),
        );
        return { value, rows, steps: st };
    }
    if (E === 0n) {
        st.push(
            step({
                title: msg('numbers.theory.modular.power_zero'),
                tex: `${tp(A)}^{0} = 1`,
                text: msg('numbers.theory.modular.anything_to_power_zero_is_1'),
                rule: 'answer',
            }),
        );
        return { value, rows, steps: st };
    }
    const bin = E.toString(2);
    const bits = bin.length;
    const used = [];
    for (let k = 0; k < bits; k++) if (bin[bits - 1 - k] === '1') used.push(k);
    const P = (k) => (k < 20 ? tn(1n << BigInt(k)) : `2^{${k}}`);
    const base = bmod(A, M);
    const sq = bits - 1;
    st.push(
        step({
            title: msg('numbers.theory.modular.write_exponent_in_binary'),
            tex: `${tn(E)} = ${bin}_2${used.length > 1 && used.length <= 12 ? ` = ${[...used].reverse().map(P).join(' + ')}` : ''}`,
            text: msg('numbers.theory.modular.then_is_product_of_powers_2', { A: sn(A), E: sn(E), sq, naive: sn(E - 1n) }),
            rule: 'binary',
        }),
    );
    let cur = base;
    for (let k = 0; k < bits; k++) {
        if (k > 0) cur = (cur * cur) % M;
        rows.push({ k, power: 1n << BigInt(k), value: cur, bit: bin[bits - 1 - k] === '1' });
    }
    if (bits <= 64) {
        const lines = [];
        let prev = null;
        for (const r of rows) {
            let rhs;
            if (r.k === 0) rhs = base === A ? tn(A) : `${tn(A)} \\equiv ${tn(base)}`;
            else {
                const s2 = prev * prev;
                rhs = `${tp(prev)}^2 = ${tn(s2)}${s2 !== r.value ? ` \\equiv ${tn(r.value)}` : ''}`;
            }
            lines.push(`${tp(A)}^{${P(r.k)}} & ${rhs} & ${r.bit ? '\\checkmark' : ''}`);
            prev = r.value;
        }
        st.push(
            step({
                title: msg('numbers.theory.modular.square_again_and_again'),
                tex: `\\begin{array}{r|l|c} ${lines.join(' \\\\ ')} \\end{array}`,
                text: msg('numbers.theory.modular.each_line_is_square_of_previous', { M: sn(M) }),
                rule: 'squaring',
            }),
        );
    }
    if (used.length > 1) {
        const picks = used.map((k) => rows[k].value);
        let run = picks[0];
        const runs = [];
        for (let i = 1; i < picks.length; i++) {
            const prod = run * picks[i];
            const r = prod % M;
            runs.push(`${sn(run)} · ${sn(picks[i])} = ${sn(prod)}${prod !== r ? ` ≡ ${sn(r)}` : ''}`);
            run = r;
        }
        const short = used.length <= 16;
        st.push(
            step({
                title: msg('numbers.theory.modular.multiply_ticked_lines'),
                tex: short
                    ? `${tp(A)}^{${tn(E)}} = ${[...used]
                          .reverse()
                          .map((k) => `${tp(A)}^{${P(k)}}`)
                          .join(' \\cdot ')} \\equiv ${[...used]
                          .reverse()
                          .map((k) => tn(rows[k].value))
                          .join(' \\cdot ')} \\equiv ${tn(value)} ${eqv(M)}`
                    : `${tp(A)}^{${tn(E)}} \\equiv ${tn(value)} ${eqv(M)}`,
                text: short ? msg('numbers.theory.modular.multiply_one_at_time_reducing_each', { p: runs.join('; ') }) : null,
                rule: 'multiply',
            }),
        );
    }
    st.push(step({ title: msg('numbers.theory.modular.answer'), tex: `${tp(A)}^{${tn(E)}} \\equiv ${tn(value)} ${eqv(M)}`, rule: 'answer' }));
    // a second route: Euler's theorem (Fermat's little theorem for a prime modulus)
    if (M <= 10n ** 12n && M > 2n && gcdCore(A, M) === 1n) {
        const ph = ntPhi(M);
        if (E >= ph) {
            const q = E / ph,
                r = E % ph;
            const prime = isPrimeBig(M);
            st.push(
                step({
                    title: prime ? msg('numbers.theory.modular.check_with_fermat_s_little_theorem') : msg('numbers.theory.modular.check_with_euler_s_theorem'),
                    tex: `${tp(A)}^{${tn(ph)}} \\equiv 1 ${eqv(M)},\\quad ${tn(E)} = ${tn(q)} \\cdot ${tn(ph)} + ${tn(r)} \\;\\Rightarrow\\; ${tp(A)}^{${tn(E)}} \\equiv ${tp(A)}^{${tn(r)}} \\equiv ${tn(value)}`,
                    text: prime
                        ? msg('numbers.theory.modular.modulus_is_prime_and_does_not', { M: sn(M), A: sn(A), ph: sn(ph) })
                        : msg('numbers.theory.modular.is_coprime_to_and_so_1', { A: sn(A), M: sn(M), ph: sn(ph) }),
                    rule: prime ? 'fermat' : 'euler',
                }),
            );
        }
    }
    return { value, rows, steps: st };
}

/** Inverse of a modulo m in [0, m), or null when gcd(a, m) ≠ 1. {steps: true} → {value, steps}. */
export function ntModInv(a, m, opts = {}) {
    const A = big(a),
        M = needModulus(m);
    const value = invCore(A, M);
    if (!opts.steps) return value;
    const st = [];
    const g = gcdCore(A, M);
    st.push(
        step({
            title: msg('numbers.theory.modular.what_we_look_for'),
            tex: `${tp(A)} \\cdot x \\equiv 1 ${eqv(M)}`,
            text: msg('numbers.theory.modular.we_want_x_such_that_x', { A: sn(A), M: sn(M) }),
            rule: 'inverse-def',
        }),
    );
    if (M === 1n) {
        st.push(
            step({
                title: msg('numbers.theory.modular.modulus_1'),
                tex: 'x \\equiv 0 \\pmod{1}',
                text: msg('numbers.theory.modular.modulo_1_every_number_is_0'),
                rule: 'answer',
            }),
        );
        return { value, steps: st };
    }
    if (value === null) {
        st.push(
            step({
                title: msg('numbers.theory.modular.no_inverse'),
                tex: eachLanguage((l) => `${G(l, A, M)} = ${tn(g)} \\ne 1`),
                text: msg('numbers.theory.modular.x_y_is_divisible_by_for', { A: sn(A), M: sn(M), g: sn(g) }),
                rule: 'answer',
                sub: gcdSteps(A, M).st,
            }),
        );
        return { value, steps: st };
    }
    const e = ntEgcd(A, M, { steps: true });
    const yP = e.y < 0n ? `(${sn(e.y)})` : sn(e.y);
    st.push(
        step({
            title: msg('numbers.theory.modular.extended_euclidean_algorithm'),
            tex: `${tp(A)} \\cdot ${tp(e.x)} + ${tn(M)} \\cdot ${tp(e.y)} = 1`,
            text: msg('numbers.theory.modular.gcd_is_1_and_running_euclid'),
            rule: 'egcd',
            sub: e.steps,
        }),
    );
    st.push(
        step({
            title: msg('numbers.theory.modular.drop_multiple_of_modulus'),
            tex: `${tp(A)} \\cdot ${tp(e.x)} \\equiv 1 ${eqv(M)} \\;\\Rightarrow\\; x \\equiv ${e.x !== value ? `${tn(e.x)} \\equiv ` : ''}${tn(value)} ${eqv(M)}`,
            text:
                e.x !== value
                    ? msg('numbers.theory.modular.term_is_multiple_of_and_does', { M: sn(M), yP, p: sn(e.x), p2: sn(M - 1n) })
                    : msg('numbers.theory.modular.term_is_multiple_of_and_does_2', { M: sn(M), yP }),
            rule: 'reduce',
        }),
    );
    const prod = A * value;
    st.push(
        step({
            title: msg('numbers.theory.modular.check'),
            tex: `${tp(A)} \\cdot ${tn(value)} = ${tn(prod)} = ${tn((prod - 1n) / M)} \\cdot ${tn(M)} + 1 \\equiv 1 ${eqv(M)}`,
            rule: 'check',
        }),
    );
    return { value, steps: st };
}

/**
 * Linear congruence a·x ≡ b (mod m) → {solvable, d, x0, m0, solutions?}: all solutions are
 * x ≡ x0 (mod m0), m0 = m / d, i.e. d residues modulo m (listed in `solutions` when d ≤ 1000).
 */
export function ntSolveCongruence(a, b, m, opts = {}) {
    const A = big(a),
        B = big(b),
        M = needModulus(m);
    const a1 = bmod(A, M),
        b1 = bmod(B, M);
    const d = gcdCore(a1, M); // gcd(0, M) = M
    const st = [];
    const cong = (x, y, mm) => `${coefX(x)} \\equiv ${tn(y)} ${eqv(mm)}`;
    if (opts.steps) {
        st.push(
            step({
                title: msg('numbers.theory.modular.what_congruence_means'),
                tex: cong(A, B, M),
                text: msg('numbers.theory.modular.we_need_x_such_that_is', {
                    p: A === 1n ? 'x' : `${sn(A)}·x`,
                    B: sn(B),
                    M: sn(M),
                    p2: (lng) =>
                        a1 !== A || b1 !== B
                            ? msg('numbers.theory.modular.first_replace_coefficients_by_their_remainders', { M: sn(M), a1: sn(a1), b1: sn(b1) }).in(lng)
                            : '',
                }),
                rule: 'congruence-def',
            }),
        );
        st.push(
            step({
                title: msg('numbers.theory.modular.gcd', { a1: sn(a1), M: sn(M), d: sn(d) }),
                tex: eachLanguage((l) => `d = ${G(l, a1, M)} = ${tn(d)}`),
                text: msg('numbers.theory.modular.gcd_of_coefficient_and_modulus_decides'),
                rule: 'gcd',
                sub: gcdSteps(a1, M).st,
            }),
        );
    }
    if (b1 % d !== 0n) {
        const res = { solvable: false, d, x0: null, m0: null, solutions: [] };
        if (opts.steps) {
            st.push(
                step({
                    title: msg('numbers.theory.modular.no_solutions'),
                    tex: `${tn(d)} \\nmid ${tn(b1)}`,
                    text: msg('numbers.theory.modular.if_x_k_then_x_k', { a1: sn(a1), b1: sn(b1), M: sn(M), d: sn(d) }),
                    rule: 'answer',
                }),
            );
            res.steps = st;
        }
        return res;
    }
    const a2 = a1 / d,
        b2 = b1 / d,
        m2 = M / d;
    const inv = invCore(a2, m2);
    const x0 = m2 === 1n ? 0n : bmod(b2 * inv, m2);
    const res = { solvable: true, d, x0, m0: m2 };
    if (d <= 1000n) {
        res.solutions = [];
        for (let k = 0n; k < d; k++) res.solutions.push(x0 + k * m2);
    }
    if (!opts.steps) return res;
    if (a1 === 0n) {
        st.push(
            step({
                title: msg('numbers.theory.modular.every_x_works'),
                tex: `0 \\cdot x \\equiv 0 ${eqv(M)}`,
                text: msg('numbers.theory.modular.both_coefficient_and_right_side_are'),
                rule: 'answer',
            }),
        );
        res.steps = st;
        return res;
    }
    if (d > 1n) {
        st.push(
            step({
                title: msg('numbers.theory.modular.divide_everything_by', { d: sn(d) }),
                tex: `${cong(a1, b1, M)} \\;\\Leftrightarrow\\; ${cong(a2, b2, m2)}`,
                text: msg('numbers.theory.modular.is_divisible_by_so_solutions_exist', {
                    b1: sn(b1),
                    d: sn(d),
                    a1: sn(a1),
                    M: sn(M),
                    a2: sn(a2),
                    b2: sn(b2),
                    m2: sn(m2),
                }),
                rule: 'divide',
            }),
        );
    }
    if (m2 === 1n) {
        st.push(
            step({
                title: msg('numbers.theory.modular.every_x_works'),
                tex: 'x \\equiv 0 \\pmod{1}',
                text: msg('numbers.theory.modular.modulo_1_congruence_always_holds'),
            }),
        );
    } else if (a2 !== 1n) {
        const iv = ntModInv(a2, m2, { steps: true });
        st.push(
            step({
                title: msg('numbers.theory.modular.multiply_by_inverse_of', { a2: sn(a2) }),
                tex: `${tn(a2)}^{-1} \\equiv ${tn(inv)} ${eqv(m2)} \\;\\Rightarrow\\; x \\equiv ${tn(b2)} \\cdot ${tn(inv)} = ${tn(b2 * inv)}${b2 * inv !== x0 ? ` \\equiv ${tn(x0)}` : ''} ${eqv(m2)}`,
                text: msg('numbers.theory.modular.and_are_coprime_so_has_inverse', { a2: sn(a2), m2: sn(m2), inv: sn(inv), p: sn(a2 * inv) }),
                rule: 'inverse',
                sub: iv.steps,
            }),
        );
    }
    if (d > 1n) {
        st.push(
            step({
                title: msg('numbers.theory.modular.solutions_modulo', { d: sn(d), n: d, M: sn(M) }),
                tex: res.solutions && d <= 12n ? `x \\equiv ${res.solutions.map(tn).join(',\\ ')} ${eqv(M)}` : `x = ${tn(x0)} + ${tn(m2)}k`,
                text: msg('numbers.theory.modular.all_solutions_are_x_k_modulo', { x0: sn(x0), m2: sn(m2), M: sn(M), d: sn(d), n: d }),
                rule: 'answer',
            }),
        );
    } else {
        st.push(
            step({
                title: msg('numbers.theory.modular.answer_and_check'),
                tex: `x \\equiv ${tn(x0)} ${eqv(M)},\\quad ${tn(a1)} \\cdot ${tn(x0)} = ${tn(a1 * x0)} \\equiv ${tn(bmod(a1 * x0, M))} ${eqv(M)}`,
                text: msg('numbers.theory.modular.solution_is_unique_modulo_x_k', { M: sn(M), x0: sn(x0) }),
                rule: 'answer',
            }),
        );
    }
    res.steps = st;
    return res;
}

/**
 * Chinese remainder theorem for any moduli (not necessarily coprime):
 * {solvable: true, x, m} with the answer x (mod m), m = lcm; or {solvable: false, conflict: i}.
 */
export function ntCrt(residues, moduli, opts = {}) {
    if (!Array.isArray(residues) || !Array.isArray(moduli) || residues.length !== moduli.length || !residues.length) {
        throw fail(msg('numbers.theory.modular.two_lists_of_same_length_are'));
    }
    const rs = residues.map((r) => big(r)),
        ms = moduli.map((m) => needModulus(m));
    let X = bmod(rs[0], ms[0]),
        Mx = ms[0];
    const st = [];
    const lin = (c, mult, v) => `${tn(c)} + ${tn(mult)}${v}`;
    if (opts.steps) {
        st.push(
            step({
                title: msg('numbers.theory.modular.system'),
                tex: `\\begin{cases} ${rs.map((r, i) => `x \\equiv ${tn(r)} ${eqv(ms[i])}`).join(' \\\\ ')} \\end{cases}`,
                text: msg('numbers.theory.modular.we_solve_by_substitution_express_x'),
                rule: 'crt',
            }),
        );
        st.push(
            step({
                title: msg('numbers.theory.modular.from_first_congruence'),
                tex: `x = ${lin(X, Mx, 't')}`,
                text: msg('numbers.theory.modular.numbers_leaving_remainder_on_division_by', { X: sn(X), Mx: sn(Mx) }),
            }),
        );
    }
    const vars = ['t', 's', 'u', 'v', 'w', 'z'];
    for (let i = 1; i < rs.length; i++) {
        const r = bmod(rs[i], ms[i]),
            m = ms[i];
        const g = gcdCore(Mx, m);
        const diff = bmod(r - X, m);
        const v = vars[(i - 1) % vars.length],
            vn = vars[i % vars.length];
        if (diff % g !== 0n) {
            const res = { solvable: false, x: null, m: null, conflict: i };
            if (opts.steps) {
                st.push(
                    step({
                        title: msg('numbers.theory.modular.contradiction'),
                        tex: `${lin(X, Mx, v)} \\equiv ${tn(r)} ${eqv(m)}`,
                        text: msg('numbers.theory.modular.moduli_and_share_divisor_modulo_conditions', {
                            Mx: sn(Mx),
                            m: sn(m),
                            g: sn(g),
                            p: sn(bmod(X, g)),
                            p2: sn(bmod(r, g)),
                        }),
                        rule: 'answer',
                    }),
                );
                res.steps = st;
            }
            return res;
        }
        const m2 = m / g;
        const a = bmod(Mx, m);
        const t0 = m2 === 1n ? 0n : bmod((diff / g) * invCore(Mx / g, m2), m2);
        const newX = X + Mx * t0,
            newM = Mx * m2;
        if (opts.steps) {
            const trivial = a === 1n && g === 1n;
            let how, sub;
            if (trivial) how = '';
            else if (m2 <= 12n) {
                const at = (a / g) * t0;
                const range = (l) =>
                    m2 === 2n ? msg('numbers.theory.modular.0_and_1').in(l) : m2 <= 4n ? [...Array(Number(m2)).keys()].join(', ') : `0, 1, …, ${sn(m2 - 1n)}`;
                const red =
                    g > 1n
                        ? msg('numbers.theory.modular.divide_congruence_and_modulus_by_gcd', { g: sn(g), p: sn(a / g), v, p2: sn(diff / g), m2: sn(m2) })
                        : '';
                how = msg('numbers.theory.modular.try_works_since', {
                    p: red,
                    v,
                    p2: (lng) => range(lng),
                    t0: sn(t0),
                    p3: sn(a / g),
                    at: sn(at),
                    p4: at !== bmod(at, m2) ? ` ≡ ${sn(bmod(at, m2))}` : '',
                });
            } else {
                how = msg('numbers.theory.modular.we_solve_it_with_modular_inverse');
                sub = ntSolveCongruence(a, diff, m, { steps: true }).steps;
            }
            st.push(
                step({
                    title: msg('numbers.theory.modular.substitute_into_congruence', { p: i + 1 }),
                    tex: `${lin(X, Mx, v)} \\equiv ${tn(r)} ${eqv(m)} \\;\\Rightarrow\\; ${coefX(a, v)} \\equiv ${tn(diff)} ${eqv(m)}${trivial ? '' : ` \\;\\Rightarrow\\; ${v} \\equiv ${tn(t0)} ${eqv(m2)}`}`,
                    text: msg('numbers.theory.modular.move_to_right_and_reduce_modulo', { X: sn(X), m: sn(m), v, p: how }),
                    rule: 'substitute',
                    ...(sub ? { sub } : {}),
                }),
            );
            st.push(
                step({
                    title: msg('numbers.theory.modular.combined_condition'),
                    tex: `${v} = ${lin(t0, m2, vn)} \\;\\Rightarrow\\; x = ${tn(X)} + ${tn(Mx)}(${lin(t0, m2, vn)}) = ${lin(newX, newM, vn)}`,
                    text: msg('numbers.theory.modular.now_x_is_described_by_single', {
                        p: sn(bmod(newX, newM)),
                        newM: sn(newM),
                        p2: (lng) =>
                            g > 1n
                                ? msg('numbers.theory.modular.modulus_is_lcm_not_product_moduli', { Mx: sn(Mx), m: sn(m), newM: sn(newM), g: sn(g) }).in(lng)
                                : '',
                    }),
                    rule: 'combine',
                }),
            );
        }
        X = bmod(newX, newM);
        Mx = newM;
    }
    const res = { solvable: true, x: X, m: Mx };
    if (opts.steps) {
        const checks = ms.map((mm) => `${sn(X)} = ${sn(X / mm)}·${sn(mm)} + ${sn(bmod(X, mm))}`).join('; ');
        st.push(
            step({
                title: msg('numbers.theory.modular.answer'),
                tex: `x \\equiv ${tn(X)} ${eqv(Mx)}`,
                text: msg('numbers.theory.modular.check_2', { checks }),
                rule: 'answer',
            }),
        );
        res.steps = st;
    }
    return res;
}

/** Multiplicative order of a modulo m (the smallest k > 0 with a^k ≡ 1), or null if gcd(a, m) ≠ 1. */
export function ntOrder(a, m) {
    const A = big(a),
        M = needModulus(m);
    if (M === 1n) return 1n;
    if (gcdCore(A, M) !== 1n) return null;
    let ord = ntPhi(M);
    for (const [p] of factorMap(ord)) {
        while (ord % p === 0n && powmod(A, ord / p, M) === 1n) ord /= p;
    }
    return ord;
}

/** The smallest primitive root modulo m, or null when there is none (it exists for 1, 2, 4, p^k, 2p^k). */
export function ntPrimitiveRoot(m) {
    const M = needModulus(m);
    if (M <= 2n) return M === 1n ? 0n : 1n;
    if (M === 4n) return 3n;
    const odd = M % 2n === 0n ? M / 2n : M;
    if (odd % 2n === 0n || factorMap(odd).size !== 1) return null;
    const ph = ntPhi(M);
    const ps = [...factorMap(ph).keys()];
    for (let g = 2n; g < M; g++) {
        if (gcdCore(g, M) !== 1n) continue;
        if (ps.every((p) => powmod(g, ph / p, M) !== 1n)) return g;
    }
    return null;
}

/** A toy RSA key from primes p ≠ q → {n, phi, e, d}; e is {e} or 65537, else the smallest odd valid e. */
export function ntRsaKey(p, q, opts = {}) {
    const P = big(p),
        Qn = big(q);
    if (P === Qn || !isPrimeBig(P) || !isPrimeBig(Qn)) throw fail(msg('numbers.theory.modular.two_different_primes_are_needed'));
    const n = P * Qn,
        phi = (P - 1n) * (Qn - 1n);
    let e = opts.e != null ? big(opts.e) : 65537n;
    if (opts.e == null && (e >= phi || gcdCore(e, phi) !== 1n)) {
        e = 3n;
        while (gcdCore(e, phi) !== 1n) e += 2n;
    }
    if (e <= 1n || e >= phi || gcdCore(e, phi) !== 1n) {
        throw fail(msg('numbers.theory.modular.e_does_not_work_we_need', { e, phi }));
    }
    const d = invCore(e, phi);
    const res = { n, phi, e, d };
    if (!opts.steps) return res;
    res.steps = [
        step({
            title: msg('numbers.theory.modular.public_modulus'),
            tex: `n = p \\cdot q = ${tn(P)} \\cdot ${tn(Qn)} = ${tn(n)}`,
            text: msg('numbers.theory.modular.multiplying_two_primes_is_easy_factoring'),
            rule: 'rsa-n',
        }),
        step({
            title: msg('numbers.theory.modular.euler_s_function'),
            tex: `\\varphi(n) = (p - 1)(q - 1) = ${tn(P - 1n)} \\cdot ${tn(Qn - 1n)} = ${tn(phi)}`,
            text: msg('numbers.theory.modular.only_key_owner_knows_it_computing'),
            rule: 'rsa-phi',
        }),
        step({
            title: msg('numbers.theory.modular.public_exponent'),
            tex: eachLanguage((l) => `e = ${tn(e)},\\quad ${G(l, e, phi)} = 1`),
            text: msg('numbers.theory.modular.e_must_be_coprime_to_n'),
            rule: 'rsa-e',
        }),
        step({
            title: msg('numbers.theory.modular.private_exponent'),
            tex: `d \\equiv e^{-1} \\pmod{\\varphi(n)}:\\quad d = ${tn(d)},\\quad ${tn(e)} \\cdot ${tn(d)} = ${tn(e * d)} \\equiv 1 \\pmod{${tn(phi)}}`,
            text: msg('numbers.theory.modular.then_m_e_d_m_mod'),
            rule: 'rsa-d',
            sub: ntModInv(e, phi, { steps: true }).steps,
        }),
    ];
    return res;
}
