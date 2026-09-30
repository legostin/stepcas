// numbers/theory/fractions — continued fractions, convergents, best approximations, Egyptian fractions.

import { Q, bigIsqrt } from '../../core/rational.js';
import { babs, big, dec, doubleExact, fail, gcdCore, ratOf, sn, subscript, tn } from './common.js';
import { msg, eachLanguage } from '../../i18n/index.js';
import { step } from '../../core/steps.js';

// ---------------------------------------------------------------- continued fractions

function cfTex(terms, period) {
    if (period && period.length) return `[${tn(terms[0])};\\ \\overline{${period.map(tn).join(',\\ ')}}]`;
    if (terms.length === 1) return `[${tn(terms[0])}]`;
    return `[${tn(terms[0])};\\ ${terms.slice(1).map(tn).join(',\\ ')}]`;
}
function nestedTex(terms) {
    let s = tn(terms[terms.length - 1]);
    for (let i = terms.length - 2; i >= 0; i--) s = `${tn(terms[i])} + \\cfrac{1}{${s}}`;
    return s;
}
function floorDiv(a, b) {
    const q = a / b;
    return a % b !== 0n && a < 0n !== b < 0n ? q - 1n : q;
}

/**
 * Continued fraction of a rational (Q, 'a/b', '3.14', BigInt) — exact and finite; of {sqrt: n} —
 * periodic, {a0, period}; of a non-integer double — the terms of its exact binary value until the
 * convergent reproduces the double (exact: false). → {terms: BigInt[], period?, exact, tex, steps?}.
 */
export function ntContinuedFraction(x, opts = {}) {
    if (x && typeof x === 'object' && !(x instanceof Q) && 'sqrt' in x) {
        const n = big(x.sqrt);
        if (n < 0n) throw fail(msg('numbers.theory.fractions.square_root_of_negative_number'));
        const a0 = bigIsqrt(n);
        if (a0 * a0 === n) {
            const res = { terms: [a0], a0, period: [], exact: true, periodic: false, tex: `\\sqrt{${tn(n)}} = ${tn(a0)}` };
            if (opts.steps)
                res.steps = [
                    step({
                        title: msg('numbers.theory.fractions.perfect_square'),
                        tex: res.tex,
                        text: msg('numbers.theory.fractions.root_is_integer_so_continued_fraction'),
                        rule: 'answer',
                    }),
                ];
            return res;
        }
        const period = [];
        const rows = [];
        let mm = 0n,
            d = 1n,
            a = a0;
        do {
            mm = d * a - mm;
            d = (n - mm * mm) / d;
            a = (a0 + mm) / d;
            period.push(a);
            rows.push({ m: mm, d, a });
            if (period.length > 200000) throw fail(msg('numbers.theory.fractions.period_is_too_long'), 'too-big');
        } while (a !== 2n * a0);
        const res = { terms: [a0, ...period], a0, period, exact: true, periodic: true, tex: `\\sqrt{${tn(n)}} = ${cfTex([a0], period)}` };
        if (opts.steps) {
            const st = [
                step({
                    title: msg('numbers.theory.fractions.integer_part'),
                    tex: `${tn(a0)}^2 = ${tn(a0 * a0)} < ${tn(n)} < ${tn((a0 + 1n) ** 2n)} = ${tn(a0 + 1n)}^2 \\;\\Rightarrow\\; a_0 = ${tn(a0)}`,
                    text: msg('numbers.theory.fractions.lies_between_and_so_its_integer', { n: sn(n), a0: sn(a0), p: sn(a0 + 1n) }),
                    rule: 'cf-int',
                }),
            ];
            const sq = Math.sqrt(Number(n));
            rows.slice(0, 20).forEach((r, i) => {
                const xv = (sq + Number(r.m)) / Number(r.d);
                const xt = r.d === 1n ? `\\sqrt{${tn(n)}} + ${tn(r.m)}` : `\\frac{\\sqrt{${tn(n)}} + ${tn(r.m)}}{${tn(r.d)}}`;
                st.push(
                    step({
                        title: msg('numbers.theory.fractions.term', { p: subscript(i + 1) }),
                        tex: eachLanguage((l) => `x_{${i + 1}} = ${xt} \\approx ${dec(xv, 3, l, true)} \\;\\Rightarrow\\; a_{${i + 1}} = ${tn(r.a)}`),
                        text: i === 0 ? msg('numbers.theory.fractions.flip_fractional_part_x_1_and', { n: sn(n), a0: sn(a0) }) : null,
                        rule: 'cf-term',
                    }),
                );
            });
            st.push(
                step({
                    title: msg('numbers.theory.fractions.period'),
                    tex: res.tex,
                    text: msg('numbers.theory.fractions.once_term_equals_2a_everything_repeats', { p: sn(2n * a0) }),
                    rule: 'answer',
                }),
            );
            res.steps = st;
        }
        return res;
    }
    if (typeof x === 'number' && !Number.isInteger(x)) {
        if (!Number.isFinite(x)) throw fail(msg('numbers.theory.fractions.finite_number_is_required'), 'nan');
        const max = opts.max ?? 40;
        let { num: a, den: b } = doubleExact(x);
        const terms = [];
        let [p0, p1, q0, q1] = [1n, 0n, 0n, 1n];
        while (b !== 0n && terms.length < max) {
            const t = floorDiv(a, b);
            terms.push(t);
            [a, b] = [b, a - t * b];
            [p0, p1] = [t * p0 + p1, p0];
            [q0, q1] = [t * q0 + q1, q0];
            if (Math.abs(Number(p0) / Number(q0) - x) <= 2 * Number.EPSILON * Math.abs(x)) break;
        }
        return { terms, exact: false, tex: cfTex(terms) };
    }
    const { num, den } = ratOf(x);
    const terms = [];
    const rows = [];
    let a = num,
        b = den;
    while (b !== 0n) {
        const t = floorDiv(a, b);
        const r = a - t * b;
        terms.push(t);
        rows.push({ a, b, q: t, r });
        a = b;
        b = r;
    }
    const res = { terms, exact: true, tex: cfTex(terms) };
    if (opts.steps) {
        const st = [
            step({
                title: msg('numbers.theory.fractions.idea'),
                text: msg('numbers.theory.fractions.take_integer_part_flip_remaining_proper'),
                rule: 'cf-idea',
            }),
        ];
        rows.forEach((r, i) => {
            st.push(
                step({
                    title: i === 0 ? msg('numbers.theory.fractions.integer_part') : msg('numbers.theory.fractions.flip', { p: sn(r.a), p2: sn(r.b) }),
                    tex:
                        r.r === 0n
                            ? `\\frac{${tn(r.a)}}{${tn(r.b)}} = ${tn(r.q)}`
                            : `\\frac{${tn(r.a)}}{${tn(r.b)}} = ${tn(r.q)} + \\frac{${tn(r.r)}}{${tn(r.b)}}`,
                    rule: 'cf-term',
                }),
            );
        });
        st.push(
            step({
                title: msg('numbers.theory.fractions.answer'),
                tex: `\\frac{${tn(num)}}{${tn(den)}} = ${terms.length <= 12 && terms.length > 1 ? nestedTex(terms) + ' = ' : ''}${cfTex(terms)}`,
                rule: 'answer',
            }),
        );
        res.steps = st;
    }
    return res;
}

/**
 * Convergents p_k/q_k: ntConvergents([3n, 7n, 15n, 1n]) → [{p, q}, …]. Also takes the result of
 * ntContinuedFraction; for a periodic one pass {count} to unroll the period that many terms.
 */
export function ntConvergents(cf, opts = {}) {
    let terms;
    if (Array.isArray(cf)) terms = cf.map((t) => big(t));
    else {
        terms = cf.terms.map((t) => big(t));
        if (cf.period && cf.period.length && opts.count) {
            terms = [terms[0]];
            while (terms.length < opts.count) terms.push(...cf.period);
        }
    }
    if (opts.count) terms = terms.slice(0, opts.count);
    const out = [];
    let [p0, p1, q0, q1] = [1n, 0n, 0n, 1n];
    for (const a of terms) {
        [p0, p1] = [a * p0 + p1, p0];
        [q0, q1] = [a * q0 + q1, q0];
        out.push({ p: p0, q: q0 });
    }
    return out;
}

/** The best rational approximation p/q of x with 1 ≤ q ≤ maxDen (x: number or rational) → {p, q}. */
export function ntBestApprox(x, maxDen) {
    const N = big(maxDen);
    if (N < 1n) throw fail(msg('numbers.theory.fractions.denominator_bound_must_be_at_least'));
    const isFloat = typeof x === 'number' && !Number.isInteger(x);
    const cf = ntContinuedFraction(x, isFloat ? { max: 60 } : {});
    const exact = isFloat ? null : ratOf(x);
    const closer = (pa, qa, pb, qb) => {
        if (isFloat) return Math.abs(Number(pa) / Number(qa) - x) < Math.abs(Number(pb) / Number(qb) - x);
        const { num, den } = exact;
        return babs(pa * den - num * qa) * qb < babs(pb * den - num * qb) * qa;
    };
    let [p0, p1, q0, q1] = [1n, 0n, 0n, 1n];
    for (const a of cf.terms) {
        const pn = a * p0 + p1,
            qn = a * q0 + q1;
        if (qn > N) {
            const k = (N - q1) / q0; // the best semiconvergent (p1 + k·p0)/(q1 + k·q0)
            const ps = p1 + k * p0,
                qs = q1 + k * q0;
            if (k > 0n && closer(ps, qs, p0, q0)) return { p: ps, q: qs };
            return { p: p0, q: q0 };
        }
        [p0, p1] = [pn, p0];
        [q0, q1] = [qn, q0];
    }
    return { p: p0, q: q0 };
}

/** Greedy (Fibonacci–Sylvester) Egyptian fraction of 0 < x ≤ 1 → denominators (BigInt[]). */
export function ntEgyptian(x, opts = {}) {
    let { num, den } = ratOf(x);
    if (num <= 0n || num > den) throw fail(msg('numbers.theory.fractions.fraction_greater_than_0_and_at'), 'range');
    const r0 = { num, den };
    const out = [];
    const st = [];
    while (num !== 0n) {
        const n = (den + num - 1n) / num;
        out.push(n);
        const nn = num * n - den,
            nd = den * n;
        const g = gcdCore(nn, nd) || 1n;
        if (opts.steps) {
            st.push(
                step({
                    title: msg('numbers.theory.fractions.take_1', { n: sn(n) }),
                    tex: `\\frac{${tn(num)}}{${tn(den)}} - \\frac{1}{${tn(n)}} = ${nn === 0n ? '0' : `\\frac{${tn(nn / g)}}{${tn(nd / g)}}`}`,
                    text:
                        num === 1n
                            ? msg('numbers.theory.fractions.what_is_left_has_numerator_1')
                            : msg('numbers.theory.fractions.largest_fraction_1_n_not_exceeding', { num: sn(num), den: sn(den), n: sn(n) }),
                    rule: 'greedy',
                }),
            );
        }
        num = nn / g;
        den = nd / g;
        if (out.length > 40) throw fail(msg('numbers.theory.fractions.too_many_terms'), 'too-big');
    }
    if (!opts.steps) return out;
    st.push(
        step({
            title: msg('numbers.theory.fractions.answer'),
            tex: `\\frac{${tn(r0.num)}}{${tn(r0.den)}} = ${out.map((n) => `\\frac{1}{${tn(n)}}`).join(' + ')}`,
            text: msg('numbers.theory.fractions.fibonacci_s_greedy_algorithm_always_stops'),
            rule: 'answer',
        }),
    );
    return { value: out, steps: st };
}
