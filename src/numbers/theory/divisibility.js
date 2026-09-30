// theory/divisibility — divisibility rules explained on the number.

import { babs, big, bmod, fail, sn, tn } from './common.js';
import { msg } from '../../i18n/index.js';
import { step } from '../../core/steps.js';

// ---------------------------------------------------------------- divisibility rules

const RULE_BASES = [2, 3, 4, 5, 8, 9, 10, 11, 25];
const RULE_COMBOS = { 6: [2, 3], 12: [3, 4], 15: [3, 5], 18: [2, 9], 20: [4, 5], 36: [4, 9], 45: [5, 9], 75: [3, 25], 100: [4, 25] };

function ruleFor(s, d) {
    // s — the decimal digits of |n|
    const last = s[s.length - 1];
    if (d === 2 || d === 5 || d === 10) {
        const ok = d === 2 ? '02468'.includes(last) : d === 5 ? '05'.includes(last) : last === '0';
        const need = d === 2 ? msg('numbers.theory.divisibility.even_0_2_4_6_or') : d === 5 ? msg('numbers.theory.divisibility.0_or_5') : '0';
        return {
            divides: ok,
            tex: s.length > 1 ? `\\ldots${last}` : last,
            text: msg('numbers.theory.divisibility.last_digit_is_number_is_divisible', {
                last,
                d,
                p: need,
                p2: (lng) => (ok ? msg('numbers.theory.divisibility.it_is_divisible').in(lng) : msg('numbers.theory.divisibility.it_is_not_divisible').in(lng)),
            }),
            why: msg('numbers.theory.divisibility.number_number_of_tens_10_last', { d }),
        };
    }
    if (d === 4 || d === 25 || d === 8) {
        const k = d === 8 ? 3 : 2;
        const t = BigInt(s.slice(-k));
        const D = BigInt(d);
        const ok = t % D === 0n;
        const pw = d === 8 ? '1000' : '100';
        return {
            divides: ok,
            tex: ok ? `${tn(t)} = ${d} \\cdot ${tn(t / D)}` : `${tn(t)} = ${d} \\cdot ${tn(t / D)} + ${tn(t % D)}`,
            text: msg('numbers.theory.divisibility.look_at', {
                p: (lng) =>
                    s.length > k
                        ? msg('numbers.theory.divisibility.last_digits', {
                              p: (lng) => (k === 2 ? msg('numbers.theory.divisibility.two').in(lng) : msg('numbers.theory.divisibility.three').in(lng)),
                          }).in(lng)
                        : msg('numbers.theory.divisibility.number_itself').in(lng),
                t: sn(t),
                p2: (lng) =>
                    ok
                        ? msg('numbers.theory.divisibility.is_divisible_by_so_whole_number', { t: sn(t), d }).in(lng)
                        : msg('numbers.theory.divisibility.is_not_divisible_by_remainder_so', { t: sn(t), d, p: sn(t % D) }).in(lng),
            }),
            why: msg('numbers.theory.divisibility.is_divisible_by_so_places_from', {
                pw,
                d,
                p: (lng) => (pw === '100' ? msg('numbers.theory.divisibility.hundreds').in(lng) : msg('numbers.theory.divisibility.thousands').in(lng)),
            }),
        };
    }
    if (d === 3 || d === 9) {
        const chain = [];
        let cur = s;
        let sum;
        do {
            sum = cur.split('').reduce((acc, c) => acc + BigInt(c), 0n);
            chain.push({ digits: cur, sum });
            cur = sum.toString();
        } while (sum >= 100n && chain.length < 5);
        const D = BigInt(d);
        const ok = sum % D === 0n;
        return {
            divides: ok,
            tex: chain.map((c) => (c.digits.length <= 24 ? `${c.digits.split('').join(' + ')} = ${tn(c.sum)}` : `\\ldots = ${tn(c.sum)}`)).join(',\\quad '),
            text: msg('numbers.theory.divisibility.digit_sum_is', {
                sum: sn(sum),
                p: (lng) => (chain.length > 1 ? msg('numbers.theory.divisibility.we_added_digits_more_than_once').in(lng) : ''),
                p2: (lng) =>
                    ok
                        ? msg('numbers.theory.divisibility.is_divisible_by_so_number_is', { sum: sn(sum), d }).in(lng)
                        : msg('numbers.theory.divisibility.is_not_divisible_by_remainder_so_2', { sum: sn(sum), d, p: sn(sum % D) }).in(lng),
            }),
            why: msg('numbers.theory.divisibility.10_100_1000_all_leave_remainder', { d }),
        };
    }
    // d === 11
    const ds = s.split('').reverse().map(Number);
    let odd = 0,
        even = 0;
    ds.forEach((v, i) => {
        if (i % 2 === 0) odd += v;
        else even += v;
    });
    const diff = odd - even;
    const ok = diff % 11 === 0;
    const oddDigits = ds.filter((_, i) => i % 2 === 0),
        evenDigits = ds.filter((_, i) => i % 2 === 1);
    return {
        divides: ok,
        tex: `(${oddDigits.join(' + ') || '0'}) - (${evenDigits.join(' + ') || '0'}) = ${odd} - ${even} = ${diff}`,
        text: msg('numbers.theory.divisibility.add_every_other_digit_starting_from', {
            odd,
            even,
            diff: sn(diff),
            p: (lng) =>
                ok
                    ? msg('numbers.theory.divisibility.is_divisible_by_11_so_number').in(lng)
                    : msg('numbers.theory.divisibility.is_not_divisible_by_11_so').in(lng),
        }),
        why: msg('numbers.theory.divisibility.10_11_1_so_10_1'),
    };
}

/**
 * A divisibility test with an explanation, d ∈ {2, 3, 4, 5, 8, 9, 10, 11, 25} or one of the
 * combinations 6, 12, 15, 18, 20, 36, 45, 75, 100 → {divides, remainder, steps}.
 */
export function ntDivisibilityRule(n, d) {
    const N = big(n);
    const D = Number(d);
    const s = babs(N).toString();
    const remainder = bmod(N, BigInt(D || 1));
    if (RULE_BASES.includes(D)) {
        const r = ruleFor(s, D);
        return {
            divides: r.divides,
            remainder,
            steps: [
                step({ title: msg('numbers.theory.divisibility.test_for', { D }), tex: r.tex, text: r.text, rule: `div-${D}` }),
                step({ title: msg('numbers.theory.divisibility.why_it_works'), text: r.why, rule: 'why' }),
            ],
        };
    }
    if (RULE_COMBOS[D]) {
        const [p, q] = RULE_COMBOS[D];
        const a = ruleFor(s, p),
            b = ruleFor(s, q);
        const ok = a.divides && b.divides;
        return {
            divides: ok,
            remainder,
            steps: [
                step({
                    title: msg('numbers.theory.divisibility.divisible_by_means_divisible_by_and', { D, p, q }),
                    tex: `${D} = ${p} \\cdot ${q}`,
                    text: msg('numbers.theory.divisibility.and_are_coprime_so_number_is', { p, q, D }),
                    rule: 'combo',
                }),
                step({
                    title: msg('numbers.theory.divisibility.test_for_2', { p }),
                    tex: a.tex,
                    text: a.text,
                    rule: `div-${p}`,
                    sub: [step({ title: msg('numbers.theory.divisibility.why_it_works'), text: a.why })],
                }),
                step({
                    title: msg('numbers.theory.divisibility.test_for_3', { q }),
                    tex: b.tex,
                    text: b.text,
                    rule: `div-${q}`,
                    sub: [step({ title: msg('numbers.theory.divisibility.why_it_works'), text: b.why })],
                }),
                step({
                    title: msg('numbers.theory.divisibility.conclusion'),
                    text: ok
                        ? msg('numbers.theory.divisibility.both_tests_pass_is_divisible_by', { N: sn(N), D })
                        : msg('numbers.theory.divisibility.at_least_one_test_fails_is', { N: sn(N), D }),
                    rule: 'answer',
                }),
            ],
        };
    }
    throw fail(msg('numbers.theory.divisibility.there_is_no_divisibility_rule_for', { D }), 'unsupported');
}
