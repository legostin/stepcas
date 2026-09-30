// theory/bases — positional number systems: conversions with steps.

import { Q } from '../../core/rational.js';
import { S, babs, fail, gcdCore, ratOf, sn, subscript, tn } from './common.js';
import { msg, notation, eachLanguage } from '../../i18n/index.js';

// ---------------------------------------------------------------- number bases

const DIGITS = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ';
export function needBase(base) {
    const b = Number(base);
    if (!Number.isInteger(b) || b < 2 || b > 36) throw fail(msg('numbers.theory.bases.base_must_be_integer_from_2'), 'base');
    return b;
}

/** A rational for explanations: 0{,}2 when it is a short finite decimal, else \frac{1}{3}. */
function qTex(num, den, lang) {
    const g0 = gcdCore(num, den) || 1n;
    num /= g0;
    den /= g0;
    let d = den;
    while (d % 2n === 0n) d /= 2n;
    while (d % 5n === 0n) d /= 5n;
    if (d === 1n) {
        let k = 0;
        while (10n ** BigInt(k) % den !== 0n) k++;
        if (k <= 12) {
            let s = (babs(num) * (10n ** BigInt(k) / den)).toString();
            if (k) {
                s = s.padStart(k + 1, '0');
                s = `${s.slice(0, -k)}${notation(lang).decimalTex}${s.slice(-k)}`;
            }
            return (num < 0n ? '-' : '') + s;
        }
    }
    return `${num < 0n ? '-' : ''}\\frac{${tn(babs(num))}}{${tn(den)}}`;
}
const qText = (num, den, lang) =>
    qTex(num, den, lang)
        .replace('{,}', ',')
        .replace(/\\frac\{(.*?)\}\{(.*?)\}/, '$1/$2')
        .replace(/\\,/g, '\u202f');

/**
 * Convert to base 2–36: integers by repeated division, fractions by repeated multiplication with
 * period detection — ntToBase('0.1', 2) === '0.0(0011)'. {maxDigits} caps the fractional digits (60).
 * {steps: true} → {value, int, pre, period, truncated, negative, tex: {ru, en}, steps}.
 */
export function ntToBase(x, base, opts = {}) {
    const b = needBase(base),
        B = BigInt(b);
    const { num, den } = ratOf(x);
    const an = babs(num);
    const I = an / den;
    let F = an % den;
    const intDigits = [];
    const divRows = [];
    if (I === 0n) intDigits.push('0');
    else {
        let n = I;
        while (n > 0n) {
            const q = n / B,
                r = n % B;
            divRows.push({ n, q, r });
            intDigits.push(DIGITS[Number(r)]);
            n = q;
        }
        intDigits.reverse();
    }
    const intStr = intDigits.join('');
    const maxDigits = opts.maxDigits ?? 60;
    const fracRows = [];
    const seen = new Map();
    let frac = '',
        periodStart = -1,
        truncated = false;
    while (F !== 0n) {
        if (seen.has(F)) {
            periodStart = seen.get(F);
            break;
        }
        if (frac.length >= maxDigits) {
            truncated = true;
            break;
        }
        seen.set(F, frac.length);
        const prod = F * B;
        const dgt = prod / den;
        fracRows.push({ num: F, den, prod, digit: Number(dgt), rest: prod % den });
        frac += DIGITS[Number(dgt)];
        F = prod % den;
    }
    const pre = periodStart >= 0 ? frac.slice(0, periodStart) : frac;
    const period = periodStart >= 0 ? frac.slice(periodStart) : '';
    const sign = num < 0n ? '-' : '';
    const value = sign + intStr + (frac ? '.' + pre + (period ? `(${period})` : '') + (truncated ? '…' : '') : '');
    if (!opts.steps) return value;

    const texOf = (l) => {
        const sep = notation(l).decimalTex;
        const f = frac ? sep + pre + (period ? `(${period})` : '') + (truncated ? '\\ldots' : '') : '';
        return `${sign}${intStr}${f}_{${b}}`;
    };
    const st = [];
    const isInt = den === 1n;
    st.push(
        S(
            msg('numbers.theory.bases.plan'),
            null,
            !isInt
                ? msg('numbers.theory.bases.we_convert_to_base_integer_and', { num: (lng) => qText(num, den, lng), b })
                : msg('numbers.theory.bases.we_convert_to_base_divide_by', { num: sn(num), b }),
            { rule: 'base-plan' },
        ),
    );
    if (sign) st.push(S(msg('numbers.theory.bases.sign'), null, msg('numbers.theory.bases.we_convert_absolute_value_and_put')));
    if (divRows.length) {
        const shown = divRows.length <= 64;
        const head = (l) => msg('numbers.theory.bases.n_n_remainder', { b }).in(l);
        const cell = (r) => (b > 10 && r >= 10n ? `${tn(r)} = \\mathrm{${DIGITS[Number(r)]}}` : tn(r));
        st.push(
            S(
                msg('numbers.theory.bases.by', {
                    p: (lng) => (isInt ? msg('numbers.theory.bases.divide').in(lng) : msg('numbers.theory.bases.integer_part_divide').in(lng)),
                    b,
                }),
                shown
                    ? eachLanguage(
                          (l) =>
                              `\\begin{array}{r|r|c} ${head(l)} \\\\ \\hline ${divRows.map((r) => `${tn(r.n)} & ${tn(r.q)} & ${cell(r.r)}`).join(' \\\\ ')} \\end{array}`,
                      )
                    : null,
                msg('numbers.theory.bases.read_from_bottom_to_top_remainders', {
                    p: (lng) => (isInt ? '' : msg('numbers.theory.bases.of_integer_part').in(lng)),
                    intStr,
                    b: subscript(b),
                    p2: (lng) => (b > 10 ? msg('numbers.theory.bases.remainders_of_10_and_more_are').in(lng) : ''),
                }),
                { rule: 'repeated-division', rows: divRows },
            ),
        );
    } else if (!isInt) {
        st.push(S(msg('numbers.theory.bases.integer_part'), null, msg('numbers.theory.bases.integer_part_is_zero')));
    }
    if (fracRows.length) {
        const shown = fracRows.slice(0, 40);
        const tail = period
            ? msg('numbers.theory.bases.fractional_part_has_appeared_before_so', { p: (lng) => qText(fracRows[periodStart].num, den, lng), period })
            : truncated
              ? msg('numbers.theory.bases.expansion_has_not_ended_after_digits', { maxDigits })
              : msg('numbers.theory.bases.fractional_part_became_zero_so_we');
        st.push(
            S(
                msg('numbers.theory.bases.fractional_part_multiply_by', { b }),
                eachLanguage(
                    (l) =>
                        `\\begin{array}{l|c} ${shown.map((r) => `${qTex(r.num, r.den, l)} \\cdot ${b} = ${qTex(r.prod, r.den, l)} & ${DIGITS[r.digit]}`).join(' \\\\ ')}${fracRows.length > shown.length ? ' \\\\ \\ldots &' : ''} \\end{array}`,
                ),
                msg('numbers.theory.bases.each_time_integer_part_of_product', { b, p: tail }),
                { rule: 'repeated-multiplication', rows: fracRows },
            ),
        );
    }
    st.push(
        S(
            msg('numbers.theory.bases.answer'),
            eachLanguage((l) => `${qTex(num, den, l)} = ${texOf(l)}`),
            period ? msg('numbers.theory.bases.digits_in_brackets_repeat_forever') : null,
            { rule: 'answer' },
        ),
    );
    return { value, int: intStr, pre, period, truncated, negative: !!sign, tex: eachLanguage(texOf, { compact: false }), steps: st };
}

/**
 * Read a numeral in base 2–36: '1A.8' (point or comma), optional sign, optional period '0.(3)'.
 * Returns a BigInt for integers and a Q for fractions. {steps: true} → {value, steps}
 * (place-value expansion, Horner's scheme for long integer parts, the period rule).
 */
export function ntFromBase(str, base, opts = {}) {
    const b = needBase(base),
        B = BigInt(b);
    const s = String(str)
        .replace(/[\s_\u00a0\u202f]/g, '')
        .replace(/^[−–]/, '-')
        .toUpperCase();
    const m = s.match(/^([+-]?)([0-9A-Z]*)(?:[.,]([0-9A-Z]*)(?:\(([0-9A-Z]+)\))?)?$/);
    if (!m || (!m[2] && !m[3] && !m[4])) throw fail(msg('numbers.theory.bases.is_not_numeral', { str }), 'syntax');
    const [, sg, ip, fp = '', per = ''] = m;
    for (const ch of ip + fp + per) {
        if (DIGITS.indexOf(ch) >= b) {
            throw fail(msg('numbers.theory.bases.there_is_no_digit_in_base', { ch, b, p: DIGITS[b - 1] }), 'digit');
        }
    }
    const val = (d) => BigInt(DIGITS.indexOf(d));
    let I = 0n;
    for (const ch of ip) I = I * B + val(ch);
    let num = I,
        den = 1n;
    if (fp || per) {
        let P = 0n;
        for (const ch of fp) P = P * B + val(ch);
        const k = B ** BigInt(fp.length);
        if (per) {
            let R = 0n;
            for (const ch of per) R = R * B + val(ch);
            const L1 = B ** BigInt(per.length) - 1n; // value = I + (P + R / L1) / B^k
            den = k * L1;
            num = I * den + P * L1 + R;
        } else {
            den = k;
            num = I * den + P;
        }
    }
    if (sg === '-') num = -num;
    const q = new Q(num, den);
    const value = q.isInt() ? q.n : q;
    if (!opts.steps) return value;
    const st = [];
    const letters = [...new Set((ip + fp + per).split('').filter((c) => DIGITS.indexOf(c) >= 10))];
    const terms = [];
    ip.split('').forEach((ch, i) => terms.push({ d: val(ch), k: ip.length - 1 - i }));
    fp.split('').forEach((ch, i) => terms.push({ d: val(ch), k: -(i + 1) }));
    const nz = terms.filter((t) => t.d !== 0n);
    const valTex = (l) => (q.isInt() ? tn(q.n) : qTex(q.n, q.d, l));
    const neg = sg === '-';
    const src = (l) => `${neg ? '-' : ''}${ip || '0'}${fp || per ? notation(l).decimalTex + fp : ''}${per ? `(${per})` : ''}_{${b}}`;
    if (!per && terms.length && terms.length <= 24) {
        st.push(
            S(
                msg('numbers.theory.bases.expand_by_place_value'),
                eachLanguage((l) => {
                    const wrap = (x) => (neg ? `-(${x})` : x);
                    const sum = nz.map((t) => `${tn(t.d)} \\cdot ${b}^{${t.k}}`).join(' + ') || '0';
                    const vals = nz.map((t) => (t.k >= 0 ? tn(t.d * B ** BigInt(t.k)) : qTex(t.d, B ** BigInt(-t.k), l))).join(' + ') || '0';
                    return `${src(l)} = ${wrap(sum)} = ${wrap(vals)} = ${valTex(l)}`;
                }),
                msg('numbers.theory.bases.digit_in_place_k_counting_from', {
                    b,
                    p: (lng) =>
                        letters.length
                            ? msg('numbers.theory.bases.letters_are_digits_above_9', { p: letters.map((c) => `${c} = ${DIGITS.indexOf(c)}`).join(', ') }).in(
                                  lng,
                              )
                            : '',
                }),
                { rule: 'positional' },
            ),
        );
    }
    if (ip.length >= 4 && ip.length <= 40) {
        let acc = 0n;
        const parts = [];
        for (const ch of ip) {
            acc = acc * B + val(ch);
            parts.push(acc);
        }
        st.push(
            S(
                msg('numbers.theory.bases.faster_horner_s_scheme'),
                parts.map((p, i) => (i === 0 ? tn(p) : `${tn(parts[i - 1])} \\cdot ${b} + ${tn(val(ip[i]))} = ${tn(p)}`)).join(',\\quad '),
                msg('numbers.theory.bases.go_through_digits_from_left_to', { b }),
                { rule: 'horner' },
            ),
        );
    }
    if (per) {
        st.push(
            S(
                msg('numbers.theory.bases.repeating_fraction'),
                eachLanguage((l) => `${src(l)} = ${valTex(l)}`),
                msg('numbers.theory.bases.period_has_digit_shifting_point_by', { length: per.length, b, per, b2: subscript(b) }),
                { rule: 'period' },
            ),
        );
    }
    st.push(
        S(
            msg('numbers.theory.bases.answer'),
            eachLanguage((l) => `${src(l)} = ${valTex(l)}`),
            null,
            { rule: 'answer' },
        ),
    );
    return { value, steps: st };
}
