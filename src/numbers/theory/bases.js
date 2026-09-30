// theory/bases — positional number systems: conversions with steps.

import { Q } from '../../core/rational.js';
import { L, S, T, babs, fail, gcdCore, ratOf, sn, subscript, tn } from './common.js';

// ---------------------------------------------------------------- number bases

const DIGITS = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ';
export function needBase(base) {
    const b = Number(base);
    if (!Number.isInteger(b) || b < 2 || b > 36) throw fail('Основание системы счисления — целое число от 2 до 36.', 'The base must be an integer from 2 to 36.', 'base');
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
        while ((10n ** BigInt(k)) % den !== 0n) k++;
        if (k <= 12) {
            let s = (babs(num) * (10n ** BigInt(k) / den)).toString();
            if (k) {
                s = s.padStart(k + 1, '0');
                s = `${s.slice(0, -k)}${lang === 'ru' ? '{,}' : '.'}${s.slice(-k)}`;
            }
            return (num < 0n ? '-' : '') + s;
        }
    }
    return `${num < 0n ? '-' : ''}\\frac{${tn(babs(num))}}{${tn(den)}}`;
}
const qText = (num, den, lang) => qTex(num, den, lang).replace('{,}', ',').replace(/\\frac\{(.*?)\}\{(.*?)\}/, '$1/$2').replace(/\\,/g, ' ');

/**
 * Convert to base 2–36: integers by repeated division, fractions by repeated multiplication with
 * period detection — ntToBase('0.1', 2) === '0.0(0011)'. {maxDigits} caps the fractional digits (60).
 * {steps: true} → {value, int, pre, period, truncated, negative, tex: {ru, en}, steps}.
 */
export function ntToBase(x, base, opts = {}) {
    const b = needBase(base), B = BigInt(b);
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
            const q = n / B, r = n % B;
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
    let frac = '', periodStart = -1, truncated = false;
    while (F !== 0n) {
        if (seen.has(F)) { periodStart = seen.get(F); break; }
        if (frac.length >= maxDigits) { truncated = true; break; }
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
        const sep = l === 'ru' ? '{,}' : '.';
        const f = frac ? sep + pre + (period ? `(${period})` : '') + (truncated ? '\\ldots' : '') : '';
        return `${sign}${intStr}${f}_{${b}}`;
    };
    const st = [];
    const isInt = den === 1n;
    st.push(S(L('Что делаем', 'The plan'), null,
        !isInt
            ? L(`Переводим ${qText(num, den, 'ru')} в систему с основанием ${b}. Целую и дробную части переводим отдельно: целую — делением на ${b}, дробную — умножением на ${b}.`,
                `We convert ${qText(num, den, 'en')} to base ${b}. The integer and fractional parts are converted separately: the integer part by dividing by ${b}, the fractional part by multiplying by ${b}.`)
            : L(`Переводим ${sn(num)} в систему с основанием ${b}: делим на ${b} с остатком, пока не получим 0. Остатки — это цифры числа, начиная с последней.`,
                `We convert ${sn(num)} to base ${b}: divide by ${b} with remainder until we reach 0. The remainders are the digits, starting from the last one.`),
        { rule: 'base-plan' }));
    if (sign) st.push(S(L('Знак', 'The sign'), null, L('Переводим модуль числа, минус ставим в конце.', 'We convert the absolute value and put the minus sign back at the end.')));
    if (divRows.length) {
        const shown = divRows.length <= 64;
        const head = (l) => (l === 'ru' ? `n & n : ${b} & \\text{остаток}` : `n & n \\div ${b} & \\text{remainder}`);
        const cell = (r) => (b > 10 && r >= 10n ? `${tn(r)} = \\mathrm{${DIGITS[Number(r)]}}` : tn(r));
        st.push(S(L(`${isInt ? 'Делим' : 'Целая часть: делим'} на ${b}`, `${isInt ? 'Divide' : 'Integer part: divide'} by ${b}`),
            shown ? T((l) => `\\begin{array}{r|r|c} ${head(l)} \\\\ \\hline ${divRows.map((r) => `${tn(r.n)} & ${tn(r.q)} & ${cell(r.r)}`).join(' \\\\ ')} \\end{array}`) : null,
            L(`Остатки, прочитанные снизу вверх, — цифры${isInt ? '' : ' целой части'}: ${intStr}${subscript(b)}.${b > 10 ? ' Остатки от 10 и больше записываем буквами: A = 10, B = 11, …' : ''}`,
                `Read from bottom to top, the remainders are the digits${isInt ? '' : ' of the integer part'}: ${intStr}${subscript(b)}.${b > 10 ? ' Remainders of 10 and more are written as letters: A = 10, B = 11, …' : ''}`),
            { rule: 'repeated-division', rows: divRows }));
    } else if (!isInt) {
        st.push(S(L('Целая часть', 'Integer part'), null, L('Целая часть равна нулю.', 'The integer part is zero.')));
    }
    if (fracRows.length) {
        const shown = fracRows.slice(0, 40);
        const tail = period
            ? L(` Дробная часть ${qText(fracRows[periodStart].num, den, 'ru')} уже встречалась — дальше цифры пойдут по кругу, период (${period}).`,
                ` The fractional part ${qText(fracRows[periodStart].num, den, 'en')} has appeared before, so the digits repeat from here on: the period is (${period}).`)
            : truncated ? L(` Дробь не закончилась за ${maxDigits} цифр — останавливаемся.`, ` The expansion has not ended after ${maxDigits} digits, so we stop.`)
                : L(' Дробная часть стала нулём — перевод закончен.', ' The fractional part became zero, so we are done.');
        st.push(S(L(`Дробная часть: умножаем на ${b}`, `Fractional part: multiply by ${b}`),
            T((l) => `\\begin{array}{l|c} ${shown.map((r) => `${qTex(r.num, r.den, l)} \\cdot ${b} = ${qTex(r.prod, r.den, l)} & ${DIGITS[r.digit]}`).join(' \\\\ ')}${fracRows.length > shown.length ? ' \\\\ \\ldots &' : ''} \\end{array}`),
            L(`Каждый раз целая часть произведения — очередная цифра после запятой, а дробную часть снова умножаем на ${b}.${tail.ru}`,
                `Each time the integer part of the product is the next digit after the point, and we multiply the fractional part by ${b} again.${tail.en}`),
            { rule: 'repeated-multiplication', rows: fracRows }));
    }
    st.push(S(L('Ответ', 'Answer'), T((l) => `${qTex(num, den, l)} = ${texOf(l)}`),
        period ? L('Цифры в скобках повторяются бесконечно.', 'The digits in brackets repeat forever.') : null, { rule: 'answer' }));
    return { value, int: intStr, pre, period, truncated, negative: !!sign, tex: T(texOf), steps: st };
}

/**
 * Read a numeral in base 2–36: '1A.8' (point or comma), optional sign, optional period '0.(3)'.
 * Returns a BigInt for integers and a Q for fractions. {steps: true} → {value, steps}
 * (place-value expansion, Horner's scheme for long integer parts, the period rule).
 */
export function ntFromBase(str, base, opts = {}) {
    const b = needBase(base), B = BigInt(b);
    const s = String(str).replace(/[\s_  ]/g, '').replace(/^[−–]/, '-').toUpperCase();
    const m = s.match(/^([+-]?)([0-9A-Z]*)(?:[.,]([0-9A-Z]*)(?:\(([0-9A-Z]+)\))?)?$/);
    if (!m || (!m[2] && !m[3] && !m[4])) throw fail(`«${str}» — не запись числа.`, `"${str}" is not a numeral.`, 'syntax');
    const [, sg, ip, fp = '', per = ''] = m;
    for (const ch of ip + fp + per) {
        if (DIGITS.indexOf(ch) >= b) {
            throw fail(`Цифры «${ch}» нет в системе с основанием ${b}: там цифры от 0 до ${DIGITS[b - 1]}.`,
                `There is no digit "${ch}" in base ${b}: its digits go from 0 to ${DIGITS[b - 1]}.`, 'digit');
        }
    }
    const val = (d) => BigInt(DIGITS.indexOf(d));
    let I = 0n;
    for (const ch of ip) I = I * B + val(ch);
    let num = I, den = 1n;
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
    const src = (l) => `${neg ? '-' : ''}${ip || '0'}${fp || per ? (l === 'ru' ? '{,}' : '.') + fp : ''}${per ? `(${per})` : ''}_{${b}}`;
    if (!per && terms.length && terms.length <= 24) {
        st.push(S(L('Раскладываем по разрядам', 'Expand by place value'),
            T((l) => {
                const wrap = (x) => (neg ? `-(${x})` : x);
                const sum = nz.map((t) => `${tn(t.d)} \\cdot ${b}^{${t.k}}`).join(' + ') || '0';
                const vals = nz.map((t) => (t.k >= 0 ? tn(t.d * B ** BigInt(t.k)) : qTex(t.d, B ** BigInt(-t.k), l))).join(' + ') || '0';
                return `${src(l)} = ${wrap(sum)} = ${wrap(vals)} = ${valTex(l)}`;
            }),
            L(`Цифра в разряде номер k (справа налево от нуля, после запятой — отрицательные номера) означает «цифра · ${b}^k»; нули можно пропустить.${letters.length ? ` Буквы — это цифры больше 9: ${letters.map((c) => `${c} = ${DIGITS.indexOf(c)}`).join(', ')}.` : ''}`,
                `A digit in place k (counting from zero right to left, negative after the point) stands for "digit · ${b}^k"; zeros can be skipped.${letters.length ? ` Letters are digits above 9: ${letters.map((c) => `${c} = ${DIGITS.indexOf(c)}`).join(', ')}.` : ''}`),
            { rule: 'positional' }));
    }
    if (ip.length >= 4 && ip.length <= 40) {
        let acc = 0n;
        const parts = [];
        for (const ch of ip) { acc = acc * B + val(ch); parts.push(acc); }
        st.push(S(L('Быстрее — схемой Горнера', "Faster: Horner's scheme"),
            parts.map((p, i) => (i === 0 ? tn(p) : `${tn(parts[i - 1])} \\cdot ${b} + ${tn(val(ip[i]))} = ${tn(p)}`)).join(',\\quad '),
            L(`Идём по цифрам слева направо: умножаем накопленное на ${b} и прибавляем следующую цифру. Так не нужно считать большие степени.`,
                `Go through the digits from left to right: multiply what you have by ${b} and add the next digit. No large powers needed.`),
            { rule: 'horner' }));
    }
    if (per) {
        st.push(S(L('Периодическая дробь', 'A repeating fraction'), T((l) => `${src(l)} = ${valTex(l)}`),
            L(`В периоде ${per.length} ${per.length === 1 ? 'цифра' : per.length <= 4 ? 'цифры' : 'цифр'}. Если сдвинуть запятую на столько же разрядов (умножить на ${b}^${per.length}) и вычесть исходное число, бесконечные хвосты сократятся. Поэтому период ${per}${subscript(b)} даёт дробь со знаменателем ${b}^${per.length} − 1.`,
                `The period has ${per.length} digit${per.length === 1 ? '' : 's'}. Shifting the point by as many places (multiplying by ${b}^${per.length}) and subtracting the original number cancels the infinite tails. So the period ${per}${subscript(b)} gives a fraction with denominator ${b}^${per.length} − 1.`),
            { rule: 'period' }));
    }
    st.push(S(L('Ответ', 'Answer'), T((l) => `${src(l)} = ${valTex(l)}`), null, { rule: 'answer' }));
    return { value, steps: st };
}
