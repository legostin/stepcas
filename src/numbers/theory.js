// numtheory — number theory on BigInt with bilingual step-by-step explanations.
//
// Inputs: BigInt, integer numbers, digit strings ("600 851 475 143"), and — where a fraction makes
// sense — Q, "a/b", "0,1", "0.(3)". Outputs: BigInt (or arrays/objects of BigInt).
// Convention: a function returns its bare value; called with {steps: true} it returns
// {value, steps, ...extra}. Functions whose natural result is already an object (ntEgcd,
// ntDiophantine, ntSolveCongruence, ntCrt, ntMillerRabin, ntContinuedFraction, ntRsaKey,
// ntDivisibilityRule) just gain a `steps` field. Step shape: {title: {ru, en}, tex?, text?, rule?, sub?}.

import { MathError, Q, bigIsqrt, bigIroot } from '../core/rational.js';

// ---------------------------------------------------------------- tiny internal helpers

const L = (ru, en) => ({ ru, en });
const T = (f) => ({ ru: f('ru'), en: f('en') });
const fail = (ru, en, code = null) => new MathError({ ru, en }, null, null, code);

function S(title, tex, text, extra) {
    const s = { title };
    if (tex != null) s.tex = tex;
    if (text != null) s.text = text;
    if (extra) Object.assign(s, extra);
    if (Array.isArray(s.sub) && !s.sub.length) delete s.sub;
    return s;
}

const babs = (a) => (a < 0n ? -a : a);
const bmod = (a, m) => ((a % m) + m) % m;

function grp(d, sep) {
    return d.length <= 4 ? d : d.replace(/\B(?=(\d{3})+(?!\d))/g, sep);
}
/** TeX for an integer: 600\,851\,475\,143 (groups from five digits on). */
function tn(n) {
    const s = String(n);
    return s[0] === '-' ? '-' + grp(s.slice(1), '\\,') : grp(s, '\\,');
}
/** TeX, parenthesised when negative (for products). */
function tp(n) {
    return String(n)[0] === '-' ? `(${tn(n)})` : tn(n);
}
/** Plain text for an integer: narrow no-break spaces between groups, a real minus sign. */
function sn(n) {
    const s = String(n);
    return s[0] === '-' ? '−' + grp(s.slice(1), ' ') : grp(s, ' ');
}
/** A decimal approximation: comma in Russian, point in English; `tex` gives {,}. */
function dec(x, digits, lang, tex = false) {
    let s = Number(x).toFixed(digits);
    if (s.includes('.')) s = s.replace(/0+$/, '').replace(/\.$/, '');
    if (lang === 'ru') s = s.replace('.', tex ? '{,}' : ',');
    return tex ? s : s.replace('-', '−');
}
/** Russian plural: ruPl(5, 'решение', 'решения', 'решений') → 'решений'. */
function ruPl(n, one, few, many) {
    const a = Number(n < 0 ? -n : n) % 100, b = a % 10;
    if (a >= 11 && a <= 14) return many;
    return b === 1 ? one : b >= 2 && b <= 4 ? few : many;
}
const SUBS = '₀₁₂₃₄₅₆₇₈₉';
const subscript = (n) => String(n).split('').map((c) => SUBS[+c]).join('');
/** k·x in TeX with the coefficient 1 / −1 hidden. */
const coefX = (a, v = 'x') => (a === 1n ? v : a === -1n ? `-${v}` : `${tn(a)}${v}`);

/** «3, 5 и 7» / «3, 5, 7, …, 67» */
function listText(items, lang) {
    const a = items.map(sn);
    if (a.length === 1) return a[0];
    if (a.length <= 4) return a.slice(0, -1).join(', ') + (lang === 'ru' ? ' и ' : ' and ') + a[a.length - 1];
    return `${a[0]}, ${a[1]}, ${a[2]}, …, ${a[a.length - 1]}`;
}

const G = (l, a, b) => (l === 'ru' ? `\\text{НОД}(${tn(a)},\\,${tn(b)})` : `\\gcd(${tn(a)}, ${tn(b)})`);
const Lc = (l, a, b) => (l === 'ru' ? `\\text{НОК}(${tn(a)},\\,${tn(b)})` : `\\operatorname{lcm}(${tn(a)}, ${tn(b)})`);
const gT = (l, a, b) => (l === 'ru' ? `НОД(${sn(a)}, ${sn(b)})` : `gcd(${sn(a)}, ${sn(b)})`);

/** Anything integer-like → BigInt. */
function big(x, what) {
    if (typeof x === 'bigint') return x;
    if (typeof x === 'number') {
        if (Number.isInteger(x)) return BigInt(x);
        throw fail(`Нужно целое число${what ? ` (${what})` : ''}, а получено ${String(x).replace('.', ',')}.`,
            `An integer is required${what ? ` (${what})` : ''}, got ${x}.`, 'not-int');
    }
    if (typeof x === 'string') {
        const s = x.replace(/[\s_   ']/g, '').replace(/^[−–]/, '-');
        if (/^[+-]?\d+$/.test(s)) return BigInt(s);
        throw fail(`«${x}» — не целое число.`, `"${x}" is not an integer.`, 'not-int');
    }
    if (x instanceof Q) {
        if (x.isInt()) return x.n;
        throw fail('Нужно целое число, а получена дробь.', 'An integer is required, not a fraction.', 'not-int');
    }
    throw fail('Нужно целое число.', 'An integer is required.', 'not-int');
}

/** Exact value of a double as {num, den}. */
function doubleExact(x) {
    const dv = new DataView(new ArrayBuffer(8));
    dv.setFloat64(0, x);
    const hi = dv.getUint32(0), lo = dv.getUint32(4);
    const exp = (hi >>> 20) & 0x7ff;
    let mant = (BigInt(hi & 0xfffff) << 32n) | BigInt(lo);
    let e;
    if (exp === 0) e = -1074;
    else { mant |= 1n << 52n; e = exp - 1075; }
    let num = mant, den = 1n;
    if (e > 0) num <<= BigInt(e);
    else den <<= BigInt(-e);
    while (num % 2n === 0n && den % 2n === 0n && den > 1n) { num /= 2n; den /= 2n; }
    return { num: hi >>> 31 ? -num : num, den };
}

/** Anything rational-like → {num, den}, reduced, den > 0. */
function ratOf(x) {
    if (typeof x === 'bigint') return { num: x, den: 1n };
    if (x instanceof Q) return { num: x.n, den: x.d };
    if (typeof x === 'number' || typeof x === 'string') {
        const q = Q.of(x);
        return { num: q.n, den: q.d };
    }
    if (x && typeof x === 'object' && typeof x.num === 'bigint' && typeof x.den === 'bigint') {
        const q = new Q(x.num, x.den);
        return { num: q.n, den: q.d };
    }
    throw fail('Нужно число.', 'A number is required.', 'nan');
}

function gcdCore(a, b) {
    a = babs(a); b = babs(b);
    while (b) [a, b] = [b, a % b];
    return a;
}

function powmod(b, e, m) {
    if (m === 1n) return 0n;
    let r = 1n;
    b = bmod(b, m);
    while (e > 0n) {
        if (e & 1n) r = (r * b) % m;
        e >>= 1n;
        if (e) b = (b * b) % m;
    }
    return r;
}

/** Inverse modulo m in [0, m), or null when gcd ≠ 1. */
function invCore(a, m) {
    if (m === 1n) return 0n;
    let [r0, r1] = [bmod(a, m), m];
    let [s0, s1] = [1n, 0n];
    while (r1) {
        const q = r0 / r1;
        [r0, r1] = [r1, r0 - q * r1];
        [s0, s1] = [s1, s0 - q * s1];
    }
    return r0 === 1n ? bmod(s0, m) : null;
}

function sieveBytes(n) {
    const comp = new Uint8Array(n + 1);
    comp[0] = 1;
    if (n >= 1) comp[1] = 1;
    for (let i = 2; i * i <= n; i++) if (!comp[i]) for (let j = i * i; j <= n; j += i) comp[j] = 1;
    return comp;
}
const TRIAL = 10000;
const SMALL = (() => {
    const c = sieveBytes(TRIAL);
    const out = [];
    for (let i = 2; i <= TRIAL; i++) if (!c[i]) out.push(i);
    return out;
})();
const SMALL_BIG = SMALL.map(BigInt);

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

function gcdSteps(A, B) {
    const st = [];
    let x = babs(A), y = babs(B);
    if (x === 0n && y === 0n) {
        st.push(S(L('НОД двух нулей', 'The gcd of two zeros'), T((l) => `${G(l, 0, 0)} = 0`),
            L('Ноль делится на любое число, так что наибольшего общего делителя у двух нулей нет. По соглашению НОД(0, 0) = 0 — так формулы остаются простыми.',
                'Zero is divisible by every number, so two zeros have no largest common divisor. By convention gcd(0, 0) = 0, which keeps formulas simple.'),
            { rule: 'gcd-zero' }));
        return { st, rows: [], g: 0n };
    }
    if (A < 0n || B < 0n) {
        st.push(S(L('Знак не важен', 'Signs do not matter'), T((l) => `${G(l, A, B)} = ${G(l, x, y)}`),
            L('У числа и у противоположного ему делители одни и те же, поэтому берём модули.',
                'A number and its negative have the same divisors, so we work with absolute values.'),
            { rule: 'gcd-abs' }));
    }
    if (x === 0n || y === 0n) {
        const n = x || y;
        st.push(S(L('Одно из чисел — ноль', 'One of the numbers is zero'), T((l) => `${G(l, x, y)} = ${tn(n)}`),
            L(`Ноль делится на что угодно, поэтому общие делители — это просто делители числа ${sn(n)}. Наибольший из них — само ${sn(n)}.`,
                `Zero is divisible by anything, so the common divisors are just the divisors of ${sn(n)}; the largest is ${sn(n)} itself.`),
            { rule: 'gcd-zero' }));
        return { st, rows: [], g: n };
    }
    const swapped = x < y;
    if (swapped) [x, y] = [y, x];
    const rows = euclidRows(x, y);
    const g = rows[rows.length - 1].b;
    st.push(S(L('Алгоритм Евклида', "Euclid's algorithm"),
        T((l) => `a = q \\cdot b + r \\;\\Rightarrow\\; ${l === 'ru' ? '\\text{НОД}(a,\\,b) = \\text{НОД}(b,\\,r)' : '\\gcd(a, b) = \\gcd(b, r)'}`),
        L(`Если a = q·b + r, то у пар (a, b) и (b, r) одни и те же общие делители: всё, что делит a и b, делит и r = a − q·b, и наоборот. Поэтому большее число можно заменить остатком от деления на меньшее — НОД не изменится. Повторяем, пока остаток не станет нулём.${swapped ? ` Начинаем с большего числа, ${sn(x)}.` : ''}`,
            `If a = q·b + r, the pairs (a, b) and (b, r) have exactly the same common divisors: anything dividing a and b also divides r = a − q·b, and vice versa. So we may replace the larger number by the remainder of dividing it by the smaller one — the gcd stays the same. We repeat until the remainder is zero.${swapped ? ` We start with the larger number, ${sn(x)}.` : ''}`),
        { rule: 'euclid' }));
    for (const { a, b, q, r } of rows) {
        st.push(S(L(`Делим ${sn(a)} на ${sn(b)}`, `Divide ${sn(a)} by ${sn(b)}`),
            `${tn(a)} = ${tn(q)} \\cdot ${tn(b)} + ${tn(r)}`,
            r > 0n
                ? L(`Получаем ${sn(q)}, остаток ${sn(r)}. Значит, НОД(${sn(a)}, ${sn(b)}) = НОД(${sn(b)}, ${sn(r)}).`,
                    `Quotient ${sn(q)}, remainder ${sn(r)}. So gcd(${sn(a)}, ${sn(b)}) = gcd(${sn(b)}, ${sn(r)}).`)
                : L(`Делится нацело: получаем ${sn(q)}, остаток 0. Алгоритм закончен.`,
                    `It divides exactly: quotient ${sn(q)}, remainder 0. We are done.`),
            { rule: 'division', row: { a, b, q, r } }));
    }
    return { st, rows, g };
}

function gcdAnswer(A, B, g) {
    return S(L('Ответ', 'Answer'), T((l) => `${G(l, A, B)} = ${tn(g)}`),
        g === 1n
            ? L('Последний ненулевой остаток равен 1: у чисел нет общих делителей, кроме единицы, — они взаимно просты.',
                'The last non-zero remainder is 1: the numbers have no common divisor except 1 — they are coprime.')
            : L(`НОД — последний ненулевой остаток, то есть число, на которое разделилось нацело: ${sn(g)}.`,
                `The gcd is the last non-zero remainder, the number that divided exactly: ${sn(g)}.`),
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
        st.push(S(L('Одно из чисел — ноль', 'One of the numbers is zero'), T((l) => `${Lc(l, A, B)} = 0`),
            L('Единственное кратное нуля — сам ноль, поэтому НОК с нулём принято считать равным 0.',
                'The only multiple of zero is zero itself, so by convention the lcm with zero is 0.'), { rule: 'lcm-zero' }));
        return { value, steps: st };
    }
    const x = babs(A), y = babs(B);
    const gs = gcdSteps(x, y);
    st.push(S(L(`Сначала НОД: ${gT('ru', x, y)} = ${sn(g)}`, `First the gcd: ${gT('en', x, y)} = ${sn(g)}`),
        T((l) => `${G(l, x, y)} = ${tn(g)}`),
        L('Находим его алгоритмом Евклида (подробности — внутри).', "We find it by Euclid's algorithm (details inside)."),
        { rule: 'gcd', sub: [...gs.st, ...(gs.rows.length ? [gcdAnswer(x, y, g)] : [])] }));
    st.push(S(L('Делим произведение на НОД', 'Divide the product by the gcd'),
        T((l) => `${Lc(l, x, y)} = \\frac{${tn(x)} \\cdot ${tn(y)}}{${tn(g)}}${g === 1n ? '' : ` = ${tn(x / g)} \\cdot ${tn(y)}`} = ${tn(value)}`),
        L('В произведении a·b общие множители чисел встречаются дважды — деление на НОД убирает лишнюю копию. Удобнее сначала разделить одно из чисел на НОД, а потом умножить.',
            'The product a·b contains the common factors twice; dividing by the gcd removes the extra copy. It is easier to divide one number by the gcd first and multiply afterwards.'),
        { rule: 'lcm-formula' }));
    if (x <= 10n ** 15n && y <= 10n ** 15n && x > 1n && y > 1n) {
        const fx = factorMap(x), fy = factorMap(y);
        const all = new Map(fx);
        for (const [p, e] of fy) all.set(p, Math.max(all.get(p) ?? 0, e));
        const sorted = [...all.entries()].sort((u, v) => (u[0] < v[0] ? -1 : 1)).map(([p, e]) => ({ p, e }));
        st.push(S(L('Проверка через разложение', 'Check by factorisation'),
            T((l) => `${tn(x)} = ${ntFactorTex(mapToList(fx))},\\quad ${tn(y)} = ${ntFactorTex(mapToList(fy))},\\quad ${Lc(l, x, y)} = ${ntFactorTex(sorted)} = ${tn(value)}`),
            L('Другой способ: разложить оба числа на простые множители и взять каждый простой множитель в наибольшей степени, в какой он встречается.',
                'Another way: factor both numbers into primes and take every prime to the highest power in which it occurs.'),
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
    if (!list.length) throw fail('Нужно хотя бы одно число.', 'At least one number is required.');
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
            st.push(S(L(`Добавляем ${sn(xs[i])}: НОД(${sn(prev)}, ${sn(xs[i])}) = ${sn(acc)}`, `Add ${sn(xs[i])}: gcd(${sn(prev)}, ${sn(xs[i])}) = ${sn(acc)}`),
                T((l) => `${G(l, prev, xs[i])} = ${tn(acc)}`),
                i === 1 ? L('НОД нескольких чисел ищем по цепочке: НОД(a, b, c) = НОД(НОД(a, b), c). Общий делитель всех чисел — это общий делитель уже найденного НОД и следующего числа.',
                    'For several numbers we chain: gcd(a, b, c) = gcd(gcd(a, b), c). A common divisor of all the numbers is a common divisor of the gcd found so far and the next number.') : null,
                { rule: 'gcd-chain', sub: [...gs.st, ...(gs.rows.length ? [gcdAnswer(prev, xs[i], acc)] : [])] }));
        }
    }
    if (!opts.steps) return acc;
    if (xs.length === 1) st.push(S(L('Одно число', 'A single number'), tn(acc), L('НОД одного числа — его модуль.', 'The gcd of one number is its absolute value.')));
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
            st.push(S(L(`Добавляем ${sn(xs[i])}: НОК(${sn(prev)}, ${sn(xs[i])}) = ${sn(acc)}`, `Add ${sn(xs[i])}: lcm(${sn(prev)}, ${sn(xs[i])}) = ${sn(acc)}`),
                T((l) => `${Lc(l, prev, xs[i])} = ${tn(acc)}`),
                i === 1 ? L('НОК нескольких чисел ищем по цепочке: НОК(a, b, c) = НОК(НОК(a, b), c).', 'For several numbers we chain: lcm(a, b, c) = lcm(lcm(a, b), c).') : null,
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
    st.push(S(L('Сначала алгоритм Евклида', "First, Euclid's algorithm"), T((l) => `${G(l, A, B)} = ${tn(g)}`),
        L('Записываем все деления с остатком — они понадобятся на обратном ходу.', 'We write down every division with remainder: we will need them on the way back.'),
        { rule: 'euclid', sub: gs.st }));
    if (X === 0n) {
        st.push(S(L('Оба числа — нули', 'Both numbers are zero'), '0 \\cdot 0 + 0 \\cdot 0 = 0', L('Подходит любая пара; берём x = y = 0.', 'Any pair works; we take x = y = 0.')));
        return { ...res, rows, steps: st };
    }
    if (rows.length <= 1) {
        st.push(S(L('Представление готово сразу', 'The representation is immediate'),
            `${tn(g)} = ${tp(A)} \\cdot ${tp(x)} + ${tp(B)} \\cdot ${tp(y)}`,
            L(`НОД совпадает с одним из чисел (${sn(g)}), так что это число берём с коэффициентом ±1, а другое — с коэффициентом 0.`,
                `The gcd equals one of the numbers (${sn(g)}), so we take that number with coefficient ±1 and the other with coefficient 0.`),
            { rule: 'bezout' }));
    } else {
        st.push(S(L('Идём назад', 'Work backwards'), null,
            L('Выражаем НОД из предпоследнего деления, а потом по очереди подставляем выражения для остатков, поднимаясь по таблице вверх. На каждом шаге НОД записан через два соседних числа из таблицы.',
                'We express the gcd from the second-to-last division, then substitute the remainders one by one, climbing up the table. At every step the gcd is written in terms of two neighbouring numbers of the table.'),
            { rule: 'back-substitution' }));
        for (const bk of back) {
            const row = rows[bk.j];
            if (bk.first) {
                st.push(S(L(`Выражаем ${sn(g)} из деления ${sn(row.a)} на ${sn(row.b)}`, `Express ${sn(g)} from dividing ${sn(row.a)} by ${sn(row.b)}`),
                    `${tn(g)} = ${linTex(1n, row.a, -row.q, row.b)}`,
                    L(`Из равенства ${sn(row.a)} = ${sn(row.q)}·${sn(row.b)} + ${sn(g)} переносим произведение в другую часть.`,
                        `From ${sn(row.a)} = ${sn(row.q)}·${sn(row.b)} + ${sn(g)} we move the product to the other side.`),
                    { rule: 'bezout' }));
            } else {
                const nxt = rows[bk.j + 1]; // gcd = fs·nxt.a + ft·nxt.b, nxt.a = row.b, nxt.b = row.r = row.a − row.q·row.b
                const { s: fs, t: ft } = bk.from;
                const inner = row.q === 1n ? `${tn(row.a)} - ${tn(row.b)}` : `${tn(row.a)} - ${tn(row.q)} \\cdot ${tn(row.b)}`;
                const mid = `${termTex(fs, row.b, true)} ${ft < 0n ? '-' : '+'} ${babs(ft) === 1n ? '' : `${tn(babs(ft))} \\cdot `}(${inner})`;
                st.push(S(L(`Подставляем ${sn(row.r)}`, `Substitute ${sn(row.r)}`),
                    `${tn(g)} = ${linTex(fs, nxt.a, ft, nxt.b)} = ${mid} = ${linTex(bk.s, row.a, bk.t, row.b)}`,
                    L(`Из деления ${sn(row.a)} на ${sn(row.b)}: ${sn(row.r)} = ${sn(row.a)} − ${sn(row.q)}·${sn(row.b)}. Подставляем и собираем подобные.`,
                        `From dividing ${sn(row.a)} by ${sn(row.b)}: ${sn(row.r)} = ${sn(row.a)} − ${sn(row.q)}·${sn(row.b)}. Substitute and collect like terms.`),
                    { rule: 'bezout' }));
            }
        }
    }
    if (A < 0n || B < 0n) {
        st.push(S(L('Возвращаем знаки', 'Put the signs back'), null,
            L('Мы работали с модулями; у отрицательного числа меняем знак коэффициента.', 'We worked with absolute values; for a negative number we flip the sign of its coefficient.')));
    }
    st.push(S(L('Ответ и проверка', 'Answer and check'),
        `${tp(A)} \\cdot ${tp(x)} + ${tp(B)} \\cdot ${tp(y)} = ${tn(A * x)} ${B * y < 0n ? '-' : '+'} ${tn(babs(B * y))} = ${tn(g)}`,
        L(`Нашли x = ${sn(x)}, y = ${sn(y)}. Такие числа есть всегда (соотношение Безу), но пара не единственная: подойдут и x + k·${sn(B / g)}, y − k·${sn(A / g)} при любом целом k.`,
            `We found x = ${sn(x)}, y = ${sn(y)}. Such numbers always exist (Bézout's identity), but the pair is not unique: x + k·${sn(B / g)}, y − k·${sn(A / g)} works for every integer k.`),
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
            st.push(S(L('Оба коэффициента — нули', 'Both coefficients are zero'), `0 \\cdot x + 0 \\cdot y = ${tn(C)}`,
                C === 0n ? L('Подходит любая пара (x, y).', 'Every pair (x, y) works.') : L('Слева всегда 0, справа — нет: решений нет.', 'The left side is always 0 and the right side is not: no solutions.')));
            res.steps = st;
        }
        return res;
    }
    const e = ntEgcd(A, B, { steps: !!opts.steps });
    const g = e.g;
    if (C % g !== 0n) {
        const res = { solvable: false, g };
        if (opts.steps) {
            st.push(S(L(`НОД(${sn(A)}, ${sn(B)}) = ${sn(g)}`, `gcd(${sn(A)}, ${sn(B)}) = ${sn(g)}`), T((l) => `${G(l, A, B)} = ${tn(g)}`), null, { rule: 'gcd', sub: e.steps[0].sub }));
            st.push(S(L('Решений нет', 'No solutions'), `${tn(g)} \\nmid ${tn(C)}`,
                L(`При любых целых x и y левая часть делится на ${sn(g)}, а ${sn(C)} на ${sn(g)} не делится.`,
                    `For all integers x and y the left side is divisible by ${sn(g)}, but ${sn(C)} is not.`), { rule: 'answer' }));
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
    st.push(S(L('НОД и коэффициенты Безу', 'The gcd and the Bézout coefficients'),
        `${tp(A)} \\cdot ${tp(e.x)} + ${tp(B)} \\cdot ${tp(e.y)} = ${tn(g)}`,
        L('Расширенный алгоритм Евклида (подробности внутри).', 'The extended Euclidean algorithm (details inside).'), { rule: 'egcd', sub: e.steps }));
    st.push(S(L(`Умножаем на ${sn(k)}`, `Multiply by ${sn(k)}`),
        `${tp(A)} \\cdot ${tp(e.x * k)} + ${tp(B)} \\cdot ${tp(e.y * k)} = ${tn(C)}`,
        g === 1n ? L(`НОД равен 1, поэтому решение есть при любой правой части: умножаем равенство на ${sn(C)}.`,
            `The gcd is 1, so there are solutions for any right-hand side: multiply the identity by ${sn(C)}.`)
            : L(`${sn(C)} делится на НОД = ${sn(g)}, поэтому решение есть: умножаем равенство на ${sn(C)} : ${sn(g)} = ${sn(k)}.`,
                `${sn(C)} is divisible by the gcd ${sn(g)}, so solutions exist: multiply the identity by ${sn(C)} / ${sn(g)} = ${sn(k)}.`), { rule: 'scale' }));
    const part = (v0, dv) => `${tn(v0)} ${dv < 0n ? '-' : '+'} ${babs(dv) === 1n ? '' : tn(babs(dv))}k`;
    st.push(S(L('Все решения', 'All solutions'),
        `x = ${part(x0, dx)},\\quad y = ${part(y0, dy)},\\quad k \\in \\mathbb Z`,
        L(`Если к x ${dx < 0n ? `прибавить ${sn(dx)}` : `прибавить ${sn(dx)}`}, а ${dy < 0n ? `из y вычесть ${sn(-dy)}` : `к y прибавить ${sn(dy)}`}, левая часть не изменится: ${sn(A)}·${sn(dx)} + ${sn(B)}·(${sn(dy)}) = 0. Других решений нет. Здесь ${sn(x0)} — наименьшее неотрицательное x.`,
            `Adding ${sn(dx)} to x and ${dy < 0n ? `subtracting ${sn(-dy)} from` : `adding ${sn(dy)} to`} y does not change the left side: ${sn(A)}·${sn(dx)} + ${sn(B)}·(${sn(dy)}) = 0. There are no other solutions. Here ${sn(x0)} is the smallest non-negative x.`),
        { rule: 'answer' }));
    res.steps = st;
    return res;
}

// ---------------------------------------------------------------- primality

const MR_TABLE = [
    [2047n, [2n]],
    [1373653n, [2n, 3n]],
    [25326001n, [2n, 3n, 5n]],
    [3215031751n, [2n, 3n, 5n, 7n]],
    [2152302898747n, [2n, 3n, 5n, 7n, 11n]],
    [3474749660383n, [2n, 3n, 5n, 7n, 11n, 13n]],
    [341550071728321n, [2n, 3n, 5n, 7n, 11n, 13n, 17n]],
    [3825123056546413051n, [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n]],
    [318665857834031151167461n, [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n]],
    [3317044064679887385961981n, [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n]],
];
/** Below this bound the Miller–Rabin answer is proven (Sorenson–Webster, first 13 primes as bases). */
const MR_LIMIT = 3317044064679887385961981n;

function mrBases(n) {
    for (const [lim, bases] of MR_TABLE) if (n < lim) return { bases, certain: true };
    const bases = [...MR_TABLE[MR_TABLE.length - 1][1]];
    let s = (n % 1000000007n) ^ 0x9e3779b9n; // deterministic pseudo-random extra bases
    for (let i = 0; i < 24; i++) {
        s = (s * 6364136223846793005n + 1442695040888963407n) % (1n << 64n);
        bases.push(2n + (s % (n - 3n)));
    }
    return { bases, certain: false };
}

function mrRound(n, a, d, s) {
    let x = powmod(a, d, n);
    const seq = [x];
    if (x === 1n || x === n - 1n) return { a, seq, pass: true };
    for (let r = 1; r < s; r++) {
        x = (x * x) % n;
        seq.push(x);
        if (x === n - 1n) return { a, seq, pass: true };
        if (x === 1n) return { a, seq, pass: false };
    }
    return { a, seq, pass: false };
}

function isPrimeBig(n) {
    if (n < 2n) return false;
    for (const p of SMALL_BIG) {
        if (p * p > n) return true;
        if (n % p === 0n) return n === p;
        if (p > 200n) break;
    }
    let d = n - 1n, s = 0;
    while ((d & 1n) === 0n) { d >>= 1n; s++; }
    for (const a of mrBases(n).bases) {
        if (a % n === 0n) continue;
        if (!mrRound(n, a, d, s).pass) return false;
    }
    return true;
}

/** Primality: deterministic Miller–Rabin below 3.3·10²⁴, probabilistic (error < 4⁻³⁷) above. */
export function ntIsPrime(n) {
    return isPrimeBig(big(n));
}

/**
 * Miller–Rabin in detail: {prime, certain, witness, d, s, rounds: [{a, seq, pass}], steps?}.
 * {bases: [...]} tests only those bases (then a "prime" verdict is marked uncertain).
 */
export function ntMillerRabin(n, opts = {}) {
    const N = big(n);
    const res = { prime: false, certain: true, witness: null, d: null, s: null, rounds: [] };
    const st = [];
    if (N < 5n || N % 2n === 0n) {
        res.prime = N === 2n || N === 3n;
        if (opts.steps) {
            st.push(S(L('Тест не нужен', 'No test needed'), null,
                N < 2n ? L(`${sn(N)} не считается простым: простые числа начинаются с 2.`, `${sn(N)} is not prime: primes start at 2.`)
                    : res.prime ? L(`${sn(N)} — простое.`, `${sn(N)} is prime.`)
                        : L(`${sn(N)} чётное и больше 2, значит, составное.`, `${sn(N)} is even and greater than 2, so it is composite.`), { rule: 'answer' }));
            res.steps = st;
        }
        return res;
    }
    let d = N - 1n, s = 0;
    while ((d & 1n) === 0n) { d >>= 1n; s++; }
    res.d = d;
    res.s = s;
    let bases, certain;
    if (opts.bases) { bases = opts.bases.map((b) => big(b)); certain = false; }
    else ({ bases, certain } = mrBases(N));
    for (const a of bases) {
        if (bmod(a, N) === 0n) continue;
        const r = mrRound(N, a, d, s);
        res.rounds.push(r);
        if (!r.pass) { res.witness = a; break; }
    }
    res.prime = res.witness === null;
    res.certain = res.prime ? certain : true;
    if (!opts.steps) return res;
    st.push(S(L('Идея теста', 'The idea'), `${tn(N)} - 1 = 2^{${s}} \\cdot ${tn(d)}`,
        L(`Если n простое, то по малой теореме Ферма a^(n−1) ≡ 1 (mod n), а у единицы по простому модулю только два квадратных корня: 1 и −1. Раскладываем n − 1 = 2^${s}·${sn(d)} и строим цепочку a^d, a^(2d), a^(4d), …: каждое число — квадрат предыдущего. У простого n цепочка либо сразу начинается с 1, либо где-то проходит через n − 1, то есть через −1.`,
            `If n is prime, Fermat's little theorem gives a^(n−1) ≡ 1 (mod n), and modulo a prime 1 has only two square roots, 1 and −1. We write n − 1 = 2^${s}·${sn(d)} and build the chain a^d, a^(2d), a^(4d), …, each number the square of the previous one. For a prime n the chain either starts at 1 or passes through n − 1, that is −1, somewhere.`),
        { rule: 'mr-idea' }));
    for (const r of res.rounds) {
        let text;
        if (r.pass) {
            text = r.seq[0] === 1n
                ? L(`Цепочка сразу начинается с 1 — основание ${sn(r.a)} не разоблачает число.`, `The chain starts at 1 — base ${sn(r.a)} does not expose a composite.`)
                : L(`Цепочка проходит через ${sn(N - 1n)} ≡ −1 — так и должно быть у простого числа. Основание ${sn(r.a)} подозрений не вызывает.`,
                    `The chain passes through ${sn(N - 1n)} ≡ −1, just as it must for a prime. Base ${sn(r.a)} raises no suspicion.`);
        } else if (r.seq[r.seq.length - 1] === 1n) {
            const prev = r.seq[r.seq.length - 2];
            text = L(`Появилась 1, но перед ней стоит ${sn(prev)}, а не ±1. Значит, у единицы нашёлся «лишний» квадратный корень, чего по простому модулю не бывает: ${sn(N)} — составное, ${sn(r.a)} — свидетель.`,
                `We reached 1, but the number before it is ${sn(prev)}, not ±1. So 1 has an extra square root, which never happens modulo a prime: ${sn(N)} is composite and ${sn(r.a)} is a witness.`);
        } else {
            text = L(`Цепочка так и не дошла ни до 1, ни до −1. У простого n так быть не может: ${sn(N)} — составное, ${sn(r.a)} — свидетель.`,
                `The chain never reached 1 or −1, which is impossible for a prime n: ${sn(N)} is composite and ${sn(r.a)} is a witness.`);
        }
        st.push(S(L(`Основание a = ${sn(r.a)}`, `Base a = ${sn(r.a)}`), `${r.seq.map(tn).join(',\\ ')} \\pmod{${tn(N)}}`, text, { rule: r.pass ? 'mr-pass' : 'mr-witness' }));
    }
    st.push(S(L('Вывод', 'Conclusion'), null,
        !res.prime ? L(`${sn(N)} — составное число. Тест Миллера — Рабина не называет делителей, но составность доказывает.`,
            `${sn(N)} is composite. The Miller–Rabin test does not name a divisor, but it proves compositeness.`)
            : res.certain ? L(`${sn(N)} — простое. Для чисел меньше 3,3·10²⁴ такого набора оснований достаточно, ответ точный.`,
                `${sn(N)} is prime. For numbers below 3.3·10²⁴ this set of bases is known to suffice, so the answer is certain.`)
                : L(`${sn(N)}, почти наверняка, простое: ни одно из ${res.rounds.length} оснований не оказалось свидетелем. Вероятность ошибки меньше 4^(−${res.rounds.length}).`,
                    `${sn(N)} is almost certainly prime: none of the ${res.rounds.length} bases is a witness. The chance of error is below 4^(−${res.rounds.length}).`),
        { rule: 'answer' }));
    res.steps = st;
    return res;
}

/** Carmichael number (Korselt's criterion): composite, squarefree, (p − 1) | (n − 1) for every prime p | n. */
export function ntIsCarmichael(n) {
    const N = big(n);
    if (N < 3n || N % 2n === 0n || isPrimeBig(N)) return false;
    for (const [p, e] of factorMap(N)) if (e > 1 || (N - 1n) % (p - 1n) !== 0n) return false;
    return true;
}

// ---------------------------------------------------------------- factorisation

const RHO_BUDGET = 4_000_000;

function rho(n) {
    if (n % 2n === 0n) return 2n;
    let budget = RHO_BUDGET;
    for (let c = 1n; c < 200n; c++) {
        const f = (v) => (v * v + c) % n;
        let y = 2n + c, r = 1, q = 1n, g = 1n, x = 0n, ys = 0n;
        const m = 128;
        do {
            x = y;
            for (let i = 0; i < r; i++) y = f(y);
            let k = 0;
            while (k < r && g === 1n) {
                ys = y;
                const lim = Math.min(m, r - k);
                for (let i = 0; i < lim; i++) {
                    y = f(y);
                    q = (q * babs(x - y)) % n;
                }
                g = gcdCore(q, n);
                k += m;
                budget -= lim;
            }
            r *= 2;
            if (budget < 0) {
                throw fail('Число слишком трудно разложить: у него слишком большие простые множители.',
                    'This number is too hard to factor: its prime factors are too large.', 'too-big');
            }
        } while (g === 1n);
        if (g === n) {
            do { ys = f(ys); g = gcdCore(babs(x - ys), n); } while (g === 1n);
        }
        if (g !== n) return g;
    }
    throw fail('Не удалось разложить число.', 'Could not factor the number.', 'too-big');
}

function perfectPower(n) {
    const bits = n.toString(2).length;
    for (const k of SMALL) {
        if (k >= bits) break;
        const r = bigIroot(n, k);
        if (r > 1n && r ** BigInt(k) === n) return { r, k };
    }
    return null;
}

function splitInto(m, out, mult = 1) {
    if (m === 1n) return;
    if (isPrimeBig(m)) { out.set(m, (out.get(m) ?? 0) + mult); return; }
    const pp = perfectPower(m);
    if (pp) { splitInto(pp.r, out, mult * pp.k); return; }
    const d = rho(m);
    splitInto(d, out, mult);
    splitInto(m / d, out, mult);
}

function factorMap(N) {
    const out = new Map();
    let m = babs(N);
    for (const p of SMALL_BIG) {
        if (p * p > m) break;
        if (m % p === 0n) {
            let e = 0;
            do { m /= p; e++; } while (m % p === 0n);
            out.set(p, e);
        }
    }
    if (m > 1n) {
        if (m < BigInt(TRIAL) * BigInt(TRIAL)) out.set(m, (out.get(m) ?? 0) + 1);
        else splitInto(m, out);
    }
    return new Map([...out.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1)));
}
const mapToList = (m) => [...m.entries()].map(([p, e]) => ({ p, e }));

/** TeX of a factorisation [{p, e}] → 2^{3} \cdot 3 \cdot 5^{2} ("1" for the empty list). */
export function ntFactorTex(factors) {
    if (!factors.length) return '1';
    return factors.map(({ p, e }) => (e === 1 ? tn(p) : `${tn(p)}^{${e}}`)).join(' \\cdot ');
}

function ruleHint(p, m, lang) {
    const s = m.toString();
    if (p === 2) return lang === 'ru' ? ' (последняя цифра чётная)' : ' (the last digit is even)';
    if (p === 5) return lang === 'ru' ? ` (оканчивается на ${s[s.length - 1]})` : ` (it ends in ${s[s.length - 1]})`;
    if (p === 3 && s.length > 1 && s.length <= 10) {
        const ds = s.split('').reduce((a, c) => a + +c, 0);
        return lang === 'ru' ? ` (сумма цифр ${s.split('').join(' + ')} = ${ds} делится на 3)` : ` (the digit sum ${s.split('').join(' + ')} = ${ds} is divisible by 3)`;
    }
    return '';
}

/**
 * Prime factorisation of |n| → [{p: BigInt, e: number}] ascending (trial division to 10 000, then
 * Miller–Rabin + Pollard–Brent ρ). {steps: true} → {value, tex, ladder: [{n, p}], steps}.
 */
export function ntFactor(n, opts = {}) {
    const N = big(n);
    if (N === 0n) throw fail('Ноль нельзя разложить на простые множители: он делится на всё.', 'Zero cannot be factored into primes: everything divides it.', 'zero');
    if (!opts.steps) return mapToList(factorMap(N));

    const st = [];
    let m = babs(N);
    const groups = [];
    let skipped = [];
    let reason = null;
    if (N < 0n) {
        st.push(S(L('Выносим минус', 'Take out the minus sign'), `${tn(N)} = -${tn(m)}`,
            L('Раскладываем модуль числа, знак пишем отдельно.', 'We factor the absolute value and keep the sign aside.')));
    }
    if (m === 1n) {
        st.push(S(L('Единица', 'One'), '1 = 1', L('У единицы нет простых делителей: это пустое произведение.', 'One has no prime factors: it is the empty product.'), { rule: 'answer' }));
        return { value: [], tex: '1', ladder: [], steps: st };
    }
    st.push(S(L('Делим на простые по порядку', 'Divide by primes in order'), null,
        L('Пробуем простые числа по возрастанию: 2, 3, 5, 7, 11, … Пока число делится — делим, когда перестаёт — берём следующее простое. Так каждый найденный делитель сам оказывается простым.',
            'We try the primes in increasing order: 2, 3, 5, 7, 11, … While the number divides, we divide; when it stops, we move to the next prime. This way every divisor we find is automatically prime.'),
        { rule: 'trial-division' }));
    const ladder = [];
    for (const p of SMALL_BIG) {
        if (p * p > m) { reason = 'sqrt'; break; }
        if (m % p === 0n) {
            const before = m;
            let e = 0;
            do { ladder.push({ n: m, p }); m /= p; e++; } while (m % p === 0n);
            groups.push({ p, e, before, after: m, skipped });
            skipped = [];
        } else skipped.push(p);
    }
    if (!reason) reason = m === 1n ? 'done' : 'big';
    for (const gr of groups) {
        const piece = (i) => `${i === 1 ? tn(gr.p) : `${tn(gr.p)}^{${i}}`} \\cdot ${tn(gr.before / gr.p ** BigInt(i))}`;
        const pieces = gr.e <= 5 ? Array.from({ length: gr.e }, (_, i) => piece(i + 1)) : [piece(1), '\\ldots', piece(gr.e)];
        const skipTxt = (l) => (gr.skipped.length ? (l === 'ru' ? `На ${listText(gr.skipped, l)} не делится. ` : `It is not divisible by ${listText(gr.skipped, l)}. `) : '');
        const times = (l) => (l === 'ru' ? `${gr.e} ${gr.e % 10 >= 2 && gr.e % 10 <= 4 && (gr.e % 100 < 12 || gr.e % 100 > 14) ? 'раза' : 'раз'}` : `${gr.e} times`);
        st.push(S(L(`Делим на ${sn(gr.p)}`, `Divide by ${sn(gr.p)}`),
            `${tn(gr.before)} = ${pieces.join(' = ')}`,
            T((l) => (l === 'ru'
                ? `${skipTxt(l)}${sn(gr.before)} делится на ${sn(gr.p)}${ruleHint(Number(gr.p), gr.before, l)}. ${gr.e > 1 ? `Делим, пока делится, — ${times(l)}` : 'Делим'}; остаётся ${sn(gr.after)}.`
                : `${skipTxt(l)}${sn(gr.before)} is divisible by ${sn(gr.p)}${ruleHint(Number(gr.p), gr.before, l)}. ${gr.e > 1 ? `We divide while we can — ${times(l)}` : 'We divide'}; ${sn(gr.after)} is left.`)),
            { rule: 'divide', p: gr.p, e: gr.e }));
    }
    const out = new Map(groups.map((g) => [g.p, g.e]));
    if (reason === 'sqrt' && m > 1n) {
        const r = Math.sqrt(Number(m));
        const whole = groups.length === 0;
        st.push(S(whole ? L('Число простое', 'The number is prime') : L('Остаток — простое число', 'What is left is prime'),
            T((l) => `\\sqrt{${tn(m)}} \\approx ${dec(r, 1, l, true)}`),
            T((l) => (l === 'ru'
                ? `${whole ? `Проверили все простые до √${sn(m)} ≈ ${dec(r, 1, l)}` : `Осталось ${sn(m)}. Все простые до √${sn(m)} ≈ ${dec(r, 1, l)} мы уже проверили`} — ни одно не делит. Значит, ${sn(m)} простое: у составного числа обязательно есть простой делитель, не больший его корня.`
                : `${whole ? `We have tried every prime up to √${sn(m)} ≈ ${dec(r, 1, l)}` : `${sn(m)} is left. We have already tried every prime up to √${sn(m)} ≈ ${dec(r, 1, l)}`} and none divides it. So ${sn(m)} is prime: a composite number always has a prime divisor no larger than its square root.`)),
            { rule: 'sqrt-bound' }));
        out.set(m, (out.get(m) ?? 0) + 1);
        ladder.push({ n: m, p: m });
    } else if (reason === 'big') {
        const rest = new Map();
        splitInto(m, rest);
        const ps = [...rest.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1));
        const certain = ps.every(([p]) => p < MR_LIMIT);
        const single = ps.length === 1 && ps[0][1] === 1;
        const digits = m.toString().length;
        st.push(S(single ? L('Большой простой остаток', 'A large prime cofactor') : L('Большой остаток', 'A large cofactor'),
            `${tn(m)} = ${ntFactorTex(ps.map(([p, e]) => ({ p, e })))}`,
            L(`После простых до ${sn(TRIAL)} осталось ${digits}-значное число ${sn(m)}; перебирать дальше слишком долго. `
                + (single ? `Тест Миллера — Рабина показывает, что оно простое${certain ? '' : ' (с вероятностью ошибки меньше 4⁻³⁷)'}.`
                    : `Тест Миллера — Рабина показывает, что оно составное, а ρ-метод Полларда (псевдослучайное блуждание по остаткам: делитель p находится примерно за √p шагов) находит множители; каждый из них проверен тестом Миллера — Рабина${certain ? '' : ' (вероятностно)'}.`),
                `After the primes up to ${sn(TRIAL)} a ${digits}-digit number ${sn(m)} is left, too big to keep trying divisors. `
                + (single ? `The Miller–Rabin test shows it is prime${certain ? '' : ' (with error probability below 4⁻³⁷)'}.`
                    : `The Miller–Rabin test shows it is composite, and Pollard's rho method (a pseudo-random walk over remainders that finds a divisor p in about √p steps) splits it; each factor is then checked by Miller–Rabin${certain ? '' : ' (probabilistically)'}.`)),
            { rule: single ? 'miller-rabin' : 'pollard-rho' }));
        for (const [p, e] of ps) {
            out.set(p, (out.get(p) ?? 0) + e);
            for (let i = 0; i < e; i++) { ladder.push({ n: m, p }); m /= p; }
        }
    }
    const value = [...out.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1)).map(([p, e]) => ({ p, e }));
    if (ladder.length > 1 && ladder.length <= 40) {
        const rowsTex = ladder.map(({ n: k, p }) => `${tn(k)} & ${tn(p)}`).join(' \\\\ ') + ' \\\\ 1 & ';
        st.push(S(L('Лесенка', 'The division ladder'), `\\begin{array}{r|l} ${rowsTex} \\end{array}`,
            L('Так это записывают в тетради: слева — что осталось, справа — на что делим. Правый столбец — все простые множители.',
                'The usual notebook layout: on the left what is left, on the right the prime we divide by. The right column lists all the prime factors.'),
            { rule: 'ladder' }));
    }
    const tex = ntFactorTex(value);
    st.push(S(L('Ответ', 'Answer'), `${tn(N)} = ${N < 0n ? '-' : ''}${tex}`,
        value.length === 1 && value[0].e === 1
            ? L(`${sn(babs(N))} — простое число.`, `${sn(babs(N))} is prime.`)
            : L('По основной теореме арифметики это разложение единственно (с точностью до порядка множителей).', 'By the fundamental theorem of arithmetic this factorisation is unique (up to the order of the factors).'),
        { rule: 'answer' }));
    return { value, tex, ladder, steps: st };
}

/** All positive divisors of n, ascending (BigInt). */
export function ntDivisors(n) {
    const N = big(n);
    if (N === 0n) throw fail('У нуля бесконечно много делителей.', 'Zero has infinitely many divisors.', 'zero');
    let divs = [1n];
    for (const [p, e] of factorMap(N)) {
        const next = [];
        for (const d of divs) {
            let pk = 1n;
            for (let i = 0; i <= e; i++) { next.push(d * pk); pk *= p; }
        }
        divs = next;
        if (divs.length > 2_000_000) throw fail('Слишком много делителей.', 'Too many divisors.', 'too-big');
    }
    return divs.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

/** Number of divisors τ(n). */
export function ntTau(n) {
    const N = big(n);
    if (N === 0n) throw fail('У нуля бесконечно много делителей.', 'Zero has infinitely many divisors.', 'zero');
    let t = 1n;
    for (const [, e] of factorMap(N)) t *= BigInt(e + 1);
    return t;
}

/** σ_k(n): the sum of the k-th powers of the divisors (k = 1 by default; k = 0 gives τ). */
export function ntSigma(n, k = 1) {
    const N = big(n);
    if (N === 0n) throw fail('У нуля бесконечно много делителей.', 'Zero has infinitely many divisors.', 'zero');
    const K = BigInt(k);
    let s = 1n;
    for (const [p, e] of factorMap(N)) {
        if (K === 0n) { s *= BigInt(e + 1); continue; }
        const pk = p ** K;
        s *= (pk ** BigInt(e + 1) - 1n) / (pk - 1n);
    }
    return s;
}

/** Möbius function μ(n) ∈ {−1, 0, 1} (a number). */
export function ntMobius(n) {
    const N = big(n);
    if (N <= 0n) throw fail('μ(n) определена для натуральных n.', 'μ(n) is defined for positive n.');
    let mu = 1;
    for (const [, e] of factorMap(N)) {
        if (e > 1) return 0;
        mu = -mu;
    }
    return mu;
}

/** Euler's totient φ(n). {steps: true} → {value, steps} (formula, multiplicativity, listing for n ≤ 100). */
export function ntPhi(n, opts = {}) {
    const N = big(n);
    if (N <= 0n) throw fail('Функция Эйлера определена для натуральных чисел.', "Euler's function is defined for positive integers.");
    const fs = mapToList(factorMap(N));
    let value = N;
    for (const { p } of fs) value = (value / p) * (p - 1n);
    if (!opts.steps) return value;
    const st = [];
    st.push(S(L('Что считаем', 'What we count'), `\\varphi(${tn(N)})`,
        L('φ(n) — сколько чисел от 1 до n взаимно просты с n, то есть не имеют с ним общих делителей, кроме 1.',
            'φ(n) is how many numbers from 1 to n are coprime to n, that is, share no divisor with it except 1.'), { rule: 'phi-def' }));
    if (N === 1n) {
        st.push(S(L('Ответ', 'Answer'), '\\varphi(1) = 1', L('Единица взаимно проста сама с собой.', 'One is coprime to itself.'), { rule: 'answer' }));
        return { value, steps: st };
    }
    st.push(S(L('Раскладываем на простые множители', 'Factor into primes'), `${tn(N)} = ${ntFactorTex(fs)}`, null, { rule: 'factor', sub: ntFactor(N, { steps: true }).steps }));
    const brackets = fs.map(({ p }) => `\\left(1 - \\frac{1}{${tn(p)}}\\right)`).join('');
    const fracs = fs.map(({ p }) => `\\frac{${tn(p - 1n)}}{${tn(p)}}`).join(' \\cdot ');
    st.push(S(L('Формула Эйлера', "Euler's formula"), `\\varphi(${tn(N)}) = ${tn(N)} ${brackets} = ${tn(N)} \\cdot ${fracs} = ${tn(value)}`,
        L('Среди любых p подряд идущих чисел ровно одно делится на p. Поэтому множитель (1 − 1/p) отбрасывает числа, кратные p, — и так для каждого простого делителя n. Для разных простых эти отсевы независимы, поэтому множители перемножаются.',
            'Among any p consecutive numbers exactly one is divisible by p, so the factor (1 − 1/p) discards the multiples of p — once for every prime divisor of n. For different primes these sieves are independent, so the factors multiply.'),
        { rule: 'phi-formula' }));
    if (fs.length > 1 || fs[0].e > 1) {
        const alt = fs.map(({ p, e }) => (e === 1 ? `${tn(p - 1n)}` : `(${tn(p ** BigInt(e))} - ${tn(p ** BigInt(e - 1))})`)).join(' \\cdot ');
        st.push(S(L('Другой путь', 'Another way'), `\\varphi(${tn(N)}) = ${fs.map(({ p, e }) => `\\varphi(${e === 1 ? tn(p) : `${tn(p)}^{${e}}`})`).join('\\,')} = ${alt} = ${tn(value)}`,
            L('φ мультипликативна: для взаимно простых множителей значения перемножаются, а φ(p^k) = p^k − p^(k−1), потому что из p^k чисел выбрасываем p^(k−1) кратных p.',
                'φ is multiplicative: for coprime factors the values multiply, and φ(p^k) = p^k − p^(k−1), because out of p^k numbers we drop the p^(k−1) multiples of p.'),
            { rule: 'phi-multiplicative' }));
    }
    if (N <= 100n) {
        const list = [];
        for (let k = 1n; k <= N; k++) if (gcdCore(k, N) === 1n) list.push(k);
        st.push(S(L('Проверка перебором', 'Check by listing'), null,
            L(`Взаимно просты с ${sn(N)}: ${list.map(sn).join(', ')} — их ${list.length}.`, `Coprime to ${sn(N)}: ${list.map(sn).join(', ')} — ${list.length} of them.`), { rule: 'check' }));
    }
    return { value, steps: st };
}

// ---------------------------------------------------------------- primes

/** Primes ≤ n as a plain array of numbers (sieve of Eratosthenes; n ≤ 10⁸). */
export function ntPrimesUpTo(n) {
    n = Math.floor(Number(n));
    if (!(n >= 2)) return [];
    if (n > 1e8) throw fail('Слишком большая граница для решета (не больше 10⁸).', 'The bound is too large for a sieve (at most 10⁸).', 'too-big');
    const comp = sieveBytes(n);
    const out = [];
    for (let i = 2; i <= n; i++) if (!comp[i]) out.push(i);
    return out;
}

/** Sieve data for widgets: {primes, isPrime: Uint8Array, spf: Int32Array} (spf = smallest prime factor, 0 for 0 and 1). */
export function ntSieve(n) {
    n = Math.max(1, Math.floor(Number(n)));
    if (n > 2e7) throw fail('Слишком большая граница (не больше 2·10⁷).', 'The bound is too large (at most 2·10⁷).', 'too-big');
    const spf = new Int32Array(n + 1);
    const primes = [];
    for (let i = 2; i <= n; i++) {
        if (spf[i] === 0) { spf[i] = i; primes.push(i); }
        for (const p of primes) {
            if (p > spf[i] || p * i > n) break;
            spf[p * i] = p;
        }
    }
    const isPrime = new Uint8Array(n + 1);
    for (const p of primes) isPrime[p] = 1;
    return { primes, isPrime, spf };
}

/** π(n): the number of primes ≤ n (Lucy_Hedgehog, O(n^¾)); fast up to 10¹⁰, allowed up to 10¹¹. */
export function ntPrimePi(n) {
    n = Math.floor(Number(n));
    if (!(n >= 2)) return 0;
    if (n > 1e11) throw fail('Слишком большое n (не больше 10¹¹).', 'n is too large (at most 10¹¹).', 'too-big');
    if (n <= 2e6) {
        const c = sieveBytes(n);
        let k = 0;
        for (let i = 2; i <= n; i++) if (!c[i]) k++;
        return k;
    }
    const r = Math.floor(Math.sqrt(n));
    const lo = new Float64Array(r + 1); // S(v) for v ≤ r
    const hi = new Float64Array(r + 1); // S(⌊n / i⌋) for i ≤ r
    for (let v = 1; v <= r; v++) lo[v] = v - 1;
    for (let i = 1; i <= r; i++) hi[i] = Math.floor(n / i) - 1;
    for (let p = 2; p <= r; p++) {
        if (lo[p] === lo[p - 1]) continue;
        const sp = lo[p - 1], p2 = p * p;
        const lim = Math.min(r, Math.floor(n / p2));
        for (let i = 1; i <= lim; i++) {
            const d = i * p;
            hi[i] -= (d <= r ? hi[d] : lo[Math.floor(n / d)]) - sp;
        }
        for (let v = r; v >= p2; v--) lo[v] -= lo[Math.floor(v / p)] - sp;
    }
    return hi[1];
}

/** The smallest prime > n. */
export function ntNextPrime(n) {
    let N = big(n);
    if (N < 2n) return 2n;
    if (N === 2n) return 3n;
    N += (N & 1n) ? 2n : 1n;
    while (!isPrimeBig(N)) N += 2n;
    return N;
}

/** The largest prime < n, or null when there is none. */
export function ntPrevPrime(n) {
    let N = big(n);
    if (N <= 2n) return null;
    if (N === 3n) return 2n;
    N -= (N & 1n) ? 2n : 1n;
    while (!isPrimeBig(N)) N -= 2n;
    return N;
}

export function ntIsPerfectSquare(n) {
    const N = big(n);
    if (N < 0n) return false;
    const r = bigIsqrt(N);
    return r * r === N;
}

/** Sum of the digits of |n| in the given base (10 by default). */
export function ntDigitSum(n, base = 10) {
    let N = babs(big(n));
    const B = BigInt(needBase(base));
    let s = 0n;
    while (N > 0n) { s += N % B; N /= B; }
    return s;
}

// ---------------------------------------------------------------- modular arithmetic

function needModulus(m) {
    const M = big(m, 'модуль');
    if (M <= 0n) throw fail('Модуль должен быть натуральным числом.', 'The modulus must be a positive integer.', 'modulus');
    return M;
}
const eqv = (m) => `\\pmod{${tn(m)}}`;

/**
 * a^e mod m by repeated squaring (result in [0, m)). A negative e uses the inverse (null if none).
 * {steps: true} → {value, rows: [{k, power, value, bit}], steps}.
 */
export function ntModPow(a, e, m, opts = {}) {
    const A = big(a), E = big(e), M = needModulus(m);
    if (E < 0n) {
        const inv = invCore(A, M);
        const value = inv === null ? null : powmod(inv, -E, M);
        if (!opts.steps) return value;
        const st = [S(L('Отрицательная степень', 'A negative exponent'), `${tp(A)}^{${tn(E)}} = \\left(${tp(A)}^{-1}\\right)^{${tn(-E)}}`,
            inv === null ? L(`Обратного к ${sn(A)} по модулю ${sn(M)} нет, поэтому отрицательная степень не определена.`, `${sn(A)} has no inverse modulo ${sn(M)}, so a negative power is undefined.`)
                : L(`Сначала находим обратный: ${sn(A)}⁻¹ ≡ ${sn(inv)} (mod ${sn(M)}), затем возводим его в степень ${sn(-E)}.`, `First the inverse: ${sn(A)}⁻¹ ≡ ${sn(inv)} (mod ${sn(M)}), then raise it to the power ${sn(-E)}.`),
            { rule: 'negative-power' })];
        if (inv === null) return { value, rows: [], steps: st };
        const r = ntModPow(inv, -E, M, { steps: true });
        return { value, rows: r.rows, steps: [...st, ...r.steps] };
    }
    const value = powmod(A, E, M);
    if (!opts.steps) return value;
    const st = [];
    const rows = [];
    if (M === 1n) {
        st.push(S(L('Модуль 1', 'Modulus 1'), `${tp(A)}^{${tn(E)}} \\equiv 0 \\pmod{1}`, L('По модулю 1 любое число сравнимо с нулём.', 'Every number is congruent to 0 modulo 1.'), { rule: 'answer' }));
        return { value, rows, steps: st };
    }
    if (E === 0n) {
        st.push(S(L('Нулевая степень', 'Power zero'), `${tp(A)}^{0} = 1`, L('Любое число в нулевой степени равно 1.', 'Anything to the power zero is 1.'), { rule: 'answer' }));
        return { value, rows, steps: st };
    }
    const bin = E.toString(2);
    const bits = bin.length;
    const used = [];
    for (let k = 0; k < bits; k++) if (bin[bits - 1 - k] === '1') used.push(k);
    const P = (k) => (k < 20 ? tn(1n << BigInt(k)) : `2^{${k}}`);
    const base = bmod(A, M);
    const sq = bits - 1;
    st.push(S(L('Показатель — в двоичную запись', 'Write the exponent in binary'),
        `${tn(E)} = ${bin}_2${used.length > 1 && used.length <= 12 ? ` = ${[...used].reverse().map(P).join(' + ')}` : ''}`,
        L(`Тогда ${sn(A)}^${sn(E)} — произведение степеней вида ${sn(A)}^(2^k) для единичных разрядов, а каждая такая степень — квадрат предыдущей. Всего ${sq} ${sq % 10 === 1 && sq % 100 !== 11 ? 'возведение' : sq % 10 >= 2 && sq % 10 <= 4 && (sq % 100 < 12 || sq % 100 > 14) ? 'возведения' : 'возведений'} в квадрат вместо ${sn(E - 1n)} умножений.`,
            `Then ${sn(A)}^${sn(E)} is the product of the powers ${sn(A)}^(2^k) for the one-bits, and each such power is the square of the previous one: ${sq} squaring${sq === 1 ? '' : 's'} instead of ${sn(E - 1n)} multiplications.`),
        { rule: 'binary' }));
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
        st.push(S(L('Возводим в квадрат по кругу', 'Square again and again'), `\\begin{array}{r|l|c} ${lines.join(' \\\\ ')} \\end{array}`,
            L(`Каждая строка — квадрат предыдущей, и сразу берём остаток от деления на ${sn(M)}, чтобы числа не росли. Галочки — разряды, где в двоичной записи показателя стоит 1.`,
                `Each line is the square of the previous one, reduced modulo ${sn(M)} right away so the numbers stay small. Ticks mark the bits of the exponent equal to 1.`),
            { rule: 'squaring' }));
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
        st.push(S(L('Перемножаем отмеченные строки', 'Multiply the ticked lines'),
            short ? `${tp(A)}^{${tn(E)}} = ${[...used].reverse().map((k) => `${tp(A)}^{${P(k)}}`).join(' \\cdot ')} \\equiv ${[...used].reverse().map((k) => tn(rows[k].value)).join(' \\cdot ')} \\equiv ${tn(value)} ${eqv(M)}`
                : `${tp(A)}^{${tn(E)}} \\equiv ${tn(value)} ${eqv(M)}`,
            short ? L(`Умножаем по одному и каждый раз берём остаток: ${runs.join('; ')}.`, `Multiply one at a time, reducing each time: ${runs.join('; ')}.`) : null,
            { rule: 'multiply' }));
    }
    st.push(S(L('Ответ', 'Answer'), `${tp(A)}^{${tn(E)}} \\equiv ${tn(value)} ${eqv(M)}`, null, { rule: 'answer' }));
    // a second route: Euler's theorem (Fermat's little theorem for a prime modulus)
    if (M <= 10n ** 12n && M > 2n && gcdCore(A, M) === 1n) {
        const ph = ntPhi(M);
        if (E >= ph) {
            const q = E / ph, r = E % ph;
            const prime = isPrimeBig(M);
            st.push(S(prime ? L('Проверка малой теоремой Ферма', "Check with Fermat's little theorem") : L('Проверка теоремой Эйлера', "Check with Euler's theorem"),
                `${tp(A)}^{${tn(ph)}} \\equiv 1 ${eqv(M)},\\quad ${tn(E)} = ${tn(q)} \\cdot ${tn(ph)} + ${tn(r)} \\;\\Rightarrow\\; ${tp(A)}^{${tn(E)}} \\equiv ${tp(A)}^{${tn(r)}} \\equiv ${tn(value)}`,
                prime ? L(`Модуль ${sn(M)} простой и не делит ${sn(A)}, поэтому ${sn(A)}^${sn(ph)} ≡ 1. Значит, от показателя важен только остаток от деления на ${sn(ph)}.`,
                    `The modulus ${sn(M)} is prime and does not divide ${sn(A)}, so ${sn(A)}^${sn(ph)} ≡ 1. Only the remainder of the exponent modulo ${sn(ph)} matters.`)
                    : L(`${sn(A)} взаимно просто с ${sn(M)}, а φ(${sn(M)}) = ${sn(ph)}, поэтому ${sn(A)}^${sn(ph)} ≡ 1. Значит, от показателя важен только остаток от деления на ${sn(ph)}.`,
                        `${sn(A)} is coprime to ${sn(M)} and φ(${sn(M)}) = ${sn(ph)}, so ${sn(A)}^${sn(ph)} ≡ 1. Only the remainder of the exponent modulo ${sn(ph)} matters.`),
                { rule: prime ? 'fermat' : 'euler' }));
        }
    }
    return { value, rows, steps: st };
}

/** Inverse of a modulo m in [0, m), or null when gcd(a, m) ≠ 1. {steps: true} → {value, steps}. */
export function ntModInv(a, m, opts = {}) {
    const A = big(a), M = needModulus(m);
    const value = invCore(A, M);
    if (!opts.steps) return value;
    const st = [];
    const g = gcdCore(A, M);
    st.push(S(L('Что ищем', 'What we look for'), `${tp(A)} \\cdot x \\equiv 1 ${eqv(M)}`,
        L(`Ищем x, для которого ${sn(A)}·x даёт остаток 1 при делении на ${sn(M)}. Это то же самое, что ${sn(A)}·x + ${sn(M)}·y = 1 для какого-то целого y.`,
            `We want x such that ${sn(A)}·x leaves remainder 1 on division by ${sn(M)}, which is the same as ${sn(A)}·x + ${sn(M)}·y = 1 for some integer y.`), { rule: 'inverse-def' }));
    if (M === 1n) {
        st.push(S(L('Модуль 1', 'Modulus 1'), 'x \\equiv 0 \\pmod{1}', L('По модулю 1 все числа сравнимы с нулём.', 'Modulo 1 every number is 0.'), { rule: 'answer' }));
        return { value, steps: st };
    }
    if (value === null) {
        st.push(S(L('Обратного нет', 'No inverse'), T((l) => `${G(l, A, M)} = ${tn(g)} \\ne 1`),
            L(`${sn(A)}·x + ${sn(M)}·y при любых x и y делится на ${sn(g)}, а 1 — нет. Обратный существует только у чисел, взаимно простых с модулем.`,
                `${sn(A)}·x + ${sn(M)}·y is divisible by ${sn(g)} for all x and y, but 1 is not. Only numbers coprime to the modulus have inverses.`),
            { rule: 'answer', sub: gcdSteps(A, M).st }));
        return { value, steps: st };
    }
    const e = ntEgcd(A, M, { steps: true });
    const yP = e.y < 0n ? `(${sn(e.y)})` : sn(e.y);
    st.push(S(L('Расширенный алгоритм Евклида', 'The extended Euclidean algorithm'),
        `${tp(A)} \\cdot ${tp(e.x)} + ${tn(M)} \\cdot ${tp(e.y)} = 1`,
        L('НОД равен 1, и обратный ход алгоритма Евклида даёт нужное представление единицы.', 'The gcd is 1, and running Euclid backwards gives the representation of 1 we need.'),
        { rule: 'egcd', sub: e.steps }));
    st.push(S(L('Отбрасываем кратное модуля', 'Drop the multiple of the modulus'),
        `${tp(A)} \\cdot ${tp(e.x)} \\equiv 1 ${eqv(M)} \\;\\Rightarrow\\; x \\equiv ${e.x !== value ? `${tn(e.x)} \\equiv ` : ''}${tn(value)} ${eqv(M)}`,
        e.x !== value ? L(`Слагаемое ${sn(M)}·${yP} делится на ${sn(M)} и на остаток не влияет. Приводим ${sn(e.x)} к промежутку от 0 до ${sn(M - 1n)}.`,
            `The term ${sn(M)}·${yP} is a multiple of ${sn(M)} and does not affect the remainder. We bring ${sn(e.x)} into the range 0 to ${sn(M - 1n)}.`)
            : L(`Слагаемое ${sn(M)}·${yP} делится на ${sn(M)} и на остаток не влияет.`, `The term ${sn(M)}·${yP} is a multiple of ${sn(M)} and does not affect the remainder.`),
        { rule: 'reduce' }));
    const prod = A * value;
    st.push(S(L('Проверка', 'Check'), `${tp(A)} \\cdot ${tn(value)} = ${tn(prod)} = ${tn((prod - 1n) / M)} \\cdot ${tn(M)} + 1 \\equiv 1 ${eqv(M)}`, null, { rule: 'check' }));
    return { value, steps: st };
}

/**
 * Linear congruence a·x ≡ b (mod m) → {solvable, d, x0, m0, solutions?}: all solutions are
 * x ≡ x0 (mod m0), m0 = m / d, i.e. d residues modulo m (listed in `solutions` when d ≤ 1000).
 */
export function ntSolveCongruence(a, b, m, opts = {}) {
    const A = big(a), B = big(b), M = needModulus(m);
    const a1 = bmod(A, M), b1 = bmod(B, M);
    const d = gcdCore(a1, M); // gcd(0, M) = M
    const st = [];
    const cong = (x, y, mm) => `${coefX(x)} \\equiv ${tn(y)} ${eqv(mm)}`;
    if (opts.steps) {
        st.push(S(L('Что значит сравнение', 'What the congruence means'), cong(A, B, M),
            L(`Нужны такие x, что ${A === 1n ? 'x' : `${sn(A)}·x`} − ${sn(B)} делится на ${sn(M)}.${a1 !== A || b1 !== B ? ` Сначала заменяем коэффициенты остатками от деления на ${sn(M)}: ${sn(a1)}x ≡ ${sn(b1)}.` : ''}`,
                `We need x such that ${A === 1n ? 'x' : `${sn(A)}·x`} − ${sn(B)} is divisible by ${sn(M)}.${a1 !== A || b1 !== B ? ` First replace the coefficients by their remainders modulo ${sn(M)}: ${sn(a1)}x ≡ ${sn(b1)}.` : ''}`),
            { rule: 'congruence-def' }));
        st.push(S(L(`НОД(${sn(a1)}, ${sn(M)}) = ${sn(d)}`, `gcd(${sn(a1)}, ${sn(M)}) = ${sn(d)}`), T((l) => `d = ${G(l, a1, M)} = ${tn(d)}`),
            L('От НОД коэффициента и модуля зависит, сколько решений.', 'The gcd of the coefficient and the modulus decides how many solutions there are.'),
            { rule: 'gcd', sub: gcdSteps(a1, M).st }));
    }
    if (b1 % d !== 0n) {
        const res = { solvable: false, d, x0: null, m0: null, solutions: [] };
        if (opts.steps) {
            st.push(S(L('Решений нет', 'No solutions'), `${tn(d)} \\nmid ${tn(b1)}`,
                L(`Если ${sn(a1)}x − ${sn(b1)} = k·${sn(M)}, то ${sn(b1)} = ${sn(a1)}x − k·${sn(M)} делится на ${sn(d)}, ведь на ${sn(d)} делятся и ${sn(a1)}, и ${sn(M)}. Но ${sn(b1)} на ${sn(d)} не делится — значит, решений нет.`,
                    `If ${sn(a1)}x − ${sn(b1)} = k·${sn(M)}, then ${sn(b1)} = ${sn(a1)}x − k·${sn(M)} is divisible by ${sn(d)}, since both ${sn(a1)} and ${sn(M)} are. But ${sn(b1)} is not, so there are no solutions.`),
                { rule: 'answer' }));
            res.steps = st;
        }
        return res;
    }
    const a2 = a1 / d, b2 = b1 / d, m2 = M / d;
    const inv = invCore(a2, m2);
    const x0 = m2 === 1n ? 0n : bmod(b2 * inv, m2);
    const res = { solvable: true, d, x0, m0: m2 };
    if (d <= 1000n) {
        res.solutions = [];
        for (let k = 0n; k < d; k++) res.solutions.push(x0 + k * m2);
    }
    if (!opts.steps) return res;
    if (a1 === 0n) {
        st.push(S(L('Подходит любое x', 'Every x works'), `0 \\cdot x \\equiv 0 ${eqv(M)}`,
            L('И коэффициент при x, и правая часть делятся на модуль: сравнение верно при любом x.', 'Both the coefficient and the right side are multiples of the modulus: the congruence holds for every x.'), { rule: 'answer' }));
        res.steps = st;
        return res;
    }
    if (d > 1n) {
        st.push(S(L(`Делим всё на ${sn(d)}`, `Divide everything by ${sn(d)}`), `${cong(a1, b1, M)} \\;\\Leftrightarrow\\; ${cong(a2, b2, m2)}`,
            L(`${sn(b1)} делится на ${sn(d)}, значит, решения есть. Делим обе части и модуль на ${sn(d)}: равенство ${sn(a1)}x − ${sn(b1)} = k·${sn(M)} равносильно ${sn(a2)}x − ${sn(b2)} = k·${sn(m2)}.`,
                `${sn(b1)} is divisible by ${sn(d)}, so solutions exist. Divide both sides and the modulus by ${sn(d)}: ${sn(a1)}x − ${sn(b1)} = k·${sn(M)} is the same as ${sn(a2)}x − ${sn(b2)} = k·${sn(m2)}.`),
            { rule: 'divide' }));
    }
    if (m2 === 1n) {
        st.push(S(L('Подходит любое x', 'Every x works'), 'x \\equiv 0 \\pmod{1}', L('По модулю 1 сравнение выполняется всегда.', 'Modulo 1 the congruence always holds.')));
    } else if (a2 !== 1n) {
        const iv = ntModInv(a2, m2, { steps: true });
        st.push(S(L(`Умножаем на обратный к ${sn(a2)}`, `Multiply by the inverse of ${sn(a2)}`),
            `${tn(a2)}^{-1} \\equiv ${tn(inv)} ${eqv(m2)} \\;\\Rightarrow\\; x \\equiv ${tn(b2)} \\cdot ${tn(inv)} = ${tn(b2 * inv)}${b2 * inv !== x0 ? ` \\equiv ${tn(x0)}` : ''} ${eqv(m2)}`,
            L(`${sn(a2)} и ${sn(m2)} взаимно просты, поэтому у ${sn(a2)} есть обратный: ${sn(a2)}·${sn(inv)} = ${sn(a2 * inv)} ≡ 1. Умножив на него обе части, мы как бы делим на ${sn(a2)}.`,
                `${sn(a2)} and ${sn(m2)} are coprime, so ${sn(a2)} has an inverse: ${sn(a2)}·${sn(inv)} = ${sn(a2 * inv)} ≡ 1. Multiplying both sides by it in effect divides by ${sn(a2)}.`),
            { rule: 'inverse', sub: iv.steps }));
    }
    if (d > 1n) {
        st.push(S(L(`${sn(d)} ${ruPl(d, 'решение', 'решения', 'решений')} по модулю ${sn(M)}`, `${sn(d)} solutions modulo ${sn(M)}`),
            res.solutions && d <= 12n ? `x \\equiv ${res.solutions.map(tn).join(',\\ ')} ${eqv(M)}` : `x = ${tn(x0)} + ${tn(m2)}k`,
            L(`Все решения — это x = ${sn(x0)} + ${sn(m2)}k. По исходному модулю ${sn(M)} они дают ровно ${sn(d)} ${ruPl(d, 'остаток', 'разных остатка', 'разных остатков')}.`,
                `All solutions are x = ${sn(x0)} + ${sn(m2)}k. Modulo the original ${sn(M)} they give exactly ${sn(d)} different remainders.`), { rule: 'answer' }));
    } else {
        st.push(S(L('Ответ и проверка', 'Answer and check'), `x \\equiv ${tn(x0)} ${eqv(M)},\\quad ${tn(a1)} \\cdot ${tn(x0)} = ${tn(a1 * x0)} \\equiv ${tn(bmod(a1 * x0, M))} ${eqv(M)}`,
            L(`Решение единственно по модулю ${sn(M)}: x = ${sn(x0)} + ${sn(M)}k.`, `The solution is unique modulo ${sn(M)}: x = ${sn(x0)} + ${sn(M)}k.`), { rule: 'answer' }));
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
        throw fail('Нужны два списка одинаковой длины: остатки и модули.', 'Two lists of the same length are needed: remainders and moduli.');
    }
    const rs = residues.map((r) => big(r)), ms = moduli.map((m) => needModulus(m));
    let X = bmod(rs[0], ms[0]), Mx = ms[0];
    const st = [];
    const lin = (c, mult, v) => `${tn(c)} + ${tn(mult)}${v}`;
    if (opts.steps) {
        st.push(S(L('Система сравнений', 'The system'), `\\begin{cases} ${rs.map((r, i) => `x \\equiv ${tn(r)} ${eqv(ms[i])}`).join(' \\\\ ')} \\end{cases}`,
            L('Решаем подстановкой: из первого сравнения выражаем x через новую неизвестную и подставляем в следующее. После каждого шага остаётся одно сравнение, которое заменяет все уже учтённые.',
                'We solve by substitution: express x from the first congruence through a new unknown and plug it into the next one. After each step a single congruence replaces all those used so far.'),
            { rule: 'crt' }));
        st.push(S(L('Из первого сравнения', 'From the first congruence'), `x = ${lin(X, Mx, 't')}`,
            L(`Числа с остатком ${sn(X)} при делении на ${sn(Mx)} — это ${sn(X)} + ${sn(Mx)}t, где t — любое целое.`,
                `Numbers leaving remainder ${sn(X)} on division by ${sn(Mx)} are ${sn(X)} + ${sn(Mx)}t for any integer t.`)));
    }
    const vars = ['t', 's', 'u', 'v', 'w', 'z'];
    for (let i = 1; i < rs.length; i++) {
        const r = bmod(rs[i], ms[i]), m = ms[i];
        const g = gcdCore(Mx, m);
        const diff = bmod(r - X, m);
        const v = vars[(i - 1) % vars.length], vn = vars[i % vars.length];
        if (diff % g !== 0n) {
            const res = { solvable: false, x: null, m: null, conflict: i };
            if (opts.steps) {
                st.push(S(L('Противоречие', 'A contradiction'), `${lin(X, Mx, v)} \\equiv ${tn(r)} ${eqv(m)}`,
                    L(`Модули ${sn(Mx)} и ${sn(m)} имеют общий делитель ${sn(g)}. По модулю ${sn(g)} прежние условия дают остаток ${sn(bmod(X, g))}, а новое — ${sn(bmod(r, g))}. Одно число не может давать два разных остатка, поэтому у системы нет решений.`,
                        `The moduli ${sn(Mx)} and ${sn(m)} share the divisor ${sn(g)}. Modulo ${sn(g)} the conditions so far give remainder ${sn(bmod(X, g))}, but the new one gives ${sn(bmod(r, g))}. One number cannot have two different remainders, so the system has no solutions.`),
                    { rule: 'answer' }));
                res.steps = st;
            }
            return res;
        }
        const m2 = m / g;
        const a = bmod(Mx, m);
        const t0 = m2 === 1n ? 0n : bmod((diff / g) * invCore(Mx / g, m2), m2);
        const newX = X + Mx * t0, newM = Mx * m2;
        if (opts.steps) {
            const trivial = a === 1n && g === 1n;
            let how, sub;
            if (trivial) how = L('', '');
            else if (m2 <= 12n) {
                const at = (a / g) * t0;
                const range = (l) => (m2 === 2n ? (l === 'ru' ? '0 и 1' : '0 and 1') : m2 <= 4n ? [...Array(Number(m2)).keys()].join(', ') : `0, 1, …, ${sn(m2 - 1n)}`);
                const red = g > 1n ? L(` Делим сравнение и модуль на НОД = ${sn(g)}: ${sn(a / g)}${v} ≡ ${sn(diff / g)} (mod ${sn(m2)}).`,
                    ` Divide the congruence and the modulus by the gcd ${sn(g)}: ${sn(a / g)}${v} ≡ ${sn(diff / g)} (mod ${sn(m2)}).`) : L('', '');
                how = L(`${red.ru} Перебираем ${v} = ${range('ru')}: подходит ${v} = ${sn(t0)}, ведь ${sn(a / g)}·${sn(t0)} = ${sn(at)}${at !== bmod(at, m2) ? ` ≡ ${sn(bmod(at, m2))}` : ''}.`,
                    `${red.en} Try ${v} = ${range('en')}: ${v} = ${sn(t0)} works, since ${sn(a / g)}·${sn(t0)} = ${sn(at)}${at !== bmod(at, m2) ? ` ≡ ${sn(bmod(at, m2))}` : ''}.`);
            } else {
                how = L(' Решаем его, умножив на обратный элемент (подробности внутри).', ' We solve it with a modular inverse (details inside).');
                sub = ntSolveCongruence(a, diff, m, { steps: true }).steps;
            }
            st.push(S(L(`Подставляем в ${i + 1}-е сравнение`, `Substitute into congruence ${i + 1}`),
                `${lin(X, Mx, v)} \\equiv ${tn(r)} ${eqv(m)} \\;\\Rightarrow\\; ${coefX(a, v)} \\equiv ${tn(diff)} ${eqv(m)}${trivial ? '' : ` \\;\\Rightarrow\\; ${v} \\equiv ${tn(t0)} ${eqv(m2)}`}`,
                L(`Переносим ${sn(X)} вправо и приводим по модулю ${sn(m)}; получилось линейное сравнение относительно ${v}.${how.ru}`,
                    `Move ${sn(X)} to the right and reduce modulo ${sn(m)}; this is a linear congruence in ${v}.${how.en}`),
                { rule: 'substitute', ...(sub ? { sub } : {}) }));
            st.push(S(L('Новое общее условие', 'The combined condition'),
                `${v} = ${lin(t0, m2, vn)} \\;\\Rightarrow\\; x = ${tn(X)} + ${tn(Mx)}(${lin(t0, m2, vn)}) = ${lin(newX, newM, vn)}`,
                L(`Теперь x задаётся одним условием: x ≡ ${sn(bmod(newX, newM))} (mod ${sn(newM)}).${g > 1n ? ` Модуль — НОК(${sn(Mx)}, ${sn(m)}) = ${sn(newM)}, а не произведение: у модулей общий делитель ${sn(g)}.` : ''}`,
                    `Now x is described by a single condition: x ≡ ${sn(bmod(newX, newM))} (mod ${sn(newM)}).${g > 1n ? ` The modulus is lcm(${sn(Mx)}, ${sn(m)}) = ${sn(newM)}, not the product: the moduli share the divisor ${sn(g)}.` : ''}`),
                { rule: 'combine' }));
        }
        X = bmod(newX, newM);
        Mx = newM;
    }
    const res = { solvable: true, x: X, m: Mx };
    if (opts.steps) {
        const checks = ms.map((mm) => `${sn(X)} = ${sn(X / mm)}·${sn(mm)} + ${sn(bmod(X, mm))}`).join('; ');
        st.push(S(L('Ответ', 'Answer'), `x \\equiv ${tn(X)} ${eqv(Mx)}`,
            L(`Проверка: ${checks}.`, `Check: ${checks}.`), { rule: 'answer' }));
        res.steps = st;
    }
    return res;
}

/** Multiplicative order of a modulo m (the smallest k > 0 with a^k ≡ 1), or null if gcd(a, m) ≠ 1. */
export function ntOrder(a, m) {
    const A = big(a), M = needModulus(m);
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
    const P = big(p), Qn = big(q);
    if (P === Qn || !isPrimeBig(P) || !isPrimeBig(Qn)) throw fail('Нужны два разных простых числа.', 'Two different primes are needed.');
    const n = P * Qn, phi = (P - 1n) * (Qn - 1n);
    let e = opts.e != null ? big(opts.e) : 65537n;
    if (opts.e == null && (e >= phi || gcdCore(e, phi) !== 1n)) {
        e = 3n;
        while (gcdCore(e, phi) !== 1n) e += 2n;
    }
    if (e <= 1n || e >= phi || gcdCore(e, phi) !== 1n) {
        throw fail(`e = ${e} не подходит: нужно 1 < e < φ(n) = ${phi} и НОД(e, φ(n)) = 1.`, `e = ${e} does not work: we need 1 < e < φ(n) = ${phi} and gcd(e, φ(n)) = 1.`);
    }
    const d = invCore(e, phi);
    const res = { n, phi, e, d };
    if (!opts.steps) return res;
    res.steps = [
        S(L('Открытый модуль', 'The public modulus'), `n = p \\cdot q = ${tn(P)} \\cdot ${tn(Qn)} = ${tn(n)}`,
            L('Перемножить два простых легко, а разложить большое n обратно на множители очень трудно. На этом и держится шифр.',
                'Multiplying two primes is easy; factoring a large n back is very hard. The cipher relies on exactly that.'), { rule: 'rsa-n' }),
        S(L('Функция Эйлера', "Euler's function"), `\\varphi(n) = (p - 1)(q - 1) = ${tn(P - 1n)} \\cdot ${tn(Qn - 1n)} = ${tn(phi)}`,
            L('Её знает только владелец ключа: чтобы вычислить φ(n), нужно знать p и q.', 'Only the key owner knows it: computing φ(n) requires p and q.'), { rule: 'rsa-phi' }),
        S(L('Открытая экспонента', 'The public exponent'), T((l) => `e = ${tn(e)},\\quad ${G(l, e, phi)} = 1`),
            L('e должно быть взаимно просто с φ(n), иначе у него не будет обратного.', 'e must be coprime to φ(n), otherwise it has no inverse.'), { rule: 'rsa-e' }),
        S(L('Секретная экспонента', 'The private exponent'), `d \\equiv e^{-1} \\pmod{\\varphi(n)}:\\quad d = ${tn(d)},\\quad ${tn(e)} \\cdot ${tn(d)} = ${tn(e * d)} \\equiv 1 \\pmod{${tn(phi)}}`,
            L('Тогда (m^e)^d ≡ m (mod n) для любого сообщения m — расшифровка отменяет шифрование (по теореме Эйлера).',
                "Then (m^e)^d ≡ m (mod n) for every message m: decryption undoes encryption (by Euler's theorem)."),
            { rule: 'rsa-d', sub: ntModInv(e, phi, { steps: true }).steps }),
    ];
    return res;
}

// ---------------------------------------------------------------- number bases

const DIGITS = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ';
function needBase(base) {
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
    return (a % b !== 0n) && ((a < 0n) !== (b < 0n)) ? q - 1n : q;
}

/**
 * Continued fraction of a rational (Q, 'a/b', '3.14', BigInt) — exact and finite; of {sqrt: n} —
 * periodic, {a0, period}; of a non-integer double — the terms of its exact binary value until the
 * convergent reproduces the double (exact: false). → {terms: BigInt[], period?, exact, tex, steps?}.
 */
export function ntContinuedFraction(x, opts = {}) {
    if (x && typeof x === 'object' && !(x instanceof Q) && 'sqrt' in x) {
        const n = big(x.sqrt);
        if (n < 0n) throw fail('Корень из отрицательного числа.', 'Square root of a negative number.');
        const a0 = bigIsqrt(n);
        if (a0 * a0 === n) {
            const res = { terms: [a0], a0, period: [], exact: true, periodic: false, tex: `\\sqrt{${tn(n)}} = ${tn(a0)}` };
            if (opts.steps) res.steps = [S(L('Точный квадрат', 'A perfect square'), res.tex, L('Корень извлекается нацело — цепная дробь из одного числа.', 'The root is an integer, so the continued fraction is a single number.'), { rule: 'answer' })];
            return res;
        }
        const period = [];
        const rows = [];
        let mm = 0n, d = 1n, a = a0;
        do {
            mm = d * a - mm;
            d = (n - mm * mm) / d;
            a = (a0 + mm) / d;
            period.push(a);
            rows.push({ m: mm, d, a });
            if (period.length > 200000) throw fail('Слишком длинный период.', 'The period is too long.', 'too-big');
        } while (a !== 2n * a0);
        const res = { terms: [a0, ...period], a0, period, exact: true, periodic: true, tex: `\\sqrt{${tn(n)}} = ${cfTex([a0], period)}` };
        if (opts.steps) {
            const st = [S(L('Целая часть', 'The integer part'), `${tn(a0)}^2 = ${tn(a0 * a0)} < ${tn(n)} < ${tn((a0 + 1n) ** 2n)} = ${tn(a0 + 1n)}^2 \\;\\Rightarrow\\; a_0 = ${tn(a0)}`,
                L(`√${sn(n)} лежит между ${sn(a0)} и ${sn(a0 + 1n)}, так что его целая часть — ${sn(a0)}.`, `√${sn(n)} lies between ${sn(a0)} and ${sn(a0 + 1n)}, so its integer part is ${sn(a0)}.`), { rule: 'cf-int' })];
            const sq = Math.sqrt(Number(n));
            rows.slice(0, 20).forEach((r, i) => {
                const xv = (sq + Number(r.m)) / Number(r.d);
                const xt = r.d === 1n ? `\\sqrt{${tn(n)}} + ${tn(r.m)}` : `\\frac{\\sqrt{${tn(n)}} + ${tn(r.m)}}{${tn(r.d)}}`;
                st.push(S(L(`Элемент a${subscript(i + 1)}`, `Term a${subscript(i + 1)}`),
                    T((l) => `x_{${i + 1}} = ${xt} \\approx ${dec(xv, 3, l, true)} \\;\\Rightarrow\\; a_{${i + 1}} = ${tn(r.a)}`),
                    i === 0 ? L(`Переворачиваем дробную часть: x₁ = 1/(√${sn(n)} − ${sn(a0)}) и избавляемся от корня в знаменателе, домножив на сопряжённое. Целая часть результата — следующий элемент; дальше повторяем то же с x₂, x₃, …`,
                        `Flip the fractional part, x₁ = 1/(√${sn(n)} − ${sn(a0)}), and clear the root from the denominator by multiplying by the conjugate. The integer part of the result is the next term; then repeat with x₂, x₃, …`) : null,
                    { rule: 'cf-term' }));
            });
            st.push(S(L('Период', 'The period'), res.tex,
                L(`Как только элемент стал равен 2a₀ = ${sn(2n * a0)}, всё повторяется. У квадратного корня из неквадрата цепная дробь всегда периодическая (теорема Лагранжа).`,
                    `Once a term equals 2a₀ = ${sn(2n * a0)}, everything repeats. The continued fraction of the square root of a non-square is always periodic (Lagrange's theorem).`), { rule: 'answer' }));
            res.steps = st;
        }
        return res;
    }
    if (typeof x === 'number' && !Number.isInteger(x)) {
        if (!Number.isFinite(x)) throw fail('Нужно конечное число.', 'A finite number is required.', 'nan');
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
    let a = num, b = den;
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
        const st = [S(L('Идея', 'The idea'), null,
            L('Выделяем целую часть, оставшуюся правильную дробь переворачиваем — и повторяем. Это тот же алгоритм Евклида: неполные частные и есть элементы цепной дроби.',
                "Take the integer part, flip the remaining proper fraction, and repeat. It is Euclid's algorithm in disguise: the partial quotients are the terms of the continued fraction."), { rule: 'cf-idea' })];
        rows.forEach((r, i) => {
            st.push(S(i === 0 ? L('Целая часть', 'The integer part') : L(`Переворачиваем: ${sn(r.a)}/${sn(r.b)}`, `Flip: ${sn(r.a)}/${sn(r.b)}`),
                r.r === 0n ? `\\frac{${tn(r.a)}}{${tn(r.b)}} = ${tn(r.q)}` : `\\frac{${tn(r.a)}}{${tn(r.b)}} = ${tn(r.q)} + \\frac{${tn(r.r)}}{${tn(r.b)}}`,
                null, { rule: 'cf-term' }));
        });
        st.push(S(L('Ответ', 'Answer'), `\\frac{${tn(num)}}{${tn(den)}} = ${terms.length <= 12 && terms.length > 1 ? nestedTex(terms) + ' = ' : ''}${cfTex(terms)}`, null, { rule: 'answer' }));
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
    if (N < 1n) throw fail('Знаменатель должен быть не меньше 1.', 'The denominator bound must be at least 1.');
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
        const pn = a * p0 + p1, qn = a * q0 + q1;
        if (qn > N) {
            const k = (N - q1) / q0; // the best semiconvergent (p1 + k·p0)/(q1 + k·q0)
            const ps = p1 + k * p0, qs = q1 + k * q0;
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
    if (num <= 0n || num > den) throw fail('Нужна дробь больше 0 и не больше 1.', 'A fraction greater than 0 and at most 1 is required.', 'range');
    const r0 = { num, den };
    const out = [];
    const st = [];
    while (num !== 0n) {
        const n = (den + num - 1n) / num;
        out.push(n);
        const nn = num * n - den, nd = den * n;
        const g = gcdCore(nn, nd) || 1n;
        if (opts.steps) {
            st.push(S(L(`Берём 1/${sn(n)}`, `Take 1/${sn(n)}`),
                `\\frac{${tn(num)}}{${tn(den)}} - \\frac{1}{${tn(n)}} = ${nn === 0n ? '0' : `\\frac{${tn(nn / g)}}{${tn(nd / g)}}`}`,
                num === 1n ? L('Осталась дробь с числителем 1 — она и есть последнее слагаемое.', 'What is left has numerator 1: it is the last term.')
                    : L(`Самая большая дробь вида 1/n, не превосходящая ${sn(num)}/${sn(den)}: n = ⌈${sn(den)} / ${sn(num)}⌉ = ${sn(n)}. Вычитаем её и повторяем с остатком.`,
                        `The largest fraction 1/n not exceeding ${sn(num)}/${sn(den)} has n = ⌈${sn(den)} / ${sn(num)}⌉ = ${sn(n)}. Subtract it and repeat with the rest.`),
                { rule: 'greedy' }));
        }
        num = nn / g;
        den = nd / g;
        if (out.length > 40) throw fail('Слишком много слагаемых.', 'Too many terms.', 'too-big');
    }
    if (!opts.steps) return out;
    st.push(S(L('Ответ', 'Answer'), `\\frac{${tn(r0.num)}}{${tn(r0.den)}} = ${out.map((n) => `\\frac{1}{${tn(n)}}`).join(' + ')}`,
        L('Жадный алгоритм Фибоначчи всегда заканчивается: числитель остатка каждый раз строго уменьшается.', "Fibonacci's greedy algorithm always stops: the numerator of the remainder strictly decreases every time."), { rule: 'answer' }));
    return { value: out, steps: st };
}

// ---------------------------------------------------------------- divisibility rules

const RULE_BASES = [2, 3, 4, 5, 8, 9, 10, 11, 25];
const RULE_COMBOS = { 6: [2, 3], 12: [3, 4], 15: [3, 5], 18: [2, 9], 20: [4, 5], 36: [4, 9], 45: [5, 9], 75: [3, 25], 100: [4, 25] };

function ruleFor(s, d) {
    // s — the decimal digits of |n|
    const last = s[s.length - 1];
    if (d === 2 || d === 5 || d === 10) {
        const ok = d === 2 ? '02468'.includes(last) : d === 5 ? '05'.includes(last) : last === '0';
        const need = d === 2 ? L('чётная (0, 2, 4, 6 или 8)', 'even (0, 2, 4, 6 or 8)') : d === 5 ? L('0 или 5', '0 or 5') : L('0', '0');
        return {
            divides: ok,
            tex: s.length > 1 ? `\\ldots${last}` : last,
            text: L(`Последняя цифра — ${last}. Число делится на ${d} тогда и только тогда, когда его последняя цифра ${need.ru}. ${ok ? 'Делится.' : 'Не делится.'}`,
                `The last digit is ${last}. A number is divisible by ${d} exactly when its last digit is ${need.en}. ${ok ? 'It is divisible.' : 'It is not divisible.'}`),
            why: L(`Число = (число десятков)·10 + последняя цифра, а 10 делится на ${d}. Значит, всё решает последняя цифра.`,
                `The number = (number of tens)·10 + last digit, and 10 is divisible by ${d}. So only the last digit matters.`),
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
            text: L(`Смотрим на ${s.length > k ? `последние ${k === 2 ? 'две цифры' : 'три цифры'}` : 'само число'}: ${sn(t)}. ${ok ? `${sn(t)} делится на ${d} — значит, и всё число делится.` : `${sn(t)} на ${d} не делится (остаток ${sn(t % D)}) — значит, и число не делится.`}`,
                `Look at ${s.length > k ? `the last ${k === 2 ? 'two' : 'three'} digits` : 'the number itself'}: ${sn(t)}. ${ok ? `${sn(t)} is divisible by ${d}, so the whole number is.` : `${sn(t)} is not divisible by ${d} (remainder ${sn(t % D)}), so neither is the number.`}`),
            why: L(`${pw} делится на ${d}, поэтому разряды начиная с ${pw === '100' ? 'сотен' : 'тысяч'} на делимость не влияют.`,
                `${pw} is divisible by ${d}, so the places from the ${pw === '100' ? 'hundreds' : 'thousands'} up do not matter.`),
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
            text: L(`Сумма цифр — ${sn(sum)}${chain.length > 1 ? ' (цифры складывали несколько раз)' : ''}. ${ok ? `${sn(sum)} делится на ${d}, значит, и число делится.` : `${sn(sum)} на ${d} не делится (остаток ${sn(sum % D)}), значит, и число не делится — и даёт тот же остаток.`}`,
                `The digit sum is ${sn(sum)}${chain.length > 1 ? ' (we added digits more than once)' : ''}. ${ok ? `${sn(sum)} is divisible by ${d}, so the number is too.` : `${sn(sum)} is not divisible by ${d} (remainder ${sn(sum % D)}), so neither is the number — and it leaves the same remainder.`}`),
            why: L(`10, 100, 1000, … дают остаток 1 при делении на ${d} (например, 100 = 99 + 1), поэтому число и сумма его цифр дают одинаковые остатки.`,
                `10, 100, 1000, … all leave remainder 1 when divided by ${d} (for example, 100 = 99 + 1), so a number and its digit sum leave the same remainder.`),
        };
    }
    // d === 11
    const ds = s.split('').reverse().map(Number);
    let odd = 0, even = 0;
    ds.forEach((v, i) => { if (i % 2 === 0) odd += v; else even += v; });
    const diff = odd - even;
    const ok = diff % 11 === 0;
    const oddDigits = ds.filter((_, i) => i % 2 === 0), evenDigits = ds.filter((_, i) => i % 2 === 1);
    return {
        divides: ok,
        tex: `(${oddDigits.join(' + ') || '0'}) - (${evenDigits.join(' + ') || '0'}) = ${odd} - ${even} = ${diff}`,
        text: L(`Складываем цифры через одну, начиная с последней (${odd}), и отдельно остальные (${even}). Разность ${sn(diff)} ${ok ? 'делится на 11 — значит, и число делится.' : 'на 11 не делится — значит, и число не делится.'}`,
            `Add every other digit starting from the last one (${odd}) and, separately, the rest (${even}). The difference ${sn(diff)} ${ok ? 'is divisible by 11, so the number is too.' : 'is not divisible by 11, so neither is the number.'}`),
        why: L('10 = 11 − 1, поэтому 10 ≡ −1, 100 ≡ 1, 1000 ≡ −1, … по модулю 11: разряды входят в остаток попеременно с плюсом и минусом.',
            '10 = 11 − 1, so 10 ≡ −1, 100 ≡ 1, 1000 ≡ −1, … modulo 11: the places enter the remainder with alternating signs.'),
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
            divides: r.divides, remainder,
            steps: [
                S(L(`Признак делимости на ${D}`, `The test for ${D}`), r.tex, r.text, { rule: `div-${D}` }),
                S(L('Почему это работает', 'Why it works'), null, r.why, { rule: 'why' }),
            ],
        };
    }
    if (RULE_COMBOS[D]) {
        const [p, q] = RULE_COMBOS[D];
        const a = ruleFor(s, p), b = ruleFor(s, q);
        const ok = a.divides && b.divides;
        return {
            divides: ok, remainder,
            steps: [
                S(L(`Делимость на ${D} — это делимость на ${p} и на ${q}`, `Divisible by ${D} means divisible by ${p} and by ${q}`), `${D} = ${p} \\cdot ${q}`,
                    L(`${p} и ${q} взаимно просты, поэтому число делится на ${D} ровно тогда, когда делится и на ${p}, и на ${q}.`,
                        `${p} and ${q} are coprime, so a number is divisible by ${D} exactly when it is divisible by both ${p} and ${q}.`), { rule: 'combo' }),
                S(L(`Проверяем делимость на ${p}`, `Test for ${p}`), a.tex, a.text, { rule: `div-${p}`, sub: [S(L('Почему это работает', 'Why it works'), null, a.why)] }),
                S(L(`Проверяем делимость на ${q}`, `Test for ${q}`), b.tex, b.text, { rule: `div-${q}`, sub: [S(L('Почему это работает', 'Why it works'), null, b.why)] }),
                S(L('Вывод', 'Conclusion'), null, ok ? L(`Оба признака выполнены: ${sn(N)} делится на ${D}.`, `Both tests pass: ${sn(N)} is divisible by ${D}.`)
                    : L(`Хотя бы один признак не выполнен: ${sn(N)} на ${D} не делится.`, `At least one test fails: ${sn(N)} is not divisible by ${D}.`), { rule: 'answer' }),
            ],
        };
    }
    throw fail(`Для ${D} признака делимости в движке нет.`, `There is no divisibility rule for ${D} in the engine.`, 'unsupported');
}
