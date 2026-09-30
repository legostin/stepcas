// theory/gcd — gcd and lcm (Euclid with steps), the extended Euclid algorithm and linear Diophantine equations.

import { Q } from '../../core/rational.js';
import { G, L, Lc, S, T, babs, big, bmod, fail, gT, gcdCore, sn, tn, tp } from './common.js';
import { factorMap, mapToList, ntFactorTex } from './primes.js';

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
