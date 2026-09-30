// theory/fractions — continued fractions, convergents, best approximations, Egyptian fractions.

import { Q, bigIsqrt } from '../../core/rational.js';
import { L, S, T, babs, big, dec, doubleExact, fail, gcdCore, ratOf, sn, subscript, tn } from './common.js';

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
