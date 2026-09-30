// theory/primes — primality (trial division, Miller–Rabin), factorisation, arithmetic functions, lists of primes.

import { bigIroot, bigIsqrt } from '../../core/rational.js';
import { needBase } from './bases.js';
import { L, S, SMALL, SMALL_BIG, T, TRIAL, babs, big, bmod, dec, fail, gcdCore, listText, powmod, sieveBytes, sn, tn } from './common.js';

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

export function isPrimeBig(n) {
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

export function factorMap(N) {
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
export const mapToList = (m) => [...m.entries()].map(([p, e]) => ({ p, e }));

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
