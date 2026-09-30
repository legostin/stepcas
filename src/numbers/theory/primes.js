// theory/primes — primality (trial division, Miller–Rabin), factorisation, arithmetic functions, lists of primes.

import { bigIroot, bigIsqrt } from '../../core/rational.js';
import { needBase } from './bases.js';
import { SMALL, SMALL_BIG, TRIAL, babs, big, bmod, dec, fail, gcdCore, listText, powmod, sieveBytes, sn, tn } from './common.js';
import { msg, eachLanguage } from '../../i18n/index.js';
import { step } from '../../core/steps.js';

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
    let d = n - 1n,
        s = 0;
    while ((d & 1n) === 0n) {
        d >>= 1n;
        s++;
    }
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
            st.push(
                step({
                    title: msg('numbers.theory.primes.no_test_needed'),
                    text:
                        N < 2n
                            ? msg('numbers.theory.primes.is_not_prime_primes_start_at', { N: sn(N) })
                            : res.prime
                              ? msg('numbers.theory.primes.is_prime', { N: sn(N) })
                              : msg('numbers.theory.primes.is_even_and_greater_than_2', { N: sn(N) }),
                    rule: 'answer',
                }),
            );
            res.steps = st;
        }
        return res;
    }
    let d = N - 1n,
        s = 0;
    while ((d & 1n) === 0n) {
        d >>= 1n;
        s++;
    }
    res.d = d;
    res.s = s;
    let bases, certain;
    if (opts.bases) {
        bases = opts.bases.map((b) => big(b));
        certain = false;
    } else ({ bases, certain } = mrBases(N));
    for (const a of bases) {
        if (bmod(a, N) === 0n) continue;
        const r = mrRound(N, a, d, s);
        res.rounds.push(r);
        if (!r.pass) {
            res.witness = a;
            break;
        }
    }
    res.prime = res.witness === null;
    res.certain = res.prime ? certain : true;
    if (!opts.steps) return res;
    st.push(
        step({
            title: msg('numbers.theory.primes.idea'),
            tex: `${tn(N)} - 1 = 2^{${s}} \\cdot ${tn(d)}`,
            text: msg('numbers.theory.primes.if_n_is_prime_fermat_s', { s, d: sn(d) }),
            rule: 'mr-idea',
        }),
    );
    for (const r of res.rounds) {
        let text;
        if (r.pass) {
            text =
                r.seq[0] === 1n
                    ? msg('numbers.theory.primes.chain_starts_at_1_base_does', { p: sn(r.a) })
                    : msg('numbers.theory.primes.chain_passes_through_1_just_as', { p: sn(N - 1n), p2: sn(r.a) });
        } else if (r.seq[r.seq.length - 1] === 1n) {
            const prev = r.seq[r.seq.length - 2];
            text = msg('numbers.theory.primes.we_reached_1_but_number_before', { prev: sn(prev), N: sn(N), p: sn(r.a) });
        } else {
            text = msg('numbers.theory.primes.chain_never_reached_1_or_1', { N: sn(N), p: sn(r.a) });
        }
        st.push(
            step({
                title: msg('numbers.theory.primes.base', { p: sn(r.a) }),
                tex: `${r.seq.map(tn).join(',\\ ')} \\pmod{${tn(N)}}`,
                text: text,
                rule: r.pass ? 'mr-pass' : 'mr-witness',
            }),
        );
    }
    st.push(
        step({
            title: msg('numbers.theory.primes.conclusion'),
            text: !res.prime
                ? msg('numbers.theory.primes.is_composite_miller_rabin_test_does', { N: sn(N) })
                : res.certain
                  ? msg('numbers.theory.primes.is_prime_for_numbers_below_3', { N: sn(N) })
                  : msg('numbers.theory.primes.is_almost_certainly_prime_none_of', { N: sn(N), length: res.rounds.length }),
            rule: 'answer',
        }),
    );
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
        let y = 2n + c,
            r = 1,
            q = 1n,
            g = 1n,
            x,
            ys = 0n;
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
                throw fail(msg('numbers.theory.primes.this_number_is_too_hard_to'), 'too-big');
            }
        } while (g === 1n);
        if (g === n) {
            do {
                ys = f(ys);
                g = gcdCore(babs(x - ys), n);
            } while (g === 1n);
        }
        if (g !== n) return g;
    }
    throw fail(msg('numbers.theory.primes.could_not_factor_number'), 'too-big');
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
    if (isPrimeBig(m)) {
        out.set(m, (out.get(m) ?? 0) + mult);
        return;
    }
    const pp = perfectPower(m);
    if (pp) {
        splitInto(pp.r, out, mult * pp.k);
        return;
    }
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
            do {
                m /= p;
                e++;
            } while (m % p === 0n);
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
    if (p === 2) return msg('numbers.theory.primes.last_digit_is_even').in(lang);
    if (p === 5) return msg('numbers.theory.primes.it_ends_in', { p: s[s.length - 1] }).in(lang);
    if (p === 3 && s.length > 1 && s.length <= 10) {
        const ds = s.split('').reduce((a, c) => a + +c, 0);
        return msg('numbers.theory.primes.digit_sum_is_divisible_by_3', { p: s.split('').join(' + '), ds }).in(lang);
    }
    return '';
}

/**
 * Prime factorisation of |n| → [{p: BigInt, e: number}] ascending (trial division to 10 000, then
 * Miller–Rabin + Pollard–Brent ρ). {steps: true} → {value, tex, ladder: [{n, p}], steps}.
 */
export function ntFactor(n, opts = {}) {
    const N = big(n);
    if (N === 0n) throw fail(msg('numbers.theory.primes.zero_cannot_be_factored_into_primes'), 'zero');
    if (!opts.steps) return mapToList(factorMap(N));

    const st = [];
    let m = babs(N);
    const groups = [];
    let skipped = [];
    let reason = null;
    if (N < 0n) {
        st.push(
            step({
                title: msg('numbers.theory.primes.take_out_minus_sign'),
                tex: `${tn(N)} = -${tn(m)}`,
                text: msg('numbers.theory.primes.we_factor_absolute_value_and_keep'),
            }),
        );
    }
    if (m === 1n) {
        st.push(
            step({ title: msg('numbers.theory.primes.one'), tex: '1 = 1', text: msg('numbers.theory.primes.one_has_no_prime_factors_it'), rule: 'answer' }),
        );
        return { value: [], tex: '1', ladder: [], steps: st };
    }
    st.push(
        step({
            title: msg('numbers.theory.primes.divide_by_primes_in_order'),
            text: msg('numbers.theory.primes.we_try_primes_in_increasing_order'),
            rule: 'trial-division',
        }),
    );
    const ladder = [];
    for (const p of SMALL_BIG) {
        if (p * p > m) {
            reason = 'sqrt';
            break;
        }
        if (m % p === 0n) {
            const before = m;
            let e = 0;
            do {
                ladder.push({ n: m, p });
                m /= p;
                e++;
            } while (m % p === 0n);
            groups.push({ p, e, before, after: m, skipped });
            skipped = [];
        } else skipped.push(p);
    }
    if (!reason) reason = m === 1n ? 'done' : 'big';
    for (const gr of groups) {
        const piece = (i) => `${i === 1 ? tn(gr.p) : `${tn(gr.p)}^{${i}}`} \\cdot ${tn(gr.before / gr.p ** BigInt(i))}`;
        const pieces = gr.e <= 5 ? Array.from({ length: gr.e }, (_, i) => piece(i + 1)) : [piece(1), '\\ldots', piece(gr.e)];
        const skipTxt = (l) => (gr.skipped.length ? msg('numbers.theory.primes.it_is_not_divisible_by', { p: listText(gr.skipped, l) }).in(l) : '');
        const times = (l) => msg('numbers.theory.primes.times', { e: gr.e }).in(l);
        st.push(
            step({
                title: msg('numbers.theory.primes.divide_by', { p: sn(gr.p) }),
                tex: `${tn(gr.before)} = ${pieces.join(' = ')}`,
                text: eachLanguage((l) =>
                    msg('numbers.theory.primes.is_divisible_by_is_left', {
                        l: skipTxt(l),
                        p: sn(gr.before),
                        p2: sn(gr.p),
                        p3: ruleHint(Number(gr.p), gr.before, l),
                        p4: (lng) =>
                            gr.e > 1
                                ? msg('numbers.theory.primes.we_divide_while_we_can', { l: times(l) }).in(lng)
                                : msg('numbers.theory.primes.we_divide').in(lng),
                        p5: sn(gr.after),
                    }).in(l),
                ),
                rule: 'divide',
                data: { p: gr.p, e: gr.e },
            }),
        );
    }
    const out = new Map(groups.map((g) => [g.p, g.e]));
    if (reason === 'sqrt' && m > 1n) {
        const r = Math.sqrt(Number(m));
        const whole = groups.length === 0;
        st.push(
            step({
                title: whole ? msg('numbers.theory.primes.number_is_prime') : msg('numbers.theory.primes.what_is_left_is_prime'),
                tex: eachLanguage((l) => `\\sqrt{${tn(m)}} \\approx ${dec(r, 1, l, true)}`),
                text: eachLanguage((l) =>
                    msg('numbers.theory.primes.and_none_divides_it_so_is', {
                        p: (lng) =>
                            whole
                                ? msg('numbers.theory.primes.we_have_tried_every_prime_up', { m: sn(m), r: dec(r, 1, l) }).in(lng)
                                : msg('numbers.theory.primes.is_left_we_have_already_tried', { m: sn(m), r: dec(r, 1, l) }).in(lng),
                        m: sn(m),
                    }).in(l),
                ),
                rule: 'sqrt-bound',
            }),
        );
        out.set(m, (out.get(m) ?? 0) + 1);
        ladder.push({ n: m, p: m });
    } else if (reason === 'big') {
        const rest = new Map();
        splitInto(m, rest);
        const ps = [...rest.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1));
        const certain = ps.every(([p]) => p < MR_LIMIT);
        const single = ps.length === 1 && ps[0][1] === 1;
        const digits = m.toString().length;
        st.push(
            step({
                title: single ? msg('numbers.theory.primes.large_prime_cofactor') : msg('numbers.theory.primes.large_cofactor'),
                tex: `${tn(m)} = ${ntFactorTex(ps.map(([p, e]) => ({ p, e })))}`,
                text: msg(single ? 'numbers.theory.primes.cofactor_is_prime' : 'numbers.theory.primes.cofactor_is_composite', {
                    trial: sn(TRIAL),
                    digits,
                    m: sn(m),
                    caveat: certain ? '' : msg(single ? 'numbers.theory.primes.error_probability' : 'numbers.theory.primes.probabilistically'),
                }),
                rule: single ? 'miller-rabin' : 'pollard-rho',
            }),
        );
        for (const [p, e] of ps) {
            out.set(p, (out.get(p) ?? 0) + e);
            for (let i = 0; i < e; i++) {
                ladder.push({ n: m, p });
                m /= p;
            }
        }
    }
    const value = [...out.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1)).map(([p, e]) => ({ p, e }));
    if (ladder.length > 1 && ladder.length <= 40) {
        const rowsTex = ladder.map(({ n: k, p }) => `${tn(k)} & ${tn(p)}`).join(' \\\\ ') + ' \\\\ 1 & ';
        st.push(
            step({
                title: msg('numbers.theory.primes.division_ladder'),
                tex: `\\begin{array}{r|l} ${rowsTex} \\end{array}`,
                text: msg('numbers.theory.primes.usual_notebook_layout_on_left_what'),
                rule: 'ladder',
            }),
        );
    }
    const tex = ntFactorTex(value);
    st.push(
        step({
            title: msg('numbers.theory.primes.answer'),
            tex: `${tn(N)} = ${N < 0n ? '-' : ''}${tex}`,
            text:
                value.length === 1 && value[0].e === 1
                    ? msg('numbers.theory.primes.is_prime_2', { p: sn(babs(N)) })
                    : msg('numbers.theory.primes.by_fundamental_theorem_of_arithmetic_this'),
            rule: 'answer',
        }),
    );
    return { value, tex, ladder, steps: st };
}

/** All positive divisors of n, ascending (BigInt). */
export function ntDivisors(n) {
    const N = big(n);
    if (N === 0n) throw fail(msg('numbers.theory.primes.zero_has_infinitely_many_divisors'), 'zero');
    let divs = [1n];
    for (const [p, e] of factorMap(N)) {
        const next = [];
        for (const d of divs) {
            let pk = 1n;
            for (let i = 0; i <= e; i++) {
                next.push(d * pk);
                pk *= p;
            }
        }
        divs = next;
        if (divs.length > 2_000_000) throw fail(msg('numbers.theory.primes.too_many_divisors'), 'too-big');
    }
    return divs.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

/** Number of divisors τ(n). */
export function ntTau(n) {
    const N = big(n);
    if (N === 0n) throw fail(msg('numbers.theory.primes.zero_has_infinitely_many_divisors'), 'zero');
    let t = 1n;
    for (const [, e] of factorMap(N)) t *= BigInt(e + 1);
    return t;
}

/** σ_k(n): the sum of the k-th powers of the divisors (k = 1 by default; k = 0 gives τ). */
export function ntSigma(n, k = 1) {
    const N = big(n);
    if (N === 0n) throw fail(msg('numbers.theory.primes.zero_has_infinitely_many_divisors'), 'zero');
    const K = BigInt(k);
    let s = 1n;
    for (const [p, e] of factorMap(N)) {
        if (K === 0n) {
            s *= BigInt(e + 1);
            continue;
        }
        const pk = p ** K;
        s *= (pk ** BigInt(e + 1) - 1n) / (pk - 1n);
    }
    return s;
}

/** Möbius function μ(n) ∈ {−1, 0, 1} (a number). */
export function ntMobius(n) {
    const N = big(n);
    if (N <= 0n) throw fail(msg('numbers.theory.primes.n_is_defined_for_positive_n'));
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
    if (N <= 0n) throw fail(msg('numbers.theory.primes.euler_s_function_is_defined_for'));
    const fs = mapToList(factorMap(N));
    let value = N;
    for (const { p } of fs) value = (value / p) * (p - 1n);
    if (!opts.steps) return value;
    const st = [];
    st.push(
        step({
            title: msg('numbers.theory.primes.what_we_count'),
            tex: `\\varphi(${tn(N)})`,
            text: msg('numbers.theory.primes.n_is_how_many_numbers_from'),
            rule: 'phi-def',
        }),
    );
    if (N === 1n) {
        st.push(
            step({
                title: msg('numbers.theory.primes.answer'),
                tex: '\\varphi(1) = 1',
                text: msg('numbers.theory.primes.one_is_coprime_to_itself'),
                rule: 'answer',
            }),
        );
        return { value, steps: st };
    }
    st.push(
        step({
            title: msg('numbers.theory.primes.factor_into_primes'),
            tex: `${tn(N)} = ${ntFactorTex(fs)}`,
            rule: 'factor',
            sub: ntFactor(N, { steps: true }).steps,
        }),
    );
    const brackets = fs.map(({ p }) => `\\left(1 - \\frac{1}{${tn(p)}}\\right)`).join('');
    const fracs = fs.map(({ p }) => `\\frac{${tn(p - 1n)}}{${tn(p)}}`).join(' \\cdot ');
    st.push(
        step({
            title: msg('numbers.theory.primes.euler_s_formula'),
            tex: `\\varphi(${tn(N)}) = ${tn(N)} ${brackets} = ${tn(N)} \\cdot ${fracs} = ${tn(value)}`,
            text: msg('numbers.theory.primes.among_any_p_consecutive_numbers_exactly'),
            rule: 'phi-formula',
        }),
    );
    if (fs.length > 1 || fs[0].e > 1) {
        const alt = fs.map(({ p, e }) => (e === 1 ? `${tn(p - 1n)}` : `(${tn(p ** BigInt(e))} - ${tn(p ** BigInt(e - 1))})`)).join(' \\cdot ');
        st.push(
            step({
                title: msg('numbers.theory.primes.another_way'),
                tex: `\\varphi(${tn(N)}) = ${fs.map(({ p, e }) => `\\varphi(${e === 1 ? tn(p) : `${tn(p)}^{${e}}`})`).join('\\,')} = ${alt} = ${tn(value)}`,
                text: msg('numbers.theory.primes.is_multiplicative_for_coprime_factors_values'),
                rule: 'phi-multiplicative',
            }),
        );
    }
    if (N <= 100n) {
        const list = [];
        for (let k = 1n; k <= N; k++) if (gcdCore(k, N) === 1n) list.push(k);
        st.push(
            step({
                title: msg('numbers.theory.primes.check_by_listing'),
                text: msg('numbers.theory.primes.coprime_to_of_them', { N: sn(N), p: list.map(sn).join(', '), length: list.length }),
                rule: 'check',
            }),
        );
    }
    return { value, steps: st };
}

// ---------------------------------------------------------------- primes

/** Primes ≤ n as a plain array of numbers (sieve of Eratosthenes; n ≤ 10⁸). */
export function ntPrimesUpTo(n) {
    n = Math.floor(Number(n));
    if (!(n >= 2)) return [];
    if (n > 1e8) throw fail(msg('numbers.theory.primes.bound_is_too_large_for_sieve'), 'too-big');
    const comp = sieveBytes(n);
    const out = [];
    for (let i = 2; i <= n; i++) if (!comp[i]) out.push(i);
    return out;
}

/** Sieve data for widgets: {primes, isPrime: Uint8Array, spf: Int32Array} (spf = smallest prime factor, 0 for 0 and 1). */
export function ntSieve(n) {
    n = Math.max(1, Math.floor(Number(n)));
    if (n > 2e7) throw fail(msg('numbers.theory.primes.bound_is_too_large_at_most'), 'too-big');
    const spf = new Int32Array(n + 1);
    const primes = [];
    for (let i = 2; i <= n; i++) {
        if (spf[i] === 0) {
            spf[i] = i;
            primes.push(i);
        }
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
    if (n > 1e11) throw fail(msg('numbers.theory.primes.n_is_too_large_at_most'), 'too-big');
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
        const sp = lo[p - 1],
            p2 = p * p;
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
    N += N & 1n ? 2n : 1n;
    while (!isPrimeBig(N)) N += 2n;
    return N;
}

/** The largest prime < n, or null when there is none. */
export function ntPrevPrime(n) {
    let N = big(n);
    if (N <= 2n) return null;
    if (N === 3n) return 2n;
    N -= N & 1n ? 2n : 1n;
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
    while (N > 0n) {
        s += N % B;
        N /= B;
    }
    return s;
}
