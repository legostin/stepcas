import { msg, notation, DEFAULT_LANGUAGE, inLanguage, MACHINE } from '../i18n/index.js';
// rational — exact rational numbers on BigInt, BigInt helpers, and MathError (used by the whole engine).
//
//   new Q(3n, 4n)            normalised: reduced, denominator > 0
//   Q.of(0.1) → 1/10         numbers go through their shortest decimal string
//   Q.of('2,5') → 5/2        strings: "3/4", "-2.5", "2,5", "1e-3", "0.(3)" (repeating), "1.5/2"
//   q.add(1).mul('3/4')      arithmetic methods accept anything Q.of() accepts

/** Error with a bilingual message and an optional position in the parsed text. */
export class MathError extends Error {
    /**
     * @param {import('../i18n/index.js').Msg|string|Object<string, string>} msg  a message, a string or {lang: text}
     * @param {number|{pos?: number, len?: number, code?: string}} [pos]
     * @param {number} [len]
     * @param {string} [code]  short machine-readable id ('div0', 'syntax', 'too-big', …)
     */
    constructor(msg, pos = null, len = null, code = null) {
        // a message (from i18n) stays language-neutral; strings and {ru, en} objects are taken as they are
        // a message (i18n), a string (the same in every language) or a {lang: text} object is kept as it is;
        // Error.message is its machine (English) text
        const m = msg ?? '';
        super(inLanguage(m, MACHINE));
        if (pos !== null && typeof pos === 'object') ({ pos = null, len = null, code = null } = pos);
        this.name = 'MathError';
        this.msg = m;
        this.pos = pos;
        this.len = len;
        this.code = code;
    }

    /** Message in the given language. */
    text(lang = DEFAULT_LANGUAGE) {
        return inLanguage(this.msg, lang);
    }
}

const DIV0 = msg('core.rational.division_by_zero');
const TOO_BIG = msg('core.rational.number_gets_too_large');

// ---------------------------------------------------------------- BigInt helpers

function toBig(x) {
    if (typeof x === 'bigint') return x;
    if (typeof x === 'number' && Number.isInteger(x)) return BigInt(x);
    if (typeof x === 'string' && /^[+-]?\d+$/.test(x.trim())) return BigInt(x.trim());
    throw new TypeError(`not an integer: ${x}`);
}

export function bigAbs(a) {
    a = toBig(a);
    return a < 0n ? -a : a;
}

export function bigGcd(a, b) {
    a = bigAbs(a);
    b = bigAbs(b);
    while (b) [a, b] = [b, a % b];
    return a;
}

export function bigLcm(a, b) {
    a = bigAbs(a);
    b = bigAbs(b);
    if (!a || !b) return 0n;
    return (a / bigGcd(a, b)) * b;
}

/** Number of bits of |n| (0 for 0). */
export function bigBitLength(n) {
    n = bigAbs(n);
    if (n === 0n) return 0;
    const h = n.toString(16);
    return (h.length - 1) * 4 + (32 - Math.clz32(parseInt(h[0], 16)));
}

/** floor(sqrt(n)) for n ≥ 0. */
export function bigIsqrt(n) {
    n = toBig(n);
    if (n < 0n) throw new MathError(msg('core.rational.square_root_of_negative_number'));
    if (n < 2n) return n;
    if (n < 2n ** 52n) {
        let r = BigInt(Math.floor(Math.sqrt(Number(n))));
        while (r * r > n) r--;
        while ((r + 1n) * (r + 1n) <= n) r++;
        return r;
    }
    let x = 1n << BigInt(Math.ceil(bigBitLength(n) / 2));
    for (;;) {
        const y = (x + n / x) >> 1n;
        if (y >= x) break;
        x = y;
    }
    while (x * x > n) x--;
    while ((x + 1n) * (x + 1n) <= n) x++;
    return x;
}

/** floor(n^(1/k)) for n ≥ 0; for n < 0 and odd k returns −floor(|n|^(1/k)). */
export function bigIroot(n, k) {
    n = toBig(n);
    k = Number(k);
    if (!Number.isInteger(k) || k < 1) throw new TypeError('root index must be a positive integer');
    if (k === 1) return n;
    if (n < 0n) {
        if (k % 2 === 0) throw new MathError(msg('core.rational.even_root_of_negative_number'));
        return -bigIroot(-n, k);
    }
    if (k === 2) return bigIsqrt(n);
    if (n < 2n) return n;
    const K = BigInt(k);
    const bits = bigBitLength(n);
    if (bits < k) return 1n;
    if (bits < 900) {
        // a double estimate is close; fix it up exactly
        let r = BigInt(Math.floor(Math.pow(Number(n), 1 / k)));
        while (r > 0n && r ** K > n) r--;
        while ((r + 1n) ** K <= n) r++;
        return r;
    }
    let x = 1n << BigInt(Math.ceil(bits / k));
    for (;;) {
        const y = ((K - 1n) * x + n / x ** (K - 1n)) / K;
        if (y >= x) break;
        x = y;
    }
    while (x ** K > n) x--;
    while ((x + 1n) ** K <= n) x++;
    return x;
}

const TRIAL_LIMIT = 100000;

/**
 * n = out^k · in with `in` free of k-th powers: rootExtract(12n, 2) → {out: 2n, in: 3n}.
 * Negative n: odd k gives a negative `out` and positive `in`; even k keeps the sign in `in`.
 * Numbers are checked by trial division up to 100 000 plus an exact perfect-power test of what is
 * left, so for huge n with two large equal prime factors `in` may still hide a k-th power.
 */
export function rootExtract(n, k) {
    n = toBig(n);
    k = Number(k);
    if (!Number.isInteger(k) || k < 1) throw new TypeError('root index must be a positive integer');
    if (n === 0n) return { out: 0n, in: 1n };
    if (k === 1) return { out: n, in: 1n };
    let sign = 1n;
    if (n < 0n) {
        n = -n;
        sign = -1n;
    }
    const K = BigInt(k);
    let out = 1n;
    let rest = 1n;
    let m = n;
    for (let p = 2; p <= TRIAL_LIMIT; p += p === 2 ? 1 : 2) {
        const P = BigInt(p);
        if (P * P > m) break;
        if (m % P) continue;
        let e = 0;
        while (m % P === 0n) {
            m /= P;
            e++;
        }
        const q = Math.floor(e / k);
        if (q) out *= P ** BigInt(q);
        if (e % k) rest *= P ** BigInt(e % k);
    }
    if (m > 1n) {
        const r = bigIroot(m, k);
        if (r ** K === m) out *= r;
        else rest *= m;
    }
    if (sign < 0n) {
        if (k % 2) out = -out;
        else rest = -rest;
    }
    return { out, in: rest };
}

// ---------------------------------------------------------------- Q

const DEC_RE = /^([+-]?)(\d*)(?:[.,](\d*))?(?:\((\d+)\))?(?:[eE]([+-]?\d+))?$/;
const MAX_POW_BITS = 400000;

function parseDecimal(s) {
    const m = DEC_RE.exec(s);
    if (!m || (!m[2] && !m[3] && !m[4])) return null;
    const [, sg, int = '', frac = '', rep = '', ex = ''] = m;
    const e = ex ? Number(ex) : 0;
    if (Math.abs(e) > 100000) throw new MathError(TOO_BIG, null, null, 'too-big');
    let q;
    if (rep) {
        // 0.12(345) = (12345 − 12) / 99900
        const a = BigInt((int || '0') + frac + rep);
        const b = BigInt((int || '0') + frac);
        q = new Q(a - b, (10n ** BigInt(rep.length) - 1n) * 10n ** BigInt(frac.length));
    } else {
        q = new Q(BigInt((int || '0') + frac), 10n ** BigInt(frac.length));
    }
    if (e) q = e > 0 ? q.mul(new Q(10n ** BigInt(e))) : q.div(new Q(10n ** BigInt(-e)));
    return sg === '-' ? q.neg() : q;
}

export class Q {
    /** @param {bigint|number} n  @param {bigint|number} [d] */
    constructor(n, d = 1n) {
        n = toBig(n);
        d = toBig(d);
        if (d === 0n) throw new MathError(DIV0, null, null, 'div0');
        if (d < 0n) {
            n = -n;
            d = -d;
        }
        if (d !== 1n) {
            const g = bigGcd(n, d);
            if (g > 1n) {
                n /= g;
                d /= g;
            }
        }
        this.n = n;
        this.d = d;
        Object.freeze(this);
    }

    /** From Q, bigint, number (integer or finite decimal), or string. */
    static of(x) {
        if (x instanceof Q) return x;
        if (typeof x === 'bigint') return new Q(x);
        if (typeof x === 'number') {
            if (!Number.isFinite(x)) throw new MathError(msg('core.rational.number_must_be_finite'), null, null, 'nan');
            if (Number.isSafeInteger(x)) return new Q(BigInt(x));
            return parseDecimal(String(x));
        }
        if (typeof x === 'string') {
            const s = x.trim().replace(/[\s\u00a0\u202f]/g, '').replace(/[−–]/g, '-');
            const slash = s.indexOf('/');
            const bad = () => new MathError(msg('core.rational.not_number', { x }), null, null, 'nan');
            if (slash >= 0) {
                const a = parseDecimal(s.slice(0, slash));
                const b = parseDecimal(s.slice(slash + 1));
                if (!a || !b) throw bad();
                return a.div(b);
            }
            const q = parseDecimal(s);
            if (!q) throw bad();
            return q;
        }
        throw new MathError(msg('core.rational.not_number_2'), null, null, 'nan');
    }

    static max(a, b) {
        a = Q.of(a);
        b = Q.of(b);
        return a.cmp(b) >= 0 ? a : b;
    }

    static min(a, b) {
        a = Q.of(a);
        b = Q.of(b);
        return a.cmp(b) <= 0 ? a : b;
    }

    get num() {
        return this.n;
    }

    get den() {
        return this.d;
    }

    add(b) {
        b = Q.of(b);
        if (this.d === 1n && b.d === 1n) return new Q(this.n + b.n);
        return new Q(this.n * b.d + b.n * this.d, this.d * b.d);
    }

    sub(b) {
        b = Q.of(b);
        if (this.d === 1n && b.d === 1n) return new Q(this.n - b.n);
        return new Q(this.n * b.d - b.n * this.d, this.d * b.d);
    }

    mul(b) {
        b = Q.of(b);
        if (this.d === 1n && b.d === 1n) return new Q(this.n * b.n);
        return new Q(this.n * b.n, this.d * b.d);
    }

    div(b) {
        b = Q.of(b);
        if (b.n === 0n) throw new MathError(DIV0, null, null, 'div0');
        return new Q(this.n * b.d, this.d * b.n);
    }

    neg() {
        return new Q(-this.n, this.d);
    }

    inv() {
        if (this.n === 0n) throw new MathError(DIV0, null, null, 'div0');
        return new Q(this.d, this.n);
    }

    /** Integer power (negative allowed; 0^0 = 1). Throws MathError when the result would be huge. */
    pow(k) {
        if (k instanceof Q) {
            if (!k.isInt()) throw new TypeError('Q.pow needs an integer exponent');
            k = k.n;
        }
        k = toBig(k);
        if (k === 0n) return Q.ONE;
        if (k < 0n) return this.inv().pow(-k);
        if (this.n === 0n || (this.d === 1n && this.n === 1n)) return this;
        if (this.d === 1n && this.n === -1n) return k % 2n === 0n ? Q.ONE : this;
        const bits = Math.max(bigBitLength(this.n), bigBitLength(this.d));
        if (bits * Number(k) > MAX_POW_BITS) throw new MathError(TOO_BIG, null, null, 'too-big');
        return new Q(this.n ** k, this.d ** k);
    }

    /** Exact k-th root when it is rational, else null (odd roots of negatives are negative). */
    exactRoot(k) {
        k = Number(k);
        if (this.n < 0n && k % 2 === 0) return null;
        const a = bigIroot(this.n, k);
        const b = bigIroot(this.d, k);
        const K = BigInt(k);
        return a ** K === this.n && b ** K === this.d ? new Q(a, b) : null;
    }

    cmp(b) {
        b = Q.of(b);
        const x = this.n * b.d - b.n * this.d;
        return x < 0n ? -1 : x > 0n ? 1 : 0;
    }

    eq(b) {
        b = Q.of(b);
        return this.n === b.n && this.d === b.d;
    }

    lt(b) {
        return this.cmp(b) < 0;
    }

    gt(b) {
        return this.cmp(b) > 0;
    }

    le(b) {
        return this.cmp(b) <= 0;
    }

    ge(b) {
        return this.cmp(b) >= 0;
    }

    isZero() {
        return this.n === 0n;
    }

    isOne() {
        return this.n === 1n && this.d === 1n;
    }

    isInt() {
        return this.d === 1n;
    }

    isNeg() {
        return this.n < 0n;
    }

    isPos() {
        return this.n > 0n;
    }

    sign() {
        return this.n < 0n ? -1 : this.n > 0n ? 1 : 0;
    }

    abs() {
        return this.n < 0n ? new Q(-this.n, this.d) : this;
    }

    floor() {
        if (this.d === 1n) return this;
        const m = ((this.n % this.d) + this.d) % this.d;
        return new Q((this.n - m) / this.d);
    }

    ceil() {
        if (this.d === 1n) return this;
        return this.floor().add(Q.ONE);
    }

    trunc() {
        return new Q(this.n / this.d);
    }

    /** Round half away from zero (school rounding: 2.5 → 3, −2.5 → −3). */
    round() {
        if (this.d === 1n) return this;
        const a = this.abs();
        const r = new Q(2n * a.n + a.d, 2n * a.d).floor();
        return this.n < 0n ? r.neg() : r;
    }

    /** Nearest double (works for huge numerators/denominators too). */
    toNumber() {
        const { n, d } = this;
        if (d === 1n) return Number(n);
        const an = n < 0n ? -n : n;
        const nb = bigBitLength(an);
        const db = bigBitLength(d);
        if (nb < 1000 && db < 1000) return Number(n) / Number(d);
        const shift = 64 - (nb - db);
        const q = shift >= 0 ? (an << BigInt(shift)) / d : an / (d << BigInt(-shift));
        const v = Number(q) * Math.pow(2, -shift / 2) * Math.pow(2, -shift / 2);
        return n < 0n ? -v : v;
    }

    /** "3/4", "-2". */
    toString() {
        return this.d === 1n ? this.n.toString() : `${this.n}/${this.d}`;
    }

    toJSON() {
        return this.toString();
    }

    /** Denominator has no primes but 2 and 5. */
    isFiniteDecimal() {
        let d = this.d;
        while (d % 2n === 0n) d /= 2n;
        while (d % 5n === 0n) d /= 5n;
        return d === 1n;
    }

    /**
     * Decimal string rounded (half away from zero) to at most `digits` fractional digits, trailing
     * zeros removed: Q(1,3).toDecimalString(4) → "0.3333"; RU uses a decimal comma.
     */
    toDecimalString(digits = 10, lang = MACHINE) {
        digits = Math.max(0, Math.floor(digits));
        const scale = 10n ** BigInt(digits);
        const a = this.abs();
        const v = (2n * a.n * scale + a.d) / (2n * a.d);
        const neg = this.n < 0n && v !== 0n;
        let s = v.toString();
        if (digits > 0) {
            s = s.padStart(digits + 1, '0');
            const int = s.slice(0, s.length - digits);
            const frac = s.slice(s.length - digits).replace(/0+$/, '');
            s = frac ? `${int}${notation(lang).decimalText}${frac}` : int;
        }
        return (neg ? '-' : '') + s;
    }

    /**
     * Periodic decimal expansion: {sign, int: bigint, pre: '1', period: '6'} for 1/6 = 0.1(6);
     * period '' for finite decimals; null when the digits run longer than maxDigits.
     */
    toPeriodic(maxDigits = 200) {
        const a = this.abs();
        const int = a.n / a.d;
        let r = a.n % a.d;
        const seen = new Map();
        let digits = '';
        while (r !== 0n && !seen.has(r)) {
            if (digits.length >= maxDigits) return null;
            seen.set(r, digits.length);
            r *= 10n;
            digits += (r / a.d).toString();
            r %= a.d;
        }
        if (r === 0n) return { sign: this.sign(), int, pre: digits, period: '' };
        const at = seen.get(r);
        return { sign: this.sign(), int, pre: digits.slice(0, at), period: digits.slice(at) };
    }

    /** "0,1(6)" (RU) / "0.1(6)" (EN); null when the period is too long. */
    toPeriodicString(lang = MACHINE, maxDigits = 200) {
        const p = this.toPeriodic(maxDigits);
        if (!p) return null;
        const sep = notation(lang).decimalText;
        const frac = p.pre + (p.period ? `(${p.period})` : '');
        return (p.sign < 0 ? '-' : '') + p.int.toString() + (frac ? sep + frac : '');
    }

    /** "\frac{3}{4}", "-\frac{1}{2}", "2" (the language does not matter for fractions). */
    toTex(lang = DEFAULT_LANGUAGE) {
        void lang;
        if (this.d === 1n) return this.n.toString();
        const s = `\\frac{${this.n < 0n ? -this.n : this.n}}{${this.d}}`;
        return this.n < 0n ? `-${s}` : s;
    }
}

Q.ZERO = new Q(0n);
Q.ONE = new Q(1n);
Q.MINUS_ONE = new Q(-1n);
Q.TWO = new Q(2n);
Q.HALF = new Q(1n, 2n);
