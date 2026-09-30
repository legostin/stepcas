// theory/common — tiny helpers: reading integers and fractions, bilingual steps.

import { MathError, Q } from '../../core/rational.js';
import { msg, notation, decimalIn } from '../../i18n/index.js';

// ---------------------------------------------------------------- tiny internal helpers

export const fail = (msg, code = null) => new MathError(msg, null, null, code);

export const babs = (a) => (a < 0n ? -a : a);
export const bmod = (a, m) => ((a % m) + m) % m;

function grp(d, sep) {
    return d.length <= 4 ? d : d.replace(/\B(?=(\d{3})+(?!\d))/g, sep);
}
/** TeX for an integer: 600\,851\,475\,143 (groups from five digits on). */
export function tn(n) {
    const s = String(n);
    return s[0] === '-' ? '-' + grp(s.slice(1), '\\,') : grp(s, '\\,');
}
/** TeX, parenthesised when negative (for products). */
export function tp(n) {
    return String(n)[0] === '-' ? `(${tn(n)})` : tn(n);
}
/** Plain text for an integer: narrow no-break spaces between groups, a real minus sign. */
export function sn(n) {
    const s = String(n);
    return s[0] === '-' ? '−' + grp(s.slice(1), '\u202f') : grp(s, '\u202f');
}
/** A decimal approximation in the language's notation (2,5 or 2.5); `tex` gives 2{,}5. */
export function dec(x, digits, lang, tex = false) {
    let s = Number(x).toFixed(digits);
    if (s.includes('.')) s = s.replace(/0+$/, '').replace(/\.$/, '');
    s = decimalIn(s, lang, { tex });
    return tex ? s : s.replace('-', '−');
}
const SUBS = '₀₁₂₃₄₅₆₇₈₉';
export const subscript = (n) =>
    String(n)
        .split('')
        .map((c) => SUBS[+c])
        .join('');
/** k·x in TeX with the coefficient 1 / −1 hidden. */
export const coefX = (a, v = 'x') => (a === 1n ? v : a === -1n ? `-${v}` : `${tn(a)}${v}`);

/** «3, 5 и 7» / «3, 5, 7, …, 67» */
export function listText(items, lang) {
    const a = items.map(sn);
    if (a.length === 1) return a[0];
    if (a.length <= 4) return a.slice(0, -1).join(', ') + msg('numbers.theory.common.and').in(lang) + a[a.length - 1];
    return `${a[0]}, ${a[1]}, ${a[2]}, …, ${a[a.length - 1]}`;
}

export const G = (l, a, b) => msg('numbers.theory.common.formula', { a: tn(a), b: tn(b) }).in(l);
export const Lc = (l, a, b) => msg('numbers.theory.common.lcm', { a: tn(a), b: tn(b) }).in(l);
export const gT = (l, a, b) => msg('numbers.theory.common.gcd', { a: sn(a), b: sn(b) }).in(l);

/** Anything integer-like → BigInt. */
export function big(x, what) {
    if (typeof x === 'bigint') return x;
    if (typeof x === 'number') {
        if (Number.isInteger(x)) return BigInt(x);
        throw fail(
            msg(what ? 'numbers.theory.common.integer_is_required_for' : 'numbers.theory.common.integer_is_required_got', {
                what,
                x: (lng) => String(x).replace('.', notation(lng).decimalText),
            }),
            'not-int',
        );
    }
    if (typeof x === 'string') {
        const s = x.replace(/[\s_\u00a0\u202f\u2009']/g, '').replace(/^[−–]/, '-');
        if (/^[+-]?\d+$/.test(s)) return BigInt(s);
        throw fail(msg('numbers.theory.common.is_not_integer', { x }), 'not-int');
    }
    if (x instanceof Q) {
        if (x.isInt()) return x.n;
        throw fail(msg('numbers.theory.common.integer_is_required_not_fraction'), 'not-int');
    }
    throw fail(msg('numbers.theory.common.integer_is_required'), 'not-int');
}

/** Exact value of a double as {num, den}. */
export function doubleExact(x) {
    const dv = new DataView(new ArrayBuffer(8));
    dv.setFloat64(0, x);
    const hi = dv.getUint32(0),
        lo = dv.getUint32(4);
    const exp = (hi >>> 20) & 0x7ff;
    let mant = (BigInt(hi & 0xfffff) << 32n) | BigInt(lo);
    let e;
    if (exp === 0) e = -1074;
    else {
        mant |= 1n << 52n;
        e = exp - 1075;
    }
    let num = mant,
        den = 1n;
    if (e > 0) num <<= BigInt(e);
    else den <<= BigInt(-e);
    while (num % 2n === 0n && den % 2n === 0n && den > 1n) {
        num /= 2n;
        den /= 2n;
    }
    return { num: hi >>> 31 ? -num : num, den };
}

/** Anything rational-like → {num, den}, reduced, den > 0. */
export function ratOf(x) {
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
    throw fail(msg('numbers.theory.common.number_is_required'), 'nan');
}

export function gcdCore(a, b) {
    a = babs(a);
    b = babs(b);
    while (b) [a, b] = [b, a % b];
    return a;
}

export function powmod(b, e, m) {
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
export function invCore(a, m) {
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

export function sieveBytes(n) {
    const comp = new Uint8Array(n + 1);
    comp[0] = 1;
    if (n >= 1) comp[1] = 1;
    for (let i = 2; i * i <= n; i++) if (!comp[i]) for (let j = i * i; j <= n; j += i) comp[j] = 1;
    return comp;
}
export const TRIAL = 10000;
export const SMALL = (() => {
    const c = sieveBytes(TRIAL);
    const out = [];
    for (let i = 2; i <= TRIAL; i++) if (!c[i]) out.push(i);
    return out;
})();
export const SMALL_BIG = SMALL.map(BigInt);
