// linalg/common — tiny helpers: bilingual steps, row names, subscripts.

import { MathError } from '../core/rational.js';
import { msg } from '../i18n/index.js';

// ---------------------------------------------------------------- tiny internal helpers

export const fail = (msg, code = null) => new MathError(msg, null, null, code);
export function S(title, tex, text, extra) {
    const s = { title };
    if (tex != null) s.tex = tex;
    if (text != null) s.text = text;
    if (extra) Object.assign(s, extra);
    if (Array.isArray(s.sub) && !s.sub.length) delete s.sub;
    return s;
}
export const qs = (x) => x.toString().replace('-', '\u2212');
export const qt = (x) => x.toTex();
/** Q as a TeX factor: parenthesised when negative. */
export const qtp = (x) => (x.isNeg() ? `\\left(${qt(x)}\\right)` : qt(x));
export const E_ = (l) => msg('linalg.common.i').in(l);
/** A − λE with a concrete λ: A - E, A + 2E, A - \frac{1}{2}E, A. */
export const shiftTex = (lam, l) => (lam.isZero() ? 'A' : `A ${lam.isNeg() ? '+' : '-'} ${lam.abs().isOne() ? '' : qt(lam.abs())}${E_(l)}`);

export const R = (i) => `R_{${i + 1}}`;
const SUBS = '₀₁₂₃₄₅₆₇₈₉';
export const sub = (n) =>
    String(n)
        .split('')
        .map((c) => SUBS[+c])
        .join('');
