// numeric/common — argument checks shared by the numerical methods.

import { MathError } from '../../core/rational.js';
import { msg } from '../../i18n/index.js';

export const fail = (msg, code = null) => new MathError(msg, null, null, code);
export const EPS = Number.EPSILON;
export const fin = Number.isFinite;

export function evalSafe(f, x) {
    let y;
    try { y = f(x); } catch { return NaN; }
    return typeof y === 'number' ? y : Number(y);
}
export function needFn(f) {
    if (typeof f !== 'function') throw fail(msg('numbers.numeric.common.function_is_required'), 'type');
}
export function needInterval(a, b) {
    if (!fin(a) || !fin(b)) throw fail(msg('numbers.numeric.common.ends_of_interval_must_be_finite'), 'range');
}

/** n evenly spaced points from a to b inclusive. */
export function numLinspace(a, b, n) {
    n = Math.floor(n);
    if (n < 1) return [];
    if (n === 1) return [a];
    const out = new Array(n);
    const h = (b - a) / (n - 1);
    for (let i = 0; i < n; i++) out[i] = i === n - 1 ? b : a + i * h;
    return out;
}
