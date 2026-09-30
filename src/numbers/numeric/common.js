// numeric/common — argument checks shared by the numerical methods.

import { MathError } from '../../core/rational.js';

export const fail = (ru, en, code = null) => new MathError({ ru, en }, null, null, code);
export const EPS = Number.EPSILON;
export const fin = Number.isFinite;

export function evalSafe(f, x) {
    let y;
    try { y = f(x); } catch { return NaN; }
    return typeof y === 'number' ? y : Number(y);
}
export function needFn(f) {
    if (typeof f !== 'function') throw fail('Нужна функция.', 'A function is required.', 'type');
}
export function needInterval(a, b) {
    if (!fin(a) || !fin(b)) throw fail('Концы отрезка должны быть конечными числами.', 'The ends of the interval must be finite numbers.', 'range');
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
