// numeric/signals — DFT, FFT and Fourier coefficients.

import { evalSafe, fin, needFn } from './common.js';

// ---------------------------------------------------------------- signals

/** Direct DFT (O(N²), exact length): X_k = Σ x_j·e^(∓2πijk/N). {inverse} divides by N. → {re, im}. */
export function numDft(re, im = null, opts = {}) {
    const N = re.length;
    const R = new Float64Array(N),
        I = new Float64Array(N);
    const cs = new Float64Array(N),
        sn = new Float64Array(N);
    for (let k = 0; k < N; k++) {
        cs[k] = Math.cos((2 * Math.PI * k) / N);
        sn[k] = Math.sin((2 * Math.PI * k) / N);
    }
    const sign = opts.inverse ? 1 : -1;
    for (let k = 0; k < N; k++) {
        let sr = 0,
            si = 0;
        for (let j = 0; j < N; j++) {
            const idx = (k * j) % N;
            const c = cs[idx],
                s = sign * sn[idx];
            const xr = re[j],
                xi = im ? im[j] : 0;
            sr += xr * c - xi * s;
            si += xr * s + xi * c;
        }
        R[k] = opts.inverse ? sr / N : sr;
        I[k] = opts.inverse ? si / N : si;
    }
    return { re: R, im: I };
}

/** Radix-2 FFT; the input is zero-padded to a power of two. {inverse} divides by N. → {re, im}. */
export function numFft(re, im = null, opts = {}) {
    let n = 1;
    while (n < re.length) n <<= 1;
    const R = new Float64Array(n),
        I = new Float64Array(n);
    R.set(re);
    if (im) I.set(im);
    for (let i = 1, j = 0; i < n; i++) {
        let bit = n >> 1;
        for (; j & bit; bit >>= 1) j ^= bit;
        j ^= bit;
        if (i < j) {
            let t = R[i];
            R[i] = R[j];
            R[j] = t;
            t = I[i];
            I[i] = I[j];
            I[j] = t;
        }
    }
    const sign = opts.inverse ? 1 : -1;
    for (let len = 2; len <= n; len <<= 1) {
        const half = len >> 1;
        const wr = new Float64Array(half),
            wi = new Float64Array(half);
        for (let k = 0; k < half; k++) {
            wr[k] = Math.cos((2 * Math.PI * k) / len);
            wi[k] = sign * Math.sin((2 * Math.PI * k) / len);
        }
        for (let i = 0; i < n; i += len) {
            for (let k = 0; k < half; k++) {
                const a = i + k,
                    b = a + half;
                const tr = R[b] * wr[k] - I[b] * wi[k];
                const ti = R[b] * wi[k] + I[b] * wr[k];
                R[b] = R[a] - tr;
                I[b] = I[a] - ti;
                R[a] += tr;
                I[a] += ti;
            }
        }
    }
    if (opts.inverse)
        for (let i = 0; i < n; i++) {
            R[i] /= n;
            I[i] /= n;
        }
    return { re: R, im: I };
}

/** Inverse FFT (the length must already be a power of two for an exact round trip). */
export function numIfft(re, im = null) {
    return numFft(re, im, { inverse: true });
}

/**
 * Fourier coefficients of a T-periodic f: f(x) ≈ a[0]/2 + Σₖ (a[k]·cos(kωx) + b[k]·sin(kωx)),
 * ω = 2π/T, k = 1..N. The period starts at `from` (−T/2 by default); midpoint sums with
 * {samples} points (max(4096, 64N)). → {a: [a0 … aN], b: [0, b1 … bN], period, mean}.
 */
export function numFourierCoefficients(f, N, period = 2 * Math.PI, opts = {}) {
    needFn(f);
    const T = period;
    const from = opts.from ?? -T / 2;
    const M = opts.samples ?? Math.max(4096, 64 * N);
    const w = (2 * Math.PI) / T;
    const a = new Array(N + 1).fill(0),
        b = new Array(N + 1).fill(0);
    for (let j = 0; j < M; j++) {
        const x = from + ((j + 0.5) * T) / M;
        const y = evalSafe(f, x);
        if (!fin(y)) continue;
        for (let k = 0; k <= N; k++) {
            a[k] += y * Math.cos(k * w * x);
            if (k) b[k] += y * Math.sin(k * w * x);
        }
    }
    for (let k = 0; k <= N; k++) {
        a[k] *= 2 / M;
        b[k] *= 2 / M;
    }
    return { a, b, period: T, mean: a[0] / 2 };
}

/** Value of the Fourier partial sum with the coefficients of numFourierCoefficients (first n harmonics). */
export function numFourierEval(coefs, x, n = coefs.a.length - 1) {
    const w = (2 * Math.PI) / coefs.period;
    let s = coefs.a[0] / 2;
    for (let k = 1; k <= Math.min(n, coefs.a.length - 1); k++) s += coefs.a[k] * Math.cos(k * w * x) + coefs.b[k] * Math.sin(k * w * x);
    return s;
}
