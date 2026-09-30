// numeric/ode — Euler, Runge–Kutta, adaptive steps and ready-made systems (SIR, Lotka–Volterra, pendulum, Lorenz).

import { fail, fin, needFn, numLinspace } from './common.js';

// ---------------------------------------------------------------- ODEs

const vadd = (y, k, s) => (typeof y === 'number' ? y + s * k : y.map((v, i) => v + s * k[i]));
function vcomb(y, h, ks, cs) {
    if (typeof y === 'number') { let s = y; for (let i = 0; i < ks.length; i++) if (cs[i]) s += h * cs[i] * ks[i]; return s; }
    return y.map((v, j) => { let s = v; for (let i = 0; i < ks.length; i++) if (cs[i]) s += h * cs[i] * ks[i][j]; return s; });
}
const vcopy = (y) => (typeof y === 'number' ? y : y.slice());
function checkY(y0) {
    if (typeof y0 === 'number') return;
    if (!Array.isArray(y0) || !y0.every((v) => typeof v === 'number')) throw fail('Начальное условие — число или массив чисел.', 'The initial value must be a number or an array of numbers.', 'type');
}

/** Euler's method: n steps of size h from (t0, y0); y is a number or an array. → {t: [], y: []}. */
export function numEuler(f, t0, y0, h, n) {
    needFn(f);
    checkY(y0);
    const T = [t0], Y = [vcopy(y0)];
    let t = t0, y = vcopy(y0);
    for (let i = 0; i < n; i++) {
        y = vadd(y, f(t, y), h);
        t = t0 + (i + 1) * h;
        T.push(t);
        Y.push(y);
    }
    return { t: T, y: Y };
}

/** Classic 4th-order Runge–Kutta: n steps of size h. → {t: [], y: []}. */
export function numRk4(f, t0, y0, h, n) {
    needFn(f);
    checkY(y0);
    const T = [t0], Y = [vcopy(y0)];
    let t = t0, y = vcopy(y0);
    for (let i = 0; i < n; i++) {
        const k1 = f(t, y);
        const k2 = f(t + h / 2, vadd(y, k1, h / 2));
        const k3 = f(t + h / 2, vadd(y, k2, h / 2));
        const k4 = f(t + h, vadd(y, k3, h));
        y = vcomb(y, h, [k1, k2, k3, k4], [1 / 6, 1 / 3, 1 / 3, 1 / 6]);
        t = t0 + (i + 1) * h;
        T.push(t);
        Y.push(y);
    }
    return { t: T, y: Y };
}

// Dormand–Prince 5(4) tableau
const DP_C = [0, 1 / 5, 3 / 10, 4 / 5, 8 / 9, 1, 1];
const DP_A = [
    [],
    [1 / 5],
    [3 / 40, 9 / 40],
    [44 / 45, -56 / 15, 32 / 9],
    [19372 / 6561, -25360 / 2187, 64448 / 6561, -212 / 729],
    [9017 / 3168, -355 / 33, 46732 / 5247, 49 / 176, -5103 / 18656],
    [35 / 384, 0, 500 / 1113, 125 / 192, -2187 / 6784, 11 / 84],
];
const DP_E = [71 / 57600, 0, -71 / 16695, 71 / 1920, -17253 / 339200, 22 / 525, -1 / 40];

/**
 * Adaptive Dormand–Prince 5(4) from t0 to t1 (either direction). {rtol = 1e-6, atol = 1e-9, h,
 * hMax, maxSteps = 100000, samples} → {t: [], y: [], steps, rejected, ok}; with `samples` the
 * solution is returned at samples + 1 evenly spaced times (cubic Hermite between steps).
 */
export function numOdeAdaptive(f, t0, y0, t1, opts = {}) {
    needFn(f);
    checkY(y0);
    const rtol = opts.rtol ?? 1e-6, atol = opts.atol ?? 1e-9;
    const maxSteps = opts.maxSteps ?? 100000;
    const dir = t1 >= t0 ? 1 : -1;
    const span = Math.abs(t1 - t0);
    const hMax = opts.hMax ?? span;
    const scalar = typeof y0 === 'number';
    const arr = (v) => (scalar ? [v] : v);
    let t = t0, y = vcopy(y0);
    let k1 = f(t, y);
    let h = opts.h ?? Math.min(hMax, span / 100 || 1e-3);
    const T = [t], Y = [vcopy(y)], DY = [k1];
    let steps = 0, rejected = 0, ok = true;
    while (dir * (t1 - t) > 1e-14 * Math.max(1, Math.abs(t1))) {
        if (steps + rejected >= maxSteps) { ok = false; break; }
        if (h > Math.abs(t1 - t)) h = Math.abs(t1 - t);
        const hs = dir * h;
        const ks = [k1];
        for (let s = 1; s < 7; s++) ks.push(f(t + DP_C[s] * hs, vcomb(y, hs, ks, DP_A[s])));
        const y5 = vcomb(y, hs, ks.slice(0, 6), DP_A[6]);
        const errV = vcomb(scalar ? 0 : y.map(() => 0), hs, ks, DP_E);
        const ya = arr(y), yb = arr(y5), ev = arr(errV);
        let e2 = 0;
        for (let i = 0; i < ya.length; i++) {
            const sc = atol + rtol * Math.max(Math.abs(ya[i]), Math.abs(yb[i]));
            e2 += (ev[i] / sc) ** 2;
        }
        const err = Math.sqrt(e2 / ya.length);
        if (!fin(err)) {
            h /= 4;
            rejected++;
            if (h < 1e-14 * Math.max(1, Math.abs(t))) { ok = false; break; }
            continue;
        }
        if (err <= 1) {
            t = Math.abs(t1 - (t + hs)) < 1e-14 * Math.max(1, Math.abs(t1)) ? t1 : t + hs;
            y = y5;
            k1 = ks[6];
            T.push(t); Y.push(vcopy(y)); DY.push(k1);
            steps++;
        } else rejected++;
        const fac = err === 0 ? 5 : Math.min(5, Math.max(0.2, 0.9 * err ** -0.2));
        h = Math.min(hMax, h * (err <= 1 ? fac : Math.min(1, fac)));
        if (h < 1e-14 * Math.max(1, Math.abs(t))) { ok = false; break; }
    }
    if (!opts.samples) return { t: T, y: Y, steps, rejected, ok };
    const N = Math.max(1, Math.floor(opts.samples));
    const ts = numLinspace(t0, t0 + dir * Math.min(span, Math.abs(t - t0)), N + 1);
    const ys = [];
    let j = 0;
    for (const tt of ts) {
        while (j < T.length - 2 && dir * (T[j + 1] - tt) < 0) j++;
        const ta = T[j], tb = T[Math.min(j + 1, T.length - 1)];
        const hh = tb - ta;
        if (hh === 0) { ys.push(vcopy(Y[j])); continue; }
        const s = (tt - ta) / hh;
        const h00 = 2 * s ** 3 - 3 * s ** 2 + 1, h10 = s ** 3 - 2 * s ** 2 + s, h01 = -2 * s ** 3 + 3 * s ** 2, h11 = s ** 3 - s ** 2;
        const A = arr(Y[j]), B = arr(Y[j + 1] ?? Y[j]), dA = arr(DY[j]), dB = arr(DY[j + 1] ?? DY[j]);
        const v = A.map((_, i) => h00 * A[i] + h10 * hh * dA[i] + h01 * B[i] + h11 * hh * dB[i]);
        ys.push(scalar ? v[0] : v);
    }
    return { t: ts, y: ys, steps, rejected, ok };
}

/** SIR epidemic model on population fractions (S + I + R = 1): state [S, I, R]. */
export function odeSir(beta, gamma) {
    return (t, [S, I]) => [-beta * S * I, beta * S * I - gamma * I, gamma * I];
}
/** Lotka–Volterra predator–prey: x' = αx − βxy, y' = δxy − γy; state [prey, predators]. */
export function odeLotkaVolterra(alpha, beta, delta, gamma) {
    return (t, [x, y]) => [alpha * x - beta * x * y, delta * x * y - gamma * y];
}
/** Pendulum θ'' = −(g/L)·sin θ − c·θ' (c = damping); state [θ, ω]. */
export function odePendulum(g = 9.81, L = 1, damping = 0) {
    return (t, [th, w]) => [w, -(g / L) * Math.sin(th) - damping * w];
}
/** Lorenz system with the classic σ = 10, ρ = 28, β = 8/3 by default; state [x, y, z]. */
export function odeLorenz(sigma = 10, rho = 28, beta = 8 / 3) {
    return (t, [x, y, z]) => [sigma * (y - x), x * (rho - z) - y, x * y - beta * z];
}
