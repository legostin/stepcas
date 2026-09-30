// numeric/calculus — numerical derivatives and integrals (adaptive, with error estimates), Riemann sums.

import { EPS, evalSafe, fail, fin, needFn, needInterval } from './common.js';
import { msg } from '../../i18n/index.js';
/* eslint-disable no-loss-of-precision -- quadrature nodes and weights are quoted to their published precision */

// ---------------------------------------------------------------- calculus

const STENCIL = {
    1: (f, x, h) => (f(x + h) - f(x - h)) / (2 * h),
    2: (f, x, h) => (f(x + h) - 2 * f(x) + f(x - h)) / (h * h),
    3: (f, x, h) => (f(x + 2 * h) - 2 * f(x + h) + 2 * f(x - h) - f(x - 2 * h)) / (2 * h * h * h),
    4: (f, x, h) => (f(x + 2 * h) - 4 * f(x + h) + 6 * f(x) - 4 * f(x - h) + f(x - 2 * h)) / (h * h * h * h),
};

/**
 * Derivative of order 1–4 at x: central differences + Richardson extrapolation (Ridders).
 * {order = 1, h (initial step), info} → number, or {value, error} with info.
 */
export function numDerivative(f, x, opts = {}) {
    needFn(f);
    const order = opts.order ?? 1;
    const D = STENCIL[order];
    if (!D) throw fail(msg('numbers.numeric.calculus.derivative_order_must_be_1_4'), 'range');
    const g = (t) => evalSafe(f, t);
    let h = opts.h ?? 0.1 * Math.max(1, Math.abs(x)) * (order > 2 ? 2 : 1);
    // near the edge of the domain (log at 0.001) shrink the step until the stencil fits
    let first = D(g, x, h);
    for (let k = 0; k < 40 && !fin(first); k++) {
        h /= 8;
        first = D(g, x, h);
    }
    // a fast-changing function (sin(cos(tan x)) near the pole of tan) fools the tableau started
    // from a wide step: its error estimate stays large, so restart from narrower steps and keep the best
    let best = ridders(D, g, x, h, first);
    for (let k = 0; k < 4 && fin(best.error) && best.error > 1e-7 * Math.max(1, Math.abs(best.value)); k++) {
        h /= 8;
        const f0 = D(g, x, h);
        if (!fin(f0)) break;
        const r = ridders(D, g, x, h, f0);
        if (r.error < best.error) best = r;
    }
    const ans = best.value,
        err = best.error;
    return opts.info ? { value: ans, error: err } : ans;
}

function ridders(D, g, x, h, first) {
    const CON = 1.4,
        CON2 = CON * CON,
        NTAB = 12,
        SAFE = 2;
    const a = Array.from({ length: NTAB }, () => new Array(NTAB).fill(0));
    a[0][0] = first;
    let err = Infinity,
        ans = a[0][0];
    for (let i = 1; i < NTAB; i++) {
        h /= CON;
        a[0][i] = D(g, x, h);
        let fac = CON2;
        for (let j = 1; j <= i; j++) {
            a[j][i] = (a[j - 1][i] * fac - a[j - 1][i - 1]) / (fac - 1);
            fac *= CON2;
            const errt = Math.max(Math.abs(a[j][i] - a[j - 1][i]), Math.abs(a[j][i] - a[j - 1][i - 1]));
            if (errt <= err) {
                err = errt;
                ans = a[j][i];
            }
        }
        if (Math.abs(a[i][i] - a[i - 1][i - 1]) >= SAFE * err) break;
    }
    return { value: ans, error: err };
}

// Gauss–Kronrod 7–15 nodes and weights (QUADPACK qk15)
const XGK = [
    0.991455371120812639206854697526329, 0.949107912342758524526189684047851, 0.864864423359769072789712788640926, 0.741531185599394439863864773280788,
    0.586087235467691130294144845693013, 0.405845151377397166906606412076961, 0.207784955007898467600689403773245, 0,
];
const WGK = [
    0.02293532201052922496373200805897, 0.063092092629978553290700663189204, 0.104790010322250183839876322541518, 0.140653259715525918745189590510238,
    0.16900472663926790282658342659855, 0.190350578064785409913256402421014, 0.204432940075298892414161999234649, 0.209482141084727828012999174891714,
];
const WG = [0.129484966168869693270611432679082, 0.27970539148927666790146777142378, 0.381830050505118944950369775488975, 0.417959183673469387755102040816327];

function gk15(f, a, b) {
    const c = 0.5 * (a + b),
        hl = 0.5 * (b - a);
    const fc = f(c);
    let rk = fc * WGK[7],
        rg = fc * WG[3];
    for (let j = 0; j < 7; j++) {
        const dx = hl * XGK[j];
        const s = f(c - dx) + f(c + dx);
        rk += WGK[j] * s;
        if (j % 2 === 1) rg += WG[(j - 1) / 2] * s;
    }
    return { value: rk * hl, error: Math.abs((rk - rg) * hl) };
}

function adaptiveGk(f, a, b, tol, maxIntervals) {
    const first = gk15(f, a, b);
    const parts = [{ a, b, ...first }];
    let total = first.value,
        err = first.error,
        evals = 15;
    while (parts.length < maxIntervals) {
        if (!fin(total)) break;
        if (err <= Math.max(tol, 50 * EPS * Math.abs(total))) break;
        let k = 0;
        for (let i = 1; i < parts.length; i++) if (parts[i].error > parts[k].error) k = i;
        const p = parts[k];
        const m = 0.5 * (p.a + p.b);
        if (m <= p.a || m >= p.b) break;
        const l = gk15(f, p.a, m),
            r = gk15(f, m, p.b);
        evals += 30;
        total += l.value + r.value - p.value;
        err += l.error + r.error - p.error;
        parts.splice(k, 1, { a: p.a, b: m, ...l }, { a: m, b: p.b, ...r });
    }
    // recompute the sums exactly to shed accumulated round-off
    total = parts.reduce((s, p) => s + p.value, 0);
    err = parts.reduce((s, p) => s + p.error, 0);
    return { value: total, error: err, evaluations: evals, intervals: parts.map((p) => [p.a, p.b]) };
}

function tanhSinh(f, a, b, tol) {
    // double-exponential quadrature; nodes approach the ends without touching them
    const hw = 0.5 * (b - a);
    const term = (t) => {
        const u = 0.5 * Math.PI * Math.sinh(t);
        const ch = Math.cosh(u);
        const w = (0.5 * Math.PI * Math.cosh(t)) / (ch * ch);
        const dist = (hw / (Math.exp(2 * Math.abs(u)) + 1)) * 2; // distance from the nearer end
        const x = t >= 0 ? b - dist : a + dist;
        if (dist === 0 || x <= a || x >= b) return 0;
        const y = f(x);
        return fin(y) ? w * y : 0;
    };
    // |t| up to 6.5: there the nodes are ~1e-300 from the ends, enough for x^(−0.9)-type singularities
    const TMAX = 6.5;
    let h = 1,
        sum = term(0),
        evals = 1;
    for (let k = 1; k <= TMAX / h; k++) {
        sum += term(k * h) + term(-k * h);
        evals += 2;
    }
    let prev = sum * h * hw;
    let err = Infinity;
    for (let level = 1; level <= 7; level++) {
        h /= 2;
        for (let k = 1; k * h <= TMAX; k += 2) {
            sum += term(k * h) + term(-k * h);
            evals += 2;
        }
        const cur = sum * h * hw;
        err = Math.abs(cur - prev);
        prev = cur;
        if (level >= 3 && err <= Math.max(tol * 1e-2, 2e-15 * Math.abs(cur))) break;
    }
    return { value: prev, error: err, evaluations: evals };
}

// ∫ₐᵇ f as ∫ g over a finite [lo, hi]: infinite limits by x = a + t/(1 − t), x = b − (1 − t)/t,
// x = t/(1 − t²); toX maps a node t back to x.
function integrand(f, a, b) {
    if (a === -Infinity && b === Infinity) {
        return {
            g: (t) => {
                const d = 1 - t * t;
                return (evalSafe(f, t / d) * (1 + t * t)) / (d * d);
            },
            lo: -1,
            hi: 1,
            map: 'both',
            toX: (t) => t / (1 - t * t),
        };
    }
    if (b === Infinity)
        return {
            g: (t) => {
                const d = 1 - t;
                return evalSafe(f, a + t / d) / (d * d);
            },
            lo: 0,
            hi: 1,
            map: 'upper',
            toX: (t) => a + t / (1 - t),
        };
    if (a === -Infinity) return { g: (t) => evalSafe(f, b - (1 - t) / t) / (t * t), lo: 0, hi: 1, map: 'lower', toX: (t) => b - (1 - t) / t };
    return { g: (x) => evalSafe(f, x), lo: a, hi: b, map: null, toX: (x) => x };
}

/**
 * Definite integral ∫ₐᵇ f. Adaptive Gauss–Kronrod (7–15) with a tanh-sinh fallback for endpoint
 * singularities (1/√x, ln x on [0, 1] …); infinite limits via substitution. {tol = 1e-10,
 * maxIntervals = 2000, info} → number, or {value, error, method, evaluations, intervals} with info.
 * The bare number is never checked for divergence (∫₁^∞ dx/x gives a finite number!): pass
 * {info: true, check: true} or call numIntegrateInfo for {…, ok, divergent, reason}.
 */
export function numIntegrate(f, a, b, opts = {}) {
    needFn(f);
    const tol = opts.tol ?? 1e-10;
    const maxIntervals = opts.maxIntervals ?? 2000;
    if (Number.isNaN(a) || Number.isNaN(b)) throw fail(msg('numbers.numeric.calculus.limits_must_be_numbers'), 'range');
    const pack = (r) => (opts.info ? r : r.value);
    if (a === b)
        return pack({
            value: 0,
            error: 0,
            method: 'trivial',
            evaluations: 0,
            intervals: [],
            ...(opts.check ? { ok: true, divergent: false, reason: null, estimate: 0 } : {}),
        });
    if (a > b) {
        const r = numIntegrate(f, b, a, { ...opts, info: true });
        return pack({ ...r, value: -r.value, ...('estimate' in r ? { estimate: -r.estimate } : {}) });
    }
    const { g, lo, hi, map, toX } = integrand(f, a, b);
    const ok = (r) => fin(r.value) && r.error <= Math.max(tol, 1e-12 * Math.abs(r.value));
    const done = (r) => {
        if (!opts.check) return pack(r);
        const d = withDiagnosis(r, g, lo, hi, map, toX, tol, maxIntervals);
        // an oscillating tail (sin x/x, sin x²) may still converge: sum it lobe by lobe
        if (map && ((d.reason === 'oscillating' && d.at === undefined) || d.reason === 'inaccurate' || (d.reason === 'tail' && Number.isNaN(d.value)))) {
            const L = oscillatingTail(f, a, b, tol);
            if (L)
                return pack({
                    ...d,
                    ...L,
                    estimate: L.value,
                    ok: true,
                    divergent: false,
                    reason: null,
                    msg: undefined,
                    evaluations: d.evaluations + L.evaluations,
                });
        }
        return pack(d);
    };
    if (!map && (!fin(g(lo)) || !fin(g(hi)))) {
        // a singular end: the double-exponential rule is made for exactly this
        const ts = tanhSinh(g, lo, hi, tol);
        if (ok(ts)) return done({ ...ts, method: 'tanh-sinh', intervals: [[lo, hi]] });
    }
    const gk = adaptiveGk(g, lo, hi, tol, maxIntervals);
    let best = { ...gk, method: map ? `gauss-kronrod (${map} infinite)` : 'gauss-kronrod' };
    if (!ok(gk)) {
        const ts = tanhSinh(g, lo, hi, tol);
        if (fin(ts.value) && (!fin(gk.value) || ts.error < gk.error)) {
            best = { ...ts, method: 'tanh-sinh', intervals: [[lo, hi]], evaluations: ts.evaluations + gk.evaluations };
        }
    }
    if (map) best.intervals = null;
    return done(best);
}

// ∫ₐ^∞ of an oscillating f: split at the sign changes, integrate each lobe, and sum the alternating
// series of lobes with repeated averaging (Euler's transform). → {value, error, lobes, evaluations} |
// null when the lobes don't shrink (∫ sin x) or the sum can't be trusted.
function lobeTail(f, A, tol) {
    let evaluations = 0;
    const F = (x) => {
        evaluations++;
        return evalSafe(f, x);
    };
    const zeros = [];
    let h = 0.02 * Math.max(1, Math.abs(A));
    let x = A + h * 1e-3,
        y = F(x);
    for (let k = 0; k < 20 && !(fin(y) && y !== 0); k++) {
        x += h * 0.1;
        y = F(x);
    }
    if (!fin(y)) return null;
    let quiet = 0;
    while (zeros.length < 402 && x < 1e7 && evaluations < 200000) {
        const xn = x + h,
            yn = F(xn);
        if (!fin(yn)) return null;
        if (yn !== 0 && Math.sign(yn) !== Math.sign(y)) {
            let l = x,
                r = xn,
                fl = y;
            for (let k = 0; k < 60 && r - l > 4 * EPS * Math.max(1, Math.abs(l)); k++) {
                const m = 0.5 * (l + r),
                    fm = F(m);
                if (fm === 0) {
                    l = r = m;
                    break;
                }
                if (Math.sign(fm) === Math.sign(fl)) {
                    l = m;
                    fl = fm;
                } else r = m;
            }
            zeros.push(0.5 * (l + r));
            quiet = 0;
            if (zeros.length >= 2) h = Math.min(2, Math.max(1e-7, (zeros[zeros.length - 1] - zeros[zeros.length - 2]) / 10));
        } else if (++quiet > 4000)
            return null; // no longer oscillating
        else if (quiet % 200 === 0) h *= 2;
        x = xn;
        if (yn !== 0) y = yn;
    }
    const n = zeros.length - 1;
    if (n < 40) return null;
    const head = numIntegrate(f, A, zeros[0], { tol, info: true });
    const lobes = [];
    let err = head.error;
    for (let k = 0; k < n; k++) {
        const r = adaptiveGk((t) => evalSafe(f, t), zeros[k], zeros[k + 1], tol * 1e-2, 60);
        evaluations += 15;
        lobes.push(r.value);
        err += r.error;
    }
    // the lobes must alternate and shrink
    let flips = 0;
    for (let k = 1; k < n; k++) if (Math.sign(lobes[k]) !== Math.sign(lobes[k - 1])) flips++;
    if (flips < 0.95 * (n - 1)) return null;
    const q = Math.floor(n / 4);
    const mean = (arr) => arr.reduce((s, v) => s + Math.abs(v), 0) / arr.length;
    if (!(mean(lobes.slice(-q)) < 0.98 * mean(lobes.slice(0, q)))) return null;
    const S = [head.value];
    for (const v of lobes) S.push(S[S.length - 1] + v);
    const euler = (upto, M) => {
        let T = S.slice(upto - M + 1, upto + 1);
        while (T.length > 1) T = T.slice(1).map((v, i) => 0.5 * (T[i] + v));
        return T[0];
    };
    const M = Math.min(60, n);
    const value = euler(n, M);
    const alt = euler(n - 10, M - 10);
    const error = err + Math.abs(value - alt);
    if (!fin(value) || error > 1e-6 * Math.max(1, Math.abs(value))) return null;
    return { value, error, lobes: n, evaluations };
}

function oscillatingTail(f, a, b, tol) {
    const mirror = (x) => evalSafe(f, -x);
    const parts =
        b === Infinity && a === -Infinity
            ? [lobeTail(f, 0, tol), lobeTail(mirror, 0, tol)]
            : b === Infinity
              ? [lobeTail(f, a, tol)]
              : [lobeTail(mirror, -b, tol)];
    if (parts.some((p) => !p)) return null;
    return {
        value: parts.reduce((s, p) => s + p.value, 0),
        error: parts.reduce((s, p) => s + p.error, 0),
        evaluations: parts.reduce((s, p) => s + p.evaluations, 0),
        method: 'lobes + Euler averaging',
        intervals: null,
    };
}

/**
 * ∫ₐᵇ f with a verdict on whether the number can be trusted →
 * {value, error, ok, divergent, reason, msg, at?, estimate, method, evaluations, intervals}.
 * reason (null when ok): 'tail' — an infinite limit and f does not decay fast enough (∫₁^∞ dx/x,
 * ∫₀^∞ sin x dx); 'pole' — f blows up non-integrably at `at` (∫₀² dx/(x² − 1), ∫₀¹ dx/x);
 * 'domain' — f is undefined on part of the interval (√(1 − x) on [0, 2]); 'oscillating' — an
 * oscillating tail that may converge only conditionally (∫₀^∞ sin x/x dx), the number is unreliable;
 * 'inaccurate' — the error estimate is too large; 'nan' — no finite value came out.
 * For divergent integrals value is +Infinity / −Infinity when the sign is clear, else NaN; the raw
 * quadrature number is kept in estimate. An integrable singularity inside the interval (1/√|x − 1|)
 * is split off and integrated from both sides. Same options as numIntegrate.
 */
export function numIntegrateInfo(f, a, b, opts = {}) {
    return numIntegrate(f, a, b, { ...opts, info: true, check: true });
}

// the reasons are messages numbers.numeric.calculus.reason.<key>

// Envelope growth of |g| at point c from one side: |g(c ± δ)| ~ δ^(−p). p ≥ 1 is not integrable
// (for the mapped tail t → 1, p = 2 − q where |f| ~ x^(−q)); osc — g changes sign near c.
function singularity(g, c, dir, W) {
    const env = [];
    let signs = 0,
        last = 0,
        big = false;
    const floor = 1e3 * EPS * Math.max(Math.abs(c), W); // closer than this the position of c is noise
    for (const k of [4, 6, 8, 10, 12]) {
        const d = W * 10 ** -k;
        if (d < floor) break;
        let m = 0,
            seen = false;
        for (let j = 0; j < 16; j++) {
            const y = g(c + dir * d * (1 + j / 15));
            if (Number.isNaN(y)) continue;
            seen = true;
            const ay = Math.abs(y);
            if (ay > m) m = ay;
            const s = Math.sign(y);
            if (s && last && s !== last) signs++;
            if (s) last = s;
        }
        env.push(seen ? m : NaN);
        if (m === Infinity) big = true;
    }
    const osc = signs >= 4;
    if (big) return { p: Infinity, osc, sign: last };
    // growth rate between neighbouring scales (×100 closer); the two closest pairs must agree, so a tall
    // but finite spike (1/(x² + 10⁻¹⁴)) that flattens out at the finest scale is not a pole
    const rates = [];
    for (let k = 1; k < env.length; k++) {
        const a = env[k - 1],
            b = env[k];
        rates.push(a > 0 && b > 0 && fin(a) && fin(b) ? Math.log(b / a) / Math.log(100) : NaN);
    }
    const tailRates = rates.slice(-2).filter((x) => !Number.isNaN(x));
    if (!tailRates.length) return { p: 0, osc: false, sign: last };
    if (!osc) return { p: Math.min(...tailRates), osc, sign: last };
    // an oscillating envelope is sampled, not seen: average the rates over all scales
    const all = rates.filter((x) => !Number.isNaN(x));
    return { p: all.reduce((a, b) => a + b, 0) / all.length, osc, sign: last };
}

// The largest |g| on [l, r] (a pole, or where g is undefined at a single point) by golden sections.
function peakIn(g, l, r) {
    const val = (x) => {
        const y = Math.abs(g(x));
        return Number.isNaN(y) ? Infinity : y;
    };
    const R = (Math.sqrt(5) - 1) / 2;
    let x1 = r - R * (r - l),
        x2 = l + R * (r - l),
        f1 = val(x1),
        f2 = val(x2);
    for (let k = 0; k < 70 && r - l > 4 * EPS * Math.max(1, Math.abs(l), Math.abs(r)); k++) {
        if (f1 >= f2) {
            r = x2;
            x2 = x1;
            f2 = f1;
            x1 = r - R * (r - l);
            f1 = val(x1);
        } else {
            l = x1;
            x1 = x2;
            f1 = f2;
            x2 = l + R * (r - l);
            f2 = val(x2);
        }
    }
    return f1 >= f2 ? x1 : x2;
}

function withDiagnosis(r, g0, lo, hi, map, toX, tol, maxIntervals) {
    const W = hi - lo;
    const out = { ...r, estimate: r.value, ok: true, divergent: false, reason: null };
    let spent = 0;
    const g = (x) => {
        spent++;
        return g0(x);
    };
    const verdict0 = (reason, extra) => {
        Object.assign(out, { ok: false, reason, ...extra });
        out.msg = msg(`numbers.numeric.calculus.reason.${reason}`);
        return out;
    };
    const verdict = (reason, extra = {}) => {
        out.evaluations = (r.evaluations ?? 0) + spent;
        return verdict0(reason, extra);
    };
    // classify a point: 'divergent' | 'oscillating' | 'integrable' | null (smooth)
    const judge = (s) => {
        if (s.osc) return s.p >= 1.9 ? 'divergent' : s.p >= 0.99 ? 'oscillating' : s.p > 0.3 ? 'integrable' : null;
        return s.p >= 0.99 ? 'divergent' : s.p > 0.02 ? 'integrable' : null;
    };
    // 1) a scan for points where g blows up or is undefined
    const N = 1024;
    const xs = new Float64Array(N + 1),
        ys = new Float64Array(N + 1);
    xs[0] = lo;
    xs[N] = hi;
    let nanRun = 0,
        nanMax = 0;
    for (let j = 1; j < N; j++) {
        xs[j] = lo + (W * j) / N;
        ys[j] = g(xs[j]);
        if (Number.isNaN(ys[j])) {
            nanRun++;
            nanMax = Math.max(nanMax, nanRun);
        } else nanRun = 0;
    }
    const cands = [];
    for (let j = 1; j < N; j++) {
        const y = Math.abs(ys[j]);
        if (!fin(ys[j])) {
            if (Number.isNaN(ys[j]) && ((j > 1 && Number.isNaN(ys[j - 1])) || (j < N - 1 && Number.isNaN(ys[j + 1])))) continue;
            cands.push({ j, h: Infinity });
        } else if (
            (j === 1 || y >= Math.abs(ys[j - 1]) || Number.isNaN(ys[j - 1])) &&
            (j === N - 1 || y >= Math.abs(ys[j + 1]) || Number.isNaN(ys[j + 1])) &&
            y > 0
        )
            cands.push({ j, h: y });
    }
    cands.sort((p, q) => q.h - p.h);
    const found = []; // {x (in t), side: 'both' | 'lo' | 'hi', kind, signs, osc}
    // an overflow stretch (e^x near the mapped +∞) that runs into an end belongs to that end
    const infTo = (j, dir) => {
        for (let k = j; k >= 1 && k <= N - 1; k += dir) if (fin(ys[k])) return false;
        return true;
    };
    for (const { j, h } of cands.slice(0, 12)) {
        if (h === Infinity && !Number.isNaN(ys[j]) && (infTo(j, 1) || infTo(j, -1))) continue;
        const c = peakIn(g, xs[j - 1], xs[j + 1]);
        // a peak at an end is the end's business (below)
        if (!(c - lo > W * 1e-9) || !(hi - c > W * 1e-9) || found.some((q) => Math.abs(q.x - c) < W * 1e-9)) continue;
        const L = singularity(g, c, -1, W),
            Rt = singularity(g, c, 1, W);
        const kl = judge(L),
            kr = judge(Rt);
        const kind = kl === 'divergent' || kr === 'divergent' ? 'divergent' : kl === 'oscillating' || kr === 'oscillating' ? 'oscillating' : kl || kr;
        if (kind) found.push({ x: c, side: 'both', kind, signs: [L.sign, Rt.sign], osc: L.osc || Rt.osc });
    }
    // 2) the ends (for a mapped infinite limit the end is the tail)
    for (const [x, dir, side] of [
        [lo, 1, 'lo'],
        [hi, -1, 'hi'],
    ]) {
        const s = singularity(g, x, dir, W);
        const kind = judge(s);
        if (kind) found.push({ x, side, kind, signs: [s.sign], osc: s.osc });
    }
    // where it happens, in x: 0.29999999999999993 → 0.3, −1.3·10⁻¹⁶ → 0
    const atX = (t) => {
        const x = toX(t);
        const scale = map ? Math.max(1, Math.abs(x)) : Math.max(W, Math.abs(x));
        if (Math.abs(x) < 1e-12 * scale) return 0;
        const r = Number(x.toPrecision(12));
        return Math.abs(r - x) <= 4 * EPS * Math.abs(x) ? r : x;
    };
    const isTail = (q) => (q.side === 'hi' && (map === 'upper' || map === 'both')) || (q.side === 'lo' && (map === 'lower' || map === 'both'));
    const div = found.filter((q) => q.kind === 'divergent');
    if (div.length) {
        const signs = div.flatMap((q) => (q.osc ? [0] : q.signs));
        const s = signs.every((v) => v === 1) ? 1 : signs.every((v) => v === -1) ? -1 : 0;
        const tail = div.find(isTail);
        const pole = div.find((q) => !isTail(q));
        out.divergent = true;
        out.value = s ? s * Infinity : NaN;
        return verdict(tail && !pole ? 'tail' : 'pole', pole ? { at: atX(pole.x) } : {});
    }
    if (nanMax >= 3) return verdict('domain');
    const osc = found.find((q) => q.kind === 'oscillating');
    if (osc) return verdict('oscillating', isTail(osc) ? {} : { at: atX(osc.x) });
    // 3) an integrable singularity inside: integrate up to it from both sides
    const inner = found
        .filter((q) => q.side === 'both' && q.kind === 'integrable')
        .map((q) => q.x)
        .sort((p, q) => p - q);
    if (inner.length && !(r.error <= Math.max(tol, 1e-12 * Math.abs(r.value)))) {
        const cuts = [lo, ...inner, hi];
        let v = 0,
            e = 0;
        for (let k = 0; k + 1 < cuts.length; k++) {
            const t = tanhSinh(g, cuts[k], cuts[k + 1], tol);
            const q = adaptiveGk(g, cuts[k], cuts[k + 1], tol, Math.max(50, maxIntervals >> 2));
            const best = fin(t.value) && (!fin(q.value) || t.error < q.error) ? t : q;
            v += best.value;
            e += best.error;
        }
        if (fin(v) && (e < r.error || !fin(r.value)))
            Object.assign(out, {
                value: v,
                estimate: v,
                error: e,
                method: 'split at singular points',
                intervals: map ? null : cuts.slice(1).map((x, k) => [cuts[k], x]),
            });
    }
    out.evaluations = (r.evaluations ?? 0) + spent;
    if (!fin(out.value)) return verdict('nan');
    if (!(out.error <= Math.max(1e3 * tol, 1e-6 * Math.abs(out.value)))) return verdict('inaccurate');
    return out;
}

/**
 * Riemann-type sums with n pieces: method 'left' | 'right' | 'mid' | 'trapezoid' | 'simpson'
 * (Simpson needs even n; an odd n is raised by one). → {value, n, method, pieces: [{x0, x1, h, …}]}
 * where h is the height of the piece's rectangle of equal area (trapezoids add y0, y1; Simpson's
 * parabolic pieces add xm, y0, ym, y1).
 */
export function numRiemann(f, a, b, n, method = 'left') {
    needFn(f);
    needInterval(a, b);
    n = Math.max(1, Math.floor(n));
    if (method === 'simpson' && n % 2) n += 1;
    const dx = (b - a) / n;
    const X = (i) => (i === n ? b : a + i * dx);
    const F = (x) => evalSafe(f, x);
    const pieces = [];
    let value = 0;
    if (method === 'simpson') {
        for (let i = 0; i < n; i += 2) {
            const x0 = X(i),
                xm = X(i + 1),
                x1 = X(i + 2);
            const y0 = F(x0),
                ym = F(xm),
                y1 = F(x1);
            const area = ((x1 - x0) / 6) * (y0 + 4 * ym + y1);
            value += area;
            pieces.push({ x0, x1, h: area / (x1 - x0), xm, y0, ym, y1 });
        }
    } else {
        for (let i = 0; i < n; i++) {
            const x0 = X(i),
                x1 = X(i + 1);
            let piece;
            if (method === 'left') piece = { x0, x1, h: F(x0) };
            else if (method === 'right') piece = { x0, x1, h: F(x1) };
            else if (method === 'mid') piece = { x0, x1, h: F((x0 + x1) / 2) };
            else if (method === 'trapezoid') {
                const y0 = F(x0),
                    y1 = F(x1);
                piece = { x0, x1, h: (y0 + y1) / 2, y0, y1 };
            } else throw fail(msg('numbers.numeric.calculus.unknown_method', { method }), 'range');
            value += piece.h * (x1 - x0);
            pieces.push(piece);
        }
    }
    return { value, n, method, pieces };
}
