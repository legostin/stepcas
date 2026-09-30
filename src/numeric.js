// numeric — floating-point numerical methods for widgets, simulators, plots and checks.
//
// Everything works on doubles. Root finders return {root, iterations, converged, …}; integrals
// and derivatives return a number (pass {info: true} for {value, error, …}). Invalid input throws
// MathError with a bilingual message. See README.md for the full contract.

import { MathError } from './rational.js';

const fail = (ru, en, code = null) => new MathError({ ru, en }, null, null, code);
const EPS = Number.EPSILON;
const fin = Number.isFinite;

function evalSafe(f, x) {
    let y;
    try { y = f(x); } catch { return NaN; }
    return typeof y === 'number' ? y : Number(y);
}
function needFn(f) {
    if (typeof f !== 'function') throw fail('Нужна функция.', 'A function is required.', 'type');
}
function needInterval(a, b) {
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

// ---------------------------------------------------------------- roots

/**
 * Bisection: f(a) and f(b) must have opposite signs. {tol (absolute, 1e-12), maxIter, trace} →
 * {root, iterations, converged, trace?: [{a, b, m, fa, fb, fm}]}.
 */
export function numBisect(f, a, b, opts = {}) {
    needFn(f);
    needInterval(a, b);
    const tol = opts.tol ?? 1e-12;
    const maxIter = opts.maxIter ?? 200;
    const trace = opts.trace ? [] : null;
    if (a > b) [a, b] = [b, a];
    let fa = evalSafe(f, a), fb = evalSafe(f, b);
    const done = (root, iterations, converged) => (trace ? { root, iterations, converged, trace } : { root, iterations, converged });
    if (!fin(fa) || !fin(fb)) throw fail('Функция не определена на конце отрезка.', 'The function is undefined at an end of the interval.', 'domain');
    if (fa === 0) return done(a, 0, true);
    if (fb === 0) return done(b, 0, true);
    if ((fa < 0) === (fb < 0)) {
        throw fail('На концах отрезка у функции один знак — метод половинного деления начать нельзя.',
            'The function has the same sign at both ends, so bisection cannot start.', 'no-sign-change');
    }
    for (let it = 1; it <= maxIter; it++) {
        const m = a + (b - a) / 2;
        const fm = evalSafe(f, m);
        if (trace) trace.push({ a, b, m, fa, fb, fm });
        if (fm === 0) return done(m, it, true);
        if (!fin(fm)) throw fail('Функция не определена внутри отрезка.', 'The function is undefined inside the interval.', 'domain');
        const stuck = m <= a || m >= b;
        if ((fm < 0) === (fa < 0)) { a = m; fa = fm; } else { b = m; fb = fm; }
        if (b - a <= 2 * tol || stuck) return done(a + (b - a) / 2, it, true);
    }
    return done(a + (b - a) / 2, maxIter, false);
}

/** Brent's method (bisection + secant + inverse quadratic interpolation) → {root, iterations, converged}. */
export function numBrent(f, a, b, opts = {}) {
    needFn(f);
    needInterval(a, b);
    const tol = opts.tol ?? 1e-15;
    const maxIter = opts.maxIter ?? 200;
    let fa = evalSafe(f, a), fb = evalSafe(f, b);
    if (!fin(fa) || !fin(fb)) throw fail('Функция не определена на конце отрезка.', 'The function is undefined at an end of the interval.', 'domain');
    if (fa === 0) return { root: a, iterations: 0, converged: true };
    if (fb === 0) return { root: b, iterations: 0, converged: true };
    if ((fa < 0) === (fb < 0)) {
        throw fail('На концах отрезка у функции один знак — корень не выделен.', 'The function has the same sign at both ends, so no root is bracketed.', 'no-sign-change');
    }
    let c = b, fc = fb, d = 0, e = 0;
    for (let it = 1; it <= maxIter; it++) {
        if ((fb > 0 && fc > 0) || (fb < 0 && fc < 0)) { c = a; fc = fa; d = b - a; e = d; }
        if (Math.abs(fc) < Math.abs(fb)) { a = b; b = c; c = a; fa = fb; fb = fc; fc = fa; }
        const tol1 = 2 * EPS * Math.abs(b) + 0.5 * tol;
        const xm = 0.5 * (c - b);
        if (Math.abs(xm) <= tol1 || fb === 0) return { root: b, iterations: it, converged: true };
        if (Math.abs(e) >= tol1 && Math.abs(fa) > Math.abs(fb)) {
            const s = fb / fa;
            let p, q;
            if (a === c) { p = 2 * xm * s; q = 1 - s; }
            else {
                const qq = fa / fc, r = fb / fc;
                p = s * (2 * xm * qq * (qq - r) - (b - a) * (r - 1));
                q = (qq - 1) * (r - 1) * (s - 1);
            }
            if (p > 0) q = -q;
            p = Math.abs(p);
            if (2 * p < Math.min(3 * xm * q - Math.abs(tol1 * q), Math.abs(e * q))) { e = d; d = p / q; }
            else { d = xm; e = d; }
        } else { d = xm; e = d; }
        a = b; fa = fb;
        b += Math.abs(d) > tol1 ? d : xm > 0 ? tol1 : -tol1;
        fb = evalSafe(f, b);
        if (!fin(fb)) throw fail('Функция не определена внутри отрезка.', 'The function is undefined inside the interval.', 'domain');
    }
    return { root: b, iterations: maxIter, converged: false };
}

/**
 * Newton's method. df may be null (a numerical derivative is used). {tol, maxIter, trace} →
 * {root, iterations, converged, reason?, trace?: [{x, fx, dfx, next}]}.
 */
export function numNewton(f, df, x0, opts = {}) {
    needFn(f);
    const tol = opts.tol ?? 1e-12;
    const maxIter = opts.maxIter ?? 50;
    const d = df ?? ((x) => numDerivative(f, x));
    const trace = opts.trace ? [] : null;
    const out = (root, iterations, converged, reason) => {
        const r = { root, iterations, converged };
        if (reason) r.reason = reason;
        if (trace) r.trace = trace;
        return r;
    };
    let x = x0;
    for (let it = 1; it <= maxIter; it++) {
        const fx = evalSafe(f, x);
        if (!fin(fx)) return out(x, it - 1, false, 'domain');
        if (fx === 0) return out(x, it - 1, true);
        const dfx = evalSafe(d, x);
        if (!fin(dfx)) return out(x, it - 1, false, 'domain');
        if (dfx === 0) return out(x, it - 1, false, 'flat');
        const next = x - fx / dfx;
        if (trace) trace.push({ x, fx, dfx, next });
        if (!fin(next)) return out(x, it, false, 'diverged');
        if (Math.abs(next - x) <= tol * Math.max(1, Math.abs(next))) return out(next, it, true);
        x = next;
    }
    return out(x, maxIter, false, 'max-iter');
}

function parityFix(m, raw, odd) {
    if ((m % 2 === 1) === odd) return m;
    const lo = m - 1, hi = m + 1;
    const cand = odd ? [lo, hi].filter((v) => v >= 1) : [lo, hi].filter((v) => v >= 2);
    return cand.sort((u, v) => Math.abs(u - raw) - Math.abs(v - raw))[0];
}
function estimateMultiplicity(f, r, h, odd) {
    const est = [];
    for (const s of [1, -1]) {
        const f1 = Math.abs(evalSafe(f, r + s * h)), f2 = Math.abs(evalSafe(f, r + 2 * s * h));
        if (f1 > 0 && f2 > 0 && fin(f1) && fin(f2)) est.push(Math.log2(f2 / f1));
    }
    const raw = est.length ? est.reduce((a, b) => a + b, 0) / est.length : 1;
    const m = Math.min(12, Math.max(1, Math.round(raw)));
    return parityFix(m, raw, odd);
}

/**
 * All roots of f in [a, b]: sign changes (refined by Brent; poles rejected) and near-zero local
 * minima of |f| (touching roots). → [{x, kind: 'cross'|'touch', multiplicity}] ascending;
 * `multiplicity` is an estimate (odd for crossings, even for touching roots). Where f is exactly 0
 * on a stretch of samples the entry is {x, kind: 'interval', from, to}.
 */
export function numFindRoots(f, a, b, opts = {}) {
    needFn(f);
    needInterval(a, b);
    if (a > b) [a, b] = [b, a];
    const n = Math.max(10, Math.floor(opts.samples ?? 1000));
    const xs = numLinspace(a, b, n + 1);
    const ys = xs.map((x) => evalSafe(f, x));
    const h = (b - a) / n;
    const found = [];
    const add = (x, kind) => found.push({ x, kind });
    const intervals = [];
    for (let i = 0; i <= n; i++) {
        if (ys[i] !== 0) continue;
        let j = i;
        while (j < n && ys[j + 1] === 0) j++;
        if (j - i >= 2) intervals.push({ x: xs[i], kind: 'interval', from: xs[i], to: xs[j] });
        else for (let k = i; k <= j; k++) add(xs[k], 'exact');
        i = j;
    }
    for (let i = 0; i < n; i++) {
        const y0 = ys[i], y1 = ys[i + 1];
        if (!fin(y0) || !fin(y1) || y0 === 0 || y1 === 0 || (y0 < 0) === (y1 < 0)) continue;
        const r = numBrent(f, xs[i], xs[i + 1]).root;
        const fr = Math.abs(evalSafe(f, r));
        if (fr <= 1e-6 * Math.max(Math.abs(y0), Math.abs(y1))) add(r, 'cross');
    }
    for (let i = 1; i < n; i++) {
        const y0 = ys[i - 1], y1 = ys[i], y2 = ys[i + 1];
        if (!fin(y0) || !fin(y1) || !fin(y2) || y0 === 0 || y1 === 0 || y2 === 0) continue;
        if ((y0 < 0) !== (y1 < 0) || (y1 < 0) !== (y2 < 0)) continue;
        if (!(Math.abs(y1) <= Math.abs(y0) && Math.abs(y1) <= Math.abs(y2))) continue;
        const g = (x) => Math.abs(evalSafe(f, x));
        let x = numGoldenMin(g, xs[i - 1], xs[i + 1], { tol: 1e-12 }).x;
        // polish on f' when it changes sign in the bracket
        const d = (t) => numDerivative(f, t, { h: h / 4 });
        const d0 = d(xs[i - 1]), d2 = d(xs[i + 1]);
        if (fin(d0) && fin(d2) && (d0 < 0) !== (d2 < 0)) {
            try {
                const xr = numBrent(d, xs[i - 1], xs[i + 1], { tol: 1e-14 }).root;
                if (g(xr) <= g(x)) x = xr;
            } catch { /* keep the golden-section point */ }
        }
        if (g(x) <= 1e-9 * Math.max(Math.abs(y0), Math.abs(y2))) add(x, 'touch');
    }
    found.sort((u, v) => u.x - v.x);
    const merged = [];
    const gap = Math.max(1e-9 * (b - a), 1e-12);
    for (const r of found) {
        const last = merged[merged.length - 1];
        if (last && Math.abs(r.x - last.x) <= Math.max(gap, h * 1e-3)) {
            if (r.kind === 'exact') last.x = r.x;
            if (last.kind !== 'exact' && r.kind === 'touch') last.kind = 'touch';
            continue;
        }
        merged.push({ ...r });
    }
    const hm = Math.max(h * 0.05, 1e-6 * Math.max(1, Math.abs(a), Math.abs(b)));
    const inside = (x) => intervals.some((iv) => x >= iv.from - h && x <= iv.to + h);
    const points = merged.filter((r) => !inside(r.x)).map((r) => {
        let kind = r.kind;
        if (kind === 'exact') {
            const l = evalSafe(f, r.x - hm), rr = evalSafe(f, r.x + hm);
            kind = fin(l) && fin(rr) && (l < 0) === (rr < 0) && l !== 0 ? 'touch' : 'cross';
        }
        return { x: r.x, kind, multiplicity: estimateMultiplicity(f, r.x, hm, kind === 'cross') };
    });
    return [...points, ...intervals].sort((u, v) => u.x - v.x);
}

// ---------------------------------------------------------------- optimisation

/** Golden-section search for a minimum of a unimodal f on [a, b] → {x, fx, iterations, trace?}. */
export function numGoldenMin(f, a, b, opts = {}) {
    needFn(f);
    needInterval(a, b);
    if (a > b) [a, b] = [b, a];
    const tol = opts.tol ?? 1e-10;
    const maxIter = opts.maxIter ?? 300;
    const trace = opts.trace ? [] : null;
    const F = (x) => { const y = evalSafe(f, x); return Number.isNaN(y) ? Infinity : y; };
    const g = (Math.sqrt(5) - 1) / 2;
    let x1 = b - g * (b - a), x2 = a + g * (b - a);
    let f1 = F(x1), f2 = F(x2);
    let it = 0;
    while (it < maxIter && b - a > tol * Math.max(1, Math.abs(a) + Math.abs(b))) {
        it++;
        if (trace) trace.push({ a, b, x1, x2, f1, f2 });
        if (f1 <= f2) { b = x2; x2 = x1; f2 = f1; x1 = b - g * (b - a); f1 = F(x1); }
        else { a = x1; x1 = x2; f1 = f2; x2 = a + g * (b - a); f2 = F(x2); }
    }
    const x = f1 <= f2 ? x1 : x2;
    const res = { x, fx: Math.min(f1, f2), iterations: it };
    if (trace) res.trace = trace;
    return res;
}

/** Local extrema of f inside (a, b) → [{x, y, kind: 'min'|'max'}] ascending by x. */
export function numExtrema(f, a, b, opts = {}) {
    needFn(f);
    needInterval(a, b);
    if (a > b) [a, b] = [b, a];
    const n = Math.max(10, Math.floor(opts.samples ?? 400));
    const xs = numLinspace(a, b, n + 1);
    const ys = xs.map((x) => evalSafe(f, x));
    const out = [];
    for (let i = 1; i < n; i++) {
        const y0 = ys[i - 1], y1 = ys[i], y2 = ys[i + 1];
        if (!fin(y0) || !fin(y1) || !fin(y2)) continue;
        let kind = null;
        if (y1 > y0 && y1 >= y2) kind = 'max';
        else if (y1 < y0 && y1 <= y2) kind = 'min';
        if (!kind) continue;
        const s = kind === 'max' ? -1 : 1;
        const r = numGoldenMin((x) => s * evalSafe(f, x), xs[i - 1], xs[i + 1], { tol: 1e-12 });
        const last = out[out.length - 1];
        if (last && last.kind === kind && Math.abs(last.x - r.x) < (b - a) / n) continue;
        out.push({ x: r.x, y: evalSafe(f, r.x), kind });
    }
    return out;
}

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
    if (!D) throw fail('Порядок производной — от 1 до 4.', 'The derivative order must be 1–4.', 'range');
    const g = (t) => evalSafe(f, t);
    let h = opts.h ?? 0.1 * Math.max(1, Math.abs(x)) * (order > 2 ? 2 : 1);
    // near the edge of the domain (log at 0.001) shrink the step until the stencil fits
    let first = D(g, x, h);
    for (let k = 0; k < 40 && !fin(first); k++) { h /= 8; first = D(g, x, h); }
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
    const ans = best.value, err = best.error;
    return opts.info ? { value: ans, error: err } : ans;
}

function ridders(D, g, x, h, first) {
    const CON = 1.4, CON2 = CON * CON, NTAB = 12, SAFE = 2;
    const a = Array.from({ length: NTAB }, () => new Array(NTAB).fill(0));
    a[0][0] = first;
    let err = Infinity, ans = a[0][0];
    for (let i = 1; i < NTAB; i++) {
        h /= CON;
        a[0][i] = D(g, x, h);
        let fac = CON2;
        for (let j = 1; j <= i; j++) {
            a[j][i] = (a[j - 1][i] * fac - a[j - 1][i - 1]) / (fac - 1);
            fac *= CON2;
            const errt = Math.max(Math.abs(a[j][i] - a[j - 1][i]), Math.abs(a[j][i] - a[j - 1][i - 1]));
            if (errt <= err) { err = errt; ans = a[j][i]; }
        }
        if (Math.abs(a[i][i] - a[i - 1][i - 1]) >= SAFE * err) break;
    }
    return { value: ans, error: err };
}

// Gauss–Kronrod 7–15 nodes and weights (QUADPACK qk15)
const XGK = [0.991455371120812639206854697526329, 0.949107912342758524526189684047851, 0.864864423359769072789712788640926,
    0.741531185599394439863864773280788, 0.586087235467691130294144845693013, 0.405845151377397166906606412076961,
    0.207784955007898467600689403773245, 0];
const WGK = [0.022935322010529224963732008058970, 0.063092092629978553290700663189204, 0.104790010322250183839876322541518,
    0.140653259715525918745189590510238, 0.169004726639267902826583426598550, 0.190350578064785409913256402421014,
    0.204432940075298892414161999234649, 0.209482141084727828012999174891714];
const WG = [0.129484966168869693270611432679082, 0.279705391489276667901467771423780, 0.381830050505118944950369775488975,
    0.417959183673469387755102040816327];

function gk15(f, a, b) {
    const c = 0.5 * (a + b), hl = 0.5 * (b - a);
    const fc = f(c);
    let rk = fc * WGK[7], rg = fc * WG[3];
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
    let total = first.value, err = first.error, evals = 15;
    while (parts.length < maxIntervals) {
        if (!fin(total)) break;
        if (err <= Math.max(tol, 50 * EPS * Math.abs(total))) break;
        let k = 0;
        for (let i = 1; i < parts.length; i++) if (parts[i].error > parts[k].error) k = i;
        const p = parts[k];
        const m = 0.5 * (p.a + p.b);
        if (m <= p.a || m >= p.b) break;
        const l = gk15(f, p.a, m), r = gk15(f, m, p.b);
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
    const c = 0.5 * (a + b), hw = 0.5 * (b - a);
    const term = (t) => {
        const u = 0.5 * Math.PI * Math.sinh(t);
        const ch = Math.cosh(u);
        const w = (0.5 * Math.PI * Math.cosh(t)) / (ch * ch);
        const dist = hw / (Math.exp(2 * Math.abs(u)) + 1) * 2; // distance from the nearer end
        const x = t >= 0 ? b - dist : a + dist;
        if (dist === 0 || x <= a || x >= b) return 0;
        const y = f(x);
        return fin(y) ? w * y : 0;
    };
    // |t| up to 6.5: there the nodes are ~1e-300 from the ends, enough for x^(−0.9)-type singularities
    const TMAX = 6.5;
    let h = 1, sum = term(0), evals = 1;
    for (let k = 1; k <= TMAX / h; k++) { sum += term(k * h) + term(-k * h); evals += 2; }
    let prev = sum * h * hw;
    let err = Infinity;
    for (let level = 1; level <= 7; level++) {
        h /= 2;
        for (let k = 1; k * h <= TMAX; k += 2) { sum += term(k * h) + term(-k * h); evals += 2; }
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
        return { g: (t) => { const d = 1 - t * t; return evalSafe(f, t / d) * (1 + t * t) / (d * d); }, lo: -1, hi: 1, map: 'both', toX: (t) => t / (1 - t * t) };
    }
    if (b === Infinity) return { g: (t) => { const d = 1 - t; return evalSafe(f, a + t / d) / (d * d); }, lo: 0, hi: 1, map: 'upper', toX: (t) => a + t / (1 - t) };
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
    if (Number.isNaN(a) || Number.isNaN(b)) throw fail('Пределы интегрирования — числа.', 'The limits must be numbers.', 'range');
    const pack = (r) => (opts.info ? r : r.value);
    if (a === b) return pack({ value: 0, error: 0, method: 'trivial', evaluations: 0, intervals: [], ...(opts.check ? { ok: true, divergent: false, reason: null, estimate: 0 } : {}) });
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
            if (L) return pack({ ...d, ...L, estimate: L.value, ok: true, divergent: false, reason: null, msg: undefined, evaluations: d.evaluations + L.evaluations });
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
    const F = (x) => { evaluations++; return evalSafe(f, x); };
    const zeros = [];
    let h = 0.02 * Math.max(1, Math.abs(A));
    let x = A + h * 1e-3, y = F(x);
    for (let k = 0; k < 20 && !(fin(y) && y !== 0); k++) { x += h * 0.1; y = F(x); }
    if (!fin(y)) return null;
    let quiet = 0;
    while (zeros.length < 402 && x < 1e7 && evaluations < 200000) {
        const xn = x + h, yn = F(xn);
        if (!fin(yn)) return null;
        if (yn !== 0 && Math.sign(yn) !== Math.sign(y)) {
            let l = x, r = xn, fl = y;
            for (let k = 0; k < 60 && r - l > 4 * EPS * Math.max(1, Math.abs(l)); k++) {
                const m = 0.5 * (l + r), fm = F(m);
                if (fm === 0) { l = r = m; break; }
                if (Math.sign(fm) === Math.sign(fl)) { l = m; fl = fm; } else r = m;
            }
            zeros.push(0.5 * (l + r));
            quiet = 0;
            if (zeros.length >= 2) h = Math.min(2, Math.max(1e-7, (zeros[zeros.length - 1] - zeros[zeros.length - 2]) / 10));
        } else if (++quiet > 4000) return null; // no longer oscillating
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
    const parts = b === Infinity && a === -Infinity ? [lobeTail(f, 0, tol), lobeTail(mirror, 0, tol)]
        : b === Infinity ? [lobeTail(f, a, tol)] : [lobeTail(mirror, -b, tol)];
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

const REASONS = {
    tail: ['Интеграл расходится: на бесконечности функция убывает недостаточно быстро.', 'The integral diverges: the function does not decay fast enough at infinity.'],
    pole: ['Интеграл расходится: функция неограниченно растёт вблизи точки, и площадь там бесконечна.', 'The integral diverges: the function blows up near a point and the area there is infinite.'],
    domain: ['Функция не определена на части отрезка.', 'The function is undefined on part of the interval.'],
    oscillating: ['Функция колеблется, не затухая достаточно быстро: численное значение ненадёжно.', 'The function oscillates without decaying fast enough: the numeric value is unreliable.'],
    inaccurate: ['Точность вычисления недостаточна: значение приблизительное.', 'The computation is not accurate enough: the value is only rough.'],
    nan: ['Не удалось получить конечное значение.', 'No finite value could be obtained.'],
};

// Envelope growth of |g| at point c from one side: |g(c ± δ)| ~ δ^(−p). p ≥ 1 is not integrable
// (for the mapped tail t → 1, p = 2 − q where |f| ~ x^(−q)); osc — g changes sign near c.
function singularity(g, c, dir, W) {
    const env = [];
    let signs = 0, last = 0, big = false;
    const floor = 1e3 * EPS * Math.max(Math.abs(c), W); // closer than this the position of c is noise
    for (const k of [4, 6, 8, 10, 12]) {
        const d = W * 10 ** -k;
        if (d < floor) break;
        let m = 0, seen = false;
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
        const a = env[k - 1], b = env[k];
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
    const val = (x) => { const y = Math.abs(g(x)); return Number.isNaN(y) ? Infinity : y; };
    const R = (Math.sqrt(5) - 1) / 2;
    let x1 = r - R * (r - l), x2 = l + R * (r - l), f1 = val(x1), f2 = val(x2);
    for (let k = 0; k < 70 && r - l > 4 * EPS * Math.max(1, Math.abs(l), Math.abs(r)); k++) {
        if (f1 >= f2) { r = x2; x2 = x1; f2 = f1; x1 = r - R * (r - l); f1 = val(x1); } else { l = x1; x1 = x2; f1 = f2; x2 = l + R * (r - l); f2 = val(x2); }
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
        out.msg = { ru: REASONS[reason][0], en: REASONS[reason][1] };
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
    const xs = new Float64Array(N + 1), ys = new Float64Array(N + 1);
    xs[0] = lo;
    xs[N] = hi;
    let nanRun = 0, nanMax = 0;
    for (let j = 1; j < N; j++) {
        xs[j] = lo + (W * j) / N;
        ys[j] = g(xs[j]);
        if (Number.isNaN(ys[j])) { nanRun++; nanMax = Math.max(nanMax, nanRun); } else nanRun = 0;
    }
    const cands = [];
    for (let j = 1; j < N; j++) {
        const y = Math.abs(ys[j]);
        if (!fin(ys[j])) {
            if (Number.isNaN(ys[j]) && ((j > 1 && Number.isNaN(ys[j - 1])) || (j < N - 1 && Number.isNaN(ys[j + 1])))) continue;
            cands.push({ j, h: Infinity });
        } else if ((j === 1 || y >= Math.abs(ys[j - 1]) || Number.isNaN(ys[j - 1])) && (j === N - 1 || y >= Math.abs(ys[j + 1]) || Number.isNaN(ys[j + 1])) && y > 0) cands.push({ j, h: y });
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
        const L = singularity(g, c, -1, W), Rt = singularity(g, c, 1, W);
        const kl = judge(L), kr = judge(Rt);
        const kind = kl === 'divergent' || kr === 'divergent' ? 'divergent' : kl === 'oscillating' || kr === 'oscillating' ? 'oscillating' : kl || kr;
        if (kind) found.push({ x: c, side: 'both', kind, signs: [L.sign, Rt.sign], osc: L.osc || Rt.osc });
    }
    // 2) the ends (for a mapped infinite limit the end is the tail)
    for (const [x, dir, side] of [[lo, 1, 'lo'], [hi, -1, 'hi']]) {
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
    const inner = found.filter((q) => q.side === 'both' && q.kind === 'integrable').map((q) => q.x).sort((p, q) => p - q);
    if (inner.length && !(r.error <= Math.max(tol, 1e-12 * Math.abs(r.value)))) {
        const cuts = [lo, ...inner, hi];
        let v = 0, e = 0;
        for (let k = 0; k + 1 < cuts.length; k++) {
            const t = tanhSinh(g, cuts[k], cuts[k + 1], tol);
            const q = adaptiveGk(g, cuts[k], cuts[k + 1], tol, Math.max(50, maxIntervals >> 2));
            const best = fin(t.value) && (!fin(q.value) || t.error < q.error) ? t : q;
            v += best.value;
            e += best.error;
        }
        if (fin(v) && (e < r.error || !fin(r.value))) Object.assign(out, { value: v, estimate: v, error: e, method: 'split at singular points', intervals: map ? null : cuts.slice(1).map((x, k) => [cuts[k], x]) });
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
            const x0 = X(i), xm = X(i + 1), x1 = X(i + 2);
            const y0 = F(x0), ym = F(xm), y1 = F(x1);
            const area = ((x1 - x0) / 6) * (y0 + 4 * ym + y1);
            value += area;
            pieces.push({ x0, x1, h: area / (x1 - x0), xm, y0, ym, y1 });
        }
    } else {
        for (let i = 0; i < n; i++) {
            const x0 = X(i), x1 = X(i + 1);
            let piece;
            if (method === 'left') piece = { x0, x1, h: F(x0) };
            else if (method === 'right') piece = { x0, x1, h: F(x1) };
            else if (method === 'mid') piece = { x0, x1, h: F((x0 + x1) / 2) };
            else if (method === 'trapezoid') { const y0 = F(x0), y1 = F(x1); piece = { x0, x1, h: (y0 + y1) / 2, y0, y1 }; }
            else throw fail(`Неизвестный метод «${method}».`, `Unknown method "${method}".`, 'range');
            value += piece.h * (x1 - x0);
            pieces.push(piece);
        }
    }
    return { value, n, method, pieces };
}

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

// ---------------------------------------------------------------- plot sampling

/**
 * Sample y = f(x) on [x0, x1] for drawing → array of polylines [[x, y], …]. Starts from n + 1
 * evenly spaced points, refines where the curve bends or changes fast (up to maxDepth halvings),
 * and splits the polyline at jumps, poles and gaps in the domain (NaN / ±∞ / exceptions).
 * {n = 400, yRange: [lo, hi] (view; points far outside are clamped), maxDepth = 8, tol = 1e-3}.
 */
export function sampleFunction(f, x0, x1, opts = {}) {
    needFn(f);
    needInterval(x0, x1);
    const n = Math.max(2, Math.floor(opts.n ?? 400));
    const maxDepth = opts.maxDepth ?? 8;
    const maxPoints = opts.maxPoints ?? 20000;
    const ev = (x) => { const y = evalSafe(f, x); return fin(y) ? y : NaN; };
    const xs = numLinspace(x0, x1, n + 1);
    const ys = xs.map(ev);
    let lo, hi;
    if (opts.yRange) [lo, hi] = opts.yRange;
    else {
        const v = ys.filter(fin).sort((p, q) => p - q);
        if (v.length) {
            lo = v[Math.floor(0.02 * (v.length - 1))];
            hi = v[Math.ceil(0.98 * (v.length - 1))];
        } else { lo = -1; hi = 1; }
    }
    const H = hi - lo > 0 ? hi - lo : Math.max(1, Math.abs(hi));
    const tolY = H * (opts.tol ?? 1e-3);
    const jumpY = H * 0.02;
    const clamp = opts.yRange ? (y) => Math.min(hi + 2 * H, Math.max(lo - 2 * H, y)) : (y) => y;
    const segs = [];
    let cur = [];
    let count = 0;
    const push = (x, y) => { cur.push([x, clamp(y)]); count++; };
    const brk = () => { if (cur.length >= 2) segs.push(cur); cur = []; };
    const isJump = (xa, ya, xb, yb) => {
        for (let k = 0; k < 60; k++) {
            const xm = (xa + xb) / 2;
            if (xm <= xa || xm >= xb) break;
            const ym = ev(xm);
            if (!fin(ym)) return true;
            if (Math.abs(ym - ya) >= Math.abs(yb - ym)) { xb = xm; yb = ym; } else { xa = xm; ya = ym; }
        }
        return Math.abs(yb - ya) > 0.5 * jumpY;
    };
    const edge = (xa, ya, xb, yb) => {
        // one end finite, the other not: walk to the edge of the domain
        const leftFinite = fin(ya);
        const pts = [];
        for (let k = 0; k < maxDepth + 40; k++) {
            const xm = (xa + xb) / 2;
            if (xm <= xa || xm >= xb) break;
            const ym = ev(xm);
            if (fin(ym) === leftFinite) {
                if (leftFinite) pts.push([xm, ym]);
                xa = xm; ya = ym;
            } else {
                if (!leftFinite) pts.push([xm, ym]);
                xb = xm; yb = ym;
            }
        }
        if (leftFinite) {
            for (const [x, y] of pts) push(x, y);
            brk();
        } else {
            brk();
            pts.sort((p, q) => p[0] - q[0]);
            for (const [x, y] of pts) push(x, y);
        }
    };
    const interval = (xa, ya, xb, yb, depth) => {
        const fa = fin(ya), fb = fin(yb);
        if (!fa && !fb) {
            if (depth < maxDepth) {
                const xm = (xa + xb) / 2, ym = ev(xm);
                if (fin(ym)) { interval(xa, ya, xm, ym, depth + 1); interval(xm, ym, xb, yb, depth + 1); }
            }
            return;
        }
        if (fa !== fb) {
            edge(xa, ya, xb, yb);
            if (fb) push(xb, yb);
            return;
        }
        const xm = (xa + xb) / 2, ym = ev(xm);
        if (!fin(ym)) {
            if (depth < maxDepth + 8) { interval(xa, ya, xm, ym, depth + 1); interval(xm, ym, xb, yb, depth + 1); }
            else { brk(); push(xb, yb); }
            return;
        }
        if (opts.yRange && ((ya > hi && ym > hi && yb > hi) || (ya < lo && ym < lo && yb < lo))) { push(xb, yb); return; }
        let smooth = Math.abs(ym - (ya + yb) / 2) <= tolY;
        if (smooth && Math.abs(yb - ya) > jumpY) {
            const q1 = ev(xa + (xb - xa) / 4), q3 = ev(xa + 3 * (xb - xa) / 4);
            smooth = fin(q1) && fin(q3) && Math.abs(q1 - (3 * ya + yb) / 4) <= tolY && Math.abs(q3 - (ya + 3 * yb) / 4) <= tolY;
        }
        if (smooth || count > maxPoints) { push(xb, yb); return; }
        if (depth < maxDepth) {
            interval(xa, ya, xm, ym, depth + 1);
            interval(xm, ym, xb, yb, depth + 1);
            return;
        }
        if (Math.abs(yb - ya) > jumpY && isJump(xa, ya, xb, yb)) {
            // which side is the jump on? keep the midpoint with the side it belongs to
            if (Math.abs(ym - ya) <= Math.abs(yb - ym)) { push(xm, ym); brk(); push(xb, yb); }
            else { brk(); push(xm, ym); push(xb, yb); }
            return;
        }
        push(xm, ym);
        push(xb, yb);
    };
    if (fin(ys[0])) push(xs[0], ys[0]);
    for (let i = 0; i < n; i++) interval(xs[i], ys[i], xs[i + 1], ys[i + 1], 0);
    brk();
    return segs;
}

// ---------------------------------------------------------------- signals

/** Direct DFT (O(N²), exact length): X_k = Σ x_j·e^(∓2πijk/N). {inverse} divides by N. → {re, im}. */
export function numDft(re, im = null, opts = {}) {
    const N = re.length;
    const R = new Float64Array(N), I = new Float64Array(N);
    const cs = new Float64Array(N), sn = new Float64Array(N);
    for (let k = 0; k < N; k++) { cs[k] = Math.cos((2 * Math.PI * k) / N); sn[k] = Math.sin((2 * Math.PI * k) / N); }
    const sign = opts.inverse ? 1 : -1;
    for (let k = 0; k < N; k++) {
        let sr = 0, si = 0;
        for (let j = 0; j < N; j++) {
            const idx = (k * j) % N;
            const c = cs[idx], s = sign * sn[idx];
            const xr = re[j], xi = im ? im[j] : 0;
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
    const R = new Float64Array(n), I = new Float64Array(n);
    R.set(re);
    if (im) I.set(im);
    for (let i = 1, j = 0; i < n; i++) {
        let bit = n >> 1;
        for (; j & bit; bit >>= 1) j ^= bit;
        j ^= bit;
        if (i < j) {
            let t = R[i]; R[i] = R[j]; R[j] = t;
            t = I[i]; I[i] = I[j]; I[j] = t;
        }
    }
    const sign = opts.inverse ? 1 : -1;
    for (let len = 2; len <= n; len <<= 1) {
        const half = len >> 1;
        const wr = new Float64Array(half), wi = new Float64Array(half);
        for (let k = 0; k < half; k++) { wr[k] = Math.cos((2 * Math.PI * k) / len); wi[k] = sign * Math.sin((2 * Math.PI * k) / len); }
        for (let i = 0; i < n; i += len) {
            for (let k = 0; k < half; k++) {
                const a = i + k, b = a + half;
                const tr = R[b] * wr[k] - I[b] * wi[k];
                const ti = R[b] * wi[k] + I[b] * wr[k];
                R[b] = R[a] - tr; I[b] = I[a] - ti;
                R[a] += tr; I[a] += ti;
            }
        }
    }
    if (opts.inverse) for (let i = 0; i < n; i++) { R[i] /= n; I[i] /= n; }
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
    const a = new Array(N + 1).fill(0), b = new Array(N + 1).fill(0);
    for (let j = 0; j < M; j++) {
        const x = from + ((j + 0.5) * T) / M;
        const y = evalSafe(f, x);
        if (!fin(y)) continue;
        for (let k = 0; k <= N; k++) {
            a[k] += y * Math.cos(k * w * x);
            if (k) b[k] += y * Math.sin(k * w * x);
        }
    }
    for (let k = 0; k <= N; k++) { a[k] *= 2 / M; b[k] *= 2 / M; }
    return { a, b, period: T, mean: a[0] / 2 };
}

/** Value of the Fourier partial sum with the coefficients of numFourierCoefficients (first n harmonics). */
export function numFourierEval(coefs, x, n = coefs.a.length - 1) {
    const w = (2 * Math.PI) / coefs.period;
    let s = coefs.a[0] / 2;
    for (let k = 1; k <= Math.min(n, coefs.a.length - 1); k++) s += coefs.a[k] * Math.cos(k * w * x) + coefs.b[k] * Math.sin(k * w * x);
    return s;
}

// ---------------------------------------------------------------- statistics

function nums(xs, min = 1) {
    if (!Array.isArray(xs) && !ArrayBuffer.isView(xs)) throw fail('Нужен список чисел.', 'A list of numbers is required.', 'type');
    const a = Array.from(xs, Number);
    if (a.length < min) throw fail(`Нужно хотя бы ${min} ${min === 1 ? 'число' : 'числа'}.`, `At least ${min} number${min === 1 ? '' : 's'} required.`, 'range');
    if (!a.every(fin)) throw fail('В данных есть не числа.', 'The data contain non-numbers.', 'nan');
    return a;
}
function sumAccurate(a) {
    // Neumaier summation
    let s = 0, c = 0;
    for (const v of a) {
        const t = s + v;
        c += Math.abs(s) >= Math.abs(v) ? (s - t) + v : (v - t) + s;
        s = t;
    }
    return s + c;
}
const isSample = (kind) => kind === 'sample' || (kind && typeof kind === 'object' && kind.sample);

export function statMean(xs) {
    const a = nums(xs);
    return sumAccurate(a) / a.length;
}

export function statMedian(xs) {
    const a = nums(xs).sort((p, q) => p - q);
    const m = a.length >> 1;
    return a.length % 2 ? a[m] : (a[m - 1] + a[m]) / 2;
}

/** The most frequent values, ascending; [] when all distinct values are equally frequent (no mode). */
export function statMode(xs) {
    const a = nums(xs);
    const cnt = new Map();
    for (const v of a) cnt.set(v, (cnt.get(v) ?? 0) + 1);
    const max = Math.max(...cnt.values());
    if (cnt.size > 1 && [...cnt.values()].every((c) => c === max)) return [];
    return [...cnt.entries()].filter(([, c]) => c === max).map(([v]) => v).sort((p, q) => p - q);
}

/** Variance: population (÷ n) by default; 'sample' or {sample: true} divides by n − 1. */
export function statVariance(xs, kind = 'population') {
    const a = nums(xs, isSample(kind) ? 2 : 1);
    const m = statMean(a);
    const ss = sumAccurate(a.map((v) => (v - m) * (v - m)));
    return ss / (isSample(kind) ? a.length - 1 : a.length);
}

export function statStd(xs, kind = 'population') {
    return Math.sqrt(statVariance(xs, kind));
}

/** Quantile with linear interpolation between order statistics (R type 7, Excel PERCENTILE.INC). */
export function statQuantile(xs, p) {
    const a = nums(xs).sort((u, v) => u - v);
    if (!(p >= 0 && p <= 1)) throw fail('Уровень квантиля — число от 0 до 1.', 'The quantile level must be between 0 and 1.', 'range');
    const h = (a.length - 1) * p;
    const lo = Math.floor(h);
    return lo + 1 < a.length ? a[lo] + (h - lo) * (a[lo + 1] - a[lo]) : a[lo];
}

/** Pearson correlation coefficient r. */
export function statCorrelation(xs, ys) {
    const x = nums(xs, 2), y = nums(ys, 2);
    if (x.length !== y.length) throw fail('Списки разной длины.', 'The lists have different lengths.', 'range');
    const mx = statMean(x), my = statMean(y);
    let sxy = 0, sxx = 0, syy = 0;
    for (let i = 0; i < x.length; i++) {
        const dx = x[i] - mx, dy = y[i] - my;
        sxy += dx * dy; sxx += dx * dx; syy += dy * dy;
    }
    if (sxx === 0 || syy === 0) return NaN;
    return sxy / Math.sqrt(sxx * syy);
}

function pointsOf(points) {
    const P = Array.from(points, (p) => (Array.isArray(p) ? [Number(p[0]), Number(p[1])] : [Number(p.x), Number(p.y)]));
    if (!P.every(([x, y]) => fin(x) && fin(y))) throw fail('Точки должны быть парами чисел.', 'Points must be pairs of numbers.', 'type');
    return P;
}

/** Least-squares line y = a·x + b → {a, b, r, r2, slope: a, intercept: b}. Points: [[x, y]] or [{x, y}]. */
export function statLinearRegression(points) {
    const P = pointsOf(points);
    if (P.length < 2) throw fail('Нужно хотя бы две точки.', 'At least two points are required.', 'range');
    const mx = statMean(P.map((p) => p[0])), my = statMean(P.map((p) => p[1]));
    let sxy = 0, sxx = 0, syy = 0;
    for (const [x, y] of P) { sxy += (x - mx) * (y - my); sxx += (x - mx) ** 2; syy += (y - my) ** 2; }
    if (sxx === 0) throw fail('У всех точек одинаковый x — прямую вида y = ax + b провести нельзя.', 'All points have the same x, so no line y = ax + b fits.', 'degenerate');
    const a = sxy / sxx, b = my - a * mx;
    const r = syy === 0 ? 1 : sxy / Math.sqrt(sxx * syy);
    return { a, b, r, r2: syy === 0 ? 1 : r * r, slope: a, intercept: b };
}

/** Householder QR least squares: minimise |A·x − y| (A is m×n, m ≥ n, full rank). */
function lstsq(A, y) {
    const m = A.length, n = A[0].length;
    const R = A.map((r) => r.slice());
    const b = y.slice();
    for (let k = 0; k < n; k++) {
        let norm = 0;
        for (let i = k; i < m; i++) norm += R[i][k] * R[i][k];
        norm = Math.sqrt(norm);
        if (norm === 0) throw fail('Задача вырождена.', 'The problem is degenerate.', 'degenerate');
        const alpha = R[k][k] > 0 ? -norm : norm;
        const v = new Array(m).fill(0);
        for (let i = k; i < m; i++) v[i] = R[i][k];
        v[k] -= alpha;
        let vv = 0;
        for (let i = k; i < m; i++) vv += v[i] * v[i];
        if (vv === 0) continue;
        for (let j = k; j < n; j++) {
            let s = 0;
            for (let i = k; i < m; i++) s += v[i] * R[i][j];
            s = (2 * s) / vv;
            for (let i = k; i < m; i++) R[i][j] -= s * v[i];
        }
        let s = 0;
        for (let i = k; i < m; i++) s += v[i] * b[i];
        s = (2 * s) / vv;
        for (let i = k; i < m; i++) b[i] -= s * v[i];
    }
    const x = new Array(n).fill(0);
    for (let i = n - 1; i >= 0; i--) {
        let s = b[i];
        for (let j = i + 1; j < n; j++) s -= R[i][j] * x[j];
        if (Math.abs(R[i][i]) < 1e-300) throw fail('Задача вырождена.', 'The problem is degenerate.', 'degenerate');
        x[i] = s / R[i][i];
    }
    return x;
}

/** Least-squares polynomial of the given degree → {coefs: [c0, c1, …] (ascending), r2}. */
export function statPolyFit(points, degree) {
    const P = pointsOf(points);
    degree = Math.floor(degree);
    if (!(degree >= 0)) throw fail('Степень — неотрицательное целое.', 'The degree must be a non-negative integer.', 'range');
    if (P.length < degree + 1) throw fail(`Для степени ${degree} нужно хотя бы ${degree + 1} точек.`, `Degree ${degree} needs at least ${degree + 1} points.`, 'range');
    const xs = P.map((p) => p[0]), ys = P.map((p) => p[1]);
    const mx = statMean(xs);
    const sx = Math.max(...xs.map((x) => Math.abs(x - mx))) || 1;
    const A = xs.map((x) => { const t = (x - mx) / sx; const row = [1]; for (let j = 1; j <= degree; j++) row.push(row[j - 1] * t); return row; });
    const d = lstsq(A, ys);
    // expand Σ d_j ((x − mx)/sx)^j into powers of x
    const coefs = new Array(degree + 1).fill(0);
    const binom = (n, k) => { let r = 1; for (let i = 1; i <= k; i++) r = (r * (n - k + i)) / i; return r; };
    for (let j = 0; j <= degree; j++) {
        const cj = d[j] / sx ** j;
        for (let k = 0; k <= j; k++) coefs[k] += cj * binom(j, k) * (-mx) ** (j - k);
    }
    const my = statMean(ys);
    let ssr = 0, sst = 0;
    for (let i = 0; i < P.length; i++) {
        let v = 0;
        for (let j = degree; j >= 0; j--) v = v * ((xs[i] - mx) / sx) + d[j];
        ssr += (ys[i] - v) ** 2;
        sst += (ys[i] - my) ** 2;
    }
    return { coefs, r2: sst === 0 ? 1 : 1 - ssr / sst };
}

// ---------------------------------------------------------------- special functions and probability

const LANCZOS = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059,
    12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
const FACT = (() => { const f = [1]; for (let i = 1; i <= 170; i++) f.push(f[i - 1] * i); return f; })();

/** ln|Γ(x)| (Lanczos, ~15 digits). */
export function numLogGamma(x) {
    if (Number.isInteger(x) && x > 0 && x <= 171) return Math.log(FACT[x - 1]);
    if (x < 0.5) return Math.log(Math.PI / Math.abs(Math.sin(Math.PI * x))) - numLogGamma(1 - x);
    x -= 1;
    let a = LANCZOS[0];
    const t = x + 7.5;
    for (let i = 1; i < 9; i++) a += LANCZOS[i] / (x + i);
    return 0.5 * Math.log(2 * Math.PI) + (x + 0.5) * Math.log(t) - t + Math.log(a);
}

/** Γ(x) (exact factorials for integers up to 171; poles give NaN). */
export function numGamma(x) {
    if (Number.isInteger(x)) return x <= 0 ? NaN : x <= 171 ? FACT[x - 1] : Infinity;
    if (x < 0.5) return Math.PI / (Math.sin(Math.PI * x) * numGamma(1 - x));
    if (x > 171.6) return Infinity;
    x -= 1;
    let a = LANCZOS[0];
    const t = x + 7.5;
    for (let i = 1; i < 9; i++) a += LANCZOS[i] / (x + i);
    return Math.sqrt(2 * Math.PI) * t ** (x + 0.5) * Math.exp(-t) * a;
}

function erfcCf(x) {
    // x ≥ 2: erfc(x) = e^(−x²)/√π · 1/(x + (1/2)/(x + 1/(x + (3/2)/(x + …)))) by the modified Lentz method
    const tiny = 1e-300;
    let f = x, C = x, D = 0;
    for (let n = 1; n < 500; n++) {
        const an = n / 2;
        D = x + an * D;
        D = Math.abs(D) < tiny ? 1 / tiny : 1 / D;
        C = x + an / C;
        if (Math.abs(C) < tiny) C = tiny;
        const delta = C * D;
        f *= delta;
        if (Math.abs(delta - 1) < 1e-16) break;
    }
    return Math.exp(-x * x) / (Math.sqrt(Math.PI) * f);
}
function erfSeries(x) {
    // erf(x) = 2/√π · e^(−x²) · Σ 2ⁿ x^(2n+1) / (1·3·…·(2n+1)) — all terms positive
    let term = x, sum = x;
    const x2 = 2 * x * x;
    for (let n = 1; n < 500; n++) {
        term *= x2 / (2 * n + 1);
        sum += term;
        if (Math.abs(term) < 1e-17 * Math.abs(sum)) break;
    }
    return (2 / Math.sqrt(Math.PI)) * Math.exp(-x * x) * sum;
}

/** The error function erf(x). */
export function probErf(x) {
    if (Number.isNaN(x)) return NaN;
    if (x < 0) return -probErf(-x);
    if (x < 2.5) return erfSeries(x);
    return 1 - erfcCf(x);
}

/** The complementary error function erfc(x) = 1 − erf(x), accurate in the tail. */
export function probErfc(x) {
    if (Number.isNaN(x)) return NaN;
    if (x < 0) return 2 - probErfc(-x);
    if (x < 2.5) return 1 - erfSeries(x);
    if (x > 27) return 0;
    return erfcCf(x);
}

export function probNormalPdf(x, mu = 0, sigma = 1) {
    const z = (x - mu) / sigma;
    return Math.exp(-0.5 * z * z) / (sigma * Math.sqrt(2 * Math.PI));
}

/** Φ((x − μ)/σ), accurate in both tails. */
export function probNormalCdf(x, mu = 0, sigma = 1) {
    return 0.5 * probErfc(-(x - mu) / (sigma * Math.SQRT2));
}

/** Normal quantile: Acklam's approximation polished by Halley's method (full double precision). */
export function probNormalInv(p, mu = 0, sigma = 1) {
    if (!(p >= 0 && p <= 1)) throw fail('Вероятность — число от 0 до 1.', 'A probability must be between 0 and 1.', 'range');
    if (p === 0) return -Infinity;
    if (p === 1) return Infinity;
    const a = [-3.969683028665376e+01, 2.209460984245205e+02, -2.759285104469687e+02, 1.383577518672690e+02, -3.066479806614716e+01, 2.506628277459239e+00];
    const b = [-5.447609879822406e+01, 1.615858368580409e+02, -1.556989798598866e+02, 6.680131188771972e+01, -1.328068155288572e+01];
    const c = [-7.784894002430293e-03, -3.223964580411365e-01, -2.400758277161838e+00, -2.549732539343734e+00, 4.374664141464968e+00, 2.938163982698783e+00];
    const d = [7.784695709041462e-03, 3.224671290700398e-01, 2.445134137142996e+00, 3.754408661907416e+00];
    const pl = 0.02425;
    let x;
    if (p < pl) {
        const q = Math.sqrt(-2 * Math.log(p));
        x = (((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1);
    } else if (p <= 1 - pl) {
        const q = p - 0.5, r = q * q;
        x = (((((a[0] * r + a[1]) * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * q / (((((b[0] * r + b[1]) * r + b[2]) * r + b[3]) * r + b[4]) * r + 1);
    } else {
        const q = Math.sqrt(-2 * Math.log(1 - p));
        x = -(((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1);
    }
    for (let i = 0; i < 2; i++) {
        const e = (p < 0.5 ? probNormalCdf(x) - p : (1 - p) - probNormalCdf(-x));
        const u = e * Math.sqrt(2 * Math.PI) * Math.exp((x * x) / 2);
        x -= u / (1 + (x * u) / 2);
    }
    return mu + sigma * x;
}

/** Binomial coefficient C(n, k) as an exact BigInt (0 outside 0 ≤ k ≤ n). */
export function probChoose(n, k) {
    const N = BigInt(n), K0 = BigInt(k);
    if (K0 < 0n || N < 0n || K0 > N) return 0n;
    const K = K0 > N - K0 ? N - K0 : K0;
    let r = 1n;
    for (let i = 1n; i <= K; i++) r = (r * (N - K + i)) / i;
    return r;
}

/** n! as an exact BigInt. */
export function probFactorial(n) {
    const N = BigInt(n);
    if (N < 0n) throw fail('Факториал определён для неотрицательных целых.', 'The factorial is defined for non-negative integers.', 'range');
    let r = 1n;
    for (let i = 2n; i <= N; i++) r *= i;
    return r;
}

/** Arrangements A(n, k) = n!/(n − k)! as an exact BigInt. */
export function probArrangements(n, k) {
    const N = BigInt(n), K = BigInt(k);
    if (K < 0n || N < 0n || K > N) return 0n;
    let r = 1n;
    for (let i = 0n; i < K; i++) r *= N - i;
    return r;
}

// Loader's saddle-point pieces (as in R's dbinom/dpois): accurate pmf values for large n
function stirlerr(n) {
    // ln(n!) − ln(√(2πn)·(n/e)^n)
    if (n <= 15) return numLogGamma(n + 1) - (n + 0.5) * Math.log(n) + n - 0.5 * Math.log(2 * Math.PI);
    const n2 = n * n;
    return (1 / 12 - (1 / 360 - (1 / 1260 - (1 / 1680 - 1 / (1188 * n2)) / n2) / n2) / n2) / n;
}
function bd0(x, np) {
    // x·ln(x/np) + np − x without cancellation
    if (Math.abs(x - np) < 0.1 * (x + np)) {
        const v = (x - np) / (x + np);
        let s = (x - np) * v, ej = 2 * x * v;
        for (let j = 1; j < 1000; j++) {
            ej *= v * v;
            const s1 = s + ej / (2 * j + 1);
            if (s1 === s) return s1;
            s = s1;
        }
        return s;
    }
    return x * Math.log(x / np) + np - x;
}

export function probBinomialPmf(k, n, p) {
    if (!Number.isInteger(k) || !Number.isInteger(n) || k < 0 || k > n) return 0;
    if (p === 0) return k === 0 ? 1 : 0;
    if (p === 1) return k === n ? 1 : 0;
    if (n <= 60) return Number(probChoose(n, k)) * p ** k * (1 - p) ** (n - k);
    const q = 1 - p;
    if (k === 0) return Math.exp(n * Math.log1p(-p));
    if (k === n) return Math.exp(n * Math.log(p));
    const lc = stirlerr(n) - stirlerr(k) - stirlerr(n - k) - bd0(k, n * p) - bd0(n - k, n * q);
    const lf = Math.log(2 * Math.PI) + Math.log(k) + Math.log1p(-k / n);
    return Math.exp(lc - 0.5 * lf);
}

/** Regularized incomplete beta I_x(a, b) (continued fraction, Lentz). */
export function probBetaRegularized(x, a, b) {
    if (x <= 0) return 0;
    if (x >= 1) return 1;
    const lbt = numLogGamma(a + b) - numLogGamma(a) - numLogGamma(b) + a * Math.log(x) + b * Math.log1p(-x);
    const bt = Math.exp(lbt);
    const cf = (a2, b2, x2) => {
        const tiny = 1e-300;
        let c = 1, d = 1 - ((a2 + b2) * x2) / (a2 + 1);
        if (Math.abs(d) < tiny) d = tiny;
        d = 1 / d;
        let h = d;
        for (let m = 1; m <= 1000; m++) {
            const m2 = 2 * m;
            let aa = (m * (b2 - m) * x2) / ((a2 + m2 - 1) * (a2 + m2));
            d = 1 + aa * d; if (Math.abs(d) < tiny) d = tiny;
            c = 1 + aa / c; if (Math.abs(c) < tiny) c = tiny;
            d = 1 / d; h *= d * c;
            aa = (-(a2 + m) * (a2 + b2 + m) * x2) / ((a2 + m2) * (a2 + m2 + 1));
            d = 1 + aa * d; if (Math.abs(d) < tiny) d = tiny;
            c = 1 + aa / c; if (Math.abs(c) < tiny) c = tiny;
            d = 1 / d;
            const del = d * c;
            h *= del;
            if (Math.abs(del - 1) < 1e-16) break;
        }
        return h;
    };
    if (x < (a + 1) / (a + b + 2)) return (bt * cf(a, b, x)) / a;
    return 1 - (bt * cf(b, a, 1 - x)) / b;
}

/** Regularized lower incomplete gamma P(a, x). */
export function probGammaRegularized(a, x) {
    if (x <= 0) return 0;
    if (x === Infinity) return 1;
    const gln = numLogGamma(a);
    if (x < a + 1) {
        let ap = a, sum = 1 / a, del = sum;
        for (let n = 1; n < 10000; n++) {
            ap += 1;
            del *= x / ap;
            sum += del;
            if (Math.abs(del) < Math.abs(sum) * 1e-17) break;
        }
        return sum * Math.exp(-x + a * Math.log(x) - gln);
    }
    const tiny = 1e-300;
    let b = x + 1 - a, c = 1 / tiny, d = 1 / b, h = d;
    for (let i = 1; i < 10000; i++) {
        const an = -i * (i - a);
        b += 2;
        d = an * d + b; if (Math.abs(d) < tiny) d = tiny;
        c = b + an / c; if (Math.abs(c) < tiny) c = tiny;
        d = 1 / d;
        const del = d * c;
        h *= del;
        if (Math.abs(del - 1) < 1e-16) break;
    }
    return 1 - Math.exp(-x + a * Math.log(x) - gln) * h;
}

/** P(X ≤ k) for X ~ Bin(n, p). */
export function probBinomialCdf(k, n, p) {
    k = Math.floor(k);
    if (k < 0) return 0;
    if (k >= n) return 1;
    if (p === 0) return 1;
    if (p === 1) return 0;
    if (n <= 1000) {
        let s = 0;
        for (let i = 0; i <= k; i++) s += probBinomialPmf(i, n, p);
        return Math.min(1, s);
    }
    return probBetaRegularized(1 - p, n - k, k + 1);
}

export function probPoissonPmf(k, lambda) {
    if (!Number.isInteger(k) || k < 0) return 0;
    if (lambda === 0) return k === 0 ? 1 : 0;
    if (k === 0) return Math.exp(-lambda);
    if (k < 10) return Math.exp(k * Math.log(lambda) - lambda) / FACT[k];
    return Math.exp(-stirlerr(k) - bd0(k, lambda)) / Math.sqrt(2 * Math.PI * k);
}

/** P(X ≤ k) for X ~ Poisson(λ). */
export function probPoissonCdf(k, lambda) {
    k = Math.floor(k);
    if (k < 0) return 0;
    if (lambda === 0) return 1;
    return 1 - probGammaRegularized(k + 1, lambda);
}

/** Geometric distribution, k = number of the first success: P(X = k) = (1 − p)^(k−1)·p, k ≥ 1. */
export function probGeometricPmf(k, p) {
    if (!Number.isInteger(k) || k < 1) return 0;
    return (1 - p) ** (k - 1) * p;
}

/** P(X ≤ k) for the geometric distribution (number of the first success). */
export function probGeometricCdf(k, p) {
    k = Math.floor(k);
    if (k < 1) return 0;
    return 1 - (1 - p) ** k;
}

/** Student's t distribution function with df degrees of freedom (df = Infinity → normal). */
export function probStudentTCdf(t, df) {
    if (!(df > 0)) throw fail('Число степеней свободы должно быть положительным.', 'The degrees of freedom must be positive.', 'range');
    if (df === Infinity) return probNormalCdf(t);
    if (t === 0) return 0.5;
    const x = df / (df + t * t);
    const tail = 0.5 * probBetaRegularized(x, df / 2, 0.5);
    return t > 0 ? 1 - tail : tail;
}

/** Quantile of Student's t: probStudentTInv(0.975, 10) ≈ 2.228 (critical values for confidence intervals). */
export function probStudentTInv(p, df) {
    if (!(p > 0 && p < 1)) {
        if (p === 0) return -Infinity;
        if (p === 1) return Infinity;
        throw fail('Вероятность — число от 0 до 1.', 'A probability must be between 0 and 1.', 'range');
    }
    if (df === Infinity) return probNormalInv(p);
    if (p === 0.5) return 0;
    if (p < 0.5) return -probStudentTInv(1 - p, df);
    let hi = Math.max(1, 2 * probNormalInv(p));
    while (probStudentTCdf(hi, df) < p) hi *= 2;
    return numBrent((t) => probStudentTCdf(t, df) - p, 0, hi, { tol: 1e-15 }).root;
}

/** χ² distribution function with k degrees of freedom. */
export function probChiSquareCdf(x, k) {
    if (x <= 0) return 0;
    return probGammaRegularized(k / 2, x / 2);
}

// ---------------------------------------------------------------- interpolation and polynomials

/** Lagrange interpolation through points [[x, y]] → {fn(x), coefs: [c0, c1, …] ascending}. */
export function numLagrange(points) {
    const P = pointsOf(points);
    const n = P.length;
    if (!n) throw fail('Нужна хотя бы одна точка.', 'At least one point is required.', 'range');
    const xs = P.map((p) => p[0]), ys = P.map((p) => p[1]);
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
        if (xs[i] === xs[j]) throw fail('У двух точек одинаковый x — через них не провести график функции.', 'Two points share the same x, so no function passes through both.', 'degenerate');
    }
    // barycentric weights for evaluation
    const w = xs.map((xi, i) => 1 / xs.reduce((prod, xj, j) => (j === i ? prod : prod * (xi - xj)), 1));
    const fn = (x) => {
        let num = 0, den = 0;
        for (let i = 0; i < n; i++) {
            if (x === xs[i]) return ys[i];
            const t = w[i] / (x - xs[i]);
            num += t * ys[i];
            den += t;
        }
        return num / den;
    };
    // Newton divided differences → monomial coefficients
    const dd = ys.slice();
    for (let j = 1; j < n; j++) for (let i = n - 1; i >= j; i--) dd[i] = (dd[i] - dd[i - 1]) / (xs[i] - xs[i - j]);
    let coefs = [dd[n - 1]];
    for (let i = n - 2; i >= 0; i--) {
        // coefs = coefs·(x − x_i) + dd[i]
        const next = new Array(coefs.length + 1).fill(0);
        for (let k = 0; k < coefs.length; k++) { next[k + 1] += coefs[k]; next[k] -= coefs[k] * xs[i]; }
        next[0] += dd[i];
        coefs = next;
    }
    return { fn, coefs };
}

/**
 * All complex roots of a polynomial with real (double) coefficients, ascending order
 * [c0, c1, …, cn] (Aberth–Ehrlich iteration + Newton polish) → [{re, im}] sorted by re, then im.
 */
export function numPolyRoots(coefs) {
    let c = Array.from(coefs, Number);
    while (c.length && c[c.length - 1] === 0) c.pop();
    if (c.length < 2) return [];
    const roots = [];
    while (c[0] === 0 && c.length > 1) { roots.push({ re: 0, im: 0 }); c = c.slice(1); }
    const n = c.length - 1;
    if (n === 0) return roots;
    const lead = c[n];
    const a = c.map((v) => v / lead);
    // initial guesses on a circle (Cauchy-type bound)
    let R = 0;
    for (let k = 0; k < n; k++) R = Math.max(R, Math.abs(a[k]) ** (1 / (n - k)));
    R = Math.max(R, 1e-3);
    const zr = new Float64Array(n), zi = new Float64Array(n);
    for (let k = 0; k < n; k++) { const t = (2 * Math.PI * k) / n + 0.4; zr[k] = R * Math.cos(t); zi[k] = R * Math.sin(t); }
    const evalP = (xr, xi) => {
        let pr = a[n], pi = 0, dr = 0, di = 0;
        for (let k = n - 1; k >= 0; k--) {
            const ndr = dr * xr - di * xi + pr, ndi = dr * xi + di * xr + pi;
            dr = ndr; di = ndi;
            const npr = pr * xr - pi * xi + a[k], npi = pr * xi + pi * xr;
            pr = npr; pi = npi;
        }
        return [pr, pi, dr, di];
    };
    for (let it = 0; it < 800; it++) {
        let maxStep = 0;
        for (let k = 0; k < n; k++) {
            const [pr, pi, dr, di] = evalP(zr[k], zi[k]);
            if (pr === 0 && pi === 0) continue;
            const dd = dr * dr + di * di;
            if (dd === 0) { zr[k] += 1e-8 * (1 + Math.abs(zr[k])); continue; }
            // ratio = p / p'
            const qr = (pr * dr + pi * di) / dd, qi = (pi * dr - pr * di) / dd;
            let sr = 0, si = 0;
            for (let j = 0; j < n; j++) {
                if (j === k) continue;
                const xr = zr[k] - zr[j], xi = zi[k] - zi[j];
                const m = xr * xr + xi * xi;
                if (m === 0) continue;
                sr += xr / m; si -= xi / m;
            }
            // w = ratio / (1 − ratio·sum)
            const tr = 1 - (qr * sr - qi * si), ti = -(qr * si + qi * sr);
            const tm = tr * tr + ti * ti;
            const wr = (qr * tr + qi * ti) / tm, wi = (qi * tr - qr * ti) / tm;
            zr[k] -= wr; zi[k] -= wi;
            maxStep = Math.max(maxStep, Math.hypot(wr, wi) / Math.max(1, Math.hypot(zr[k], zi[k])));
        }
        if (maxStep < 1e-15) break;
    }
    // multiple roots come out as tight clusters: replace a cluster of m by the root of p^(m−1) near its centre
    const done = new Array(n).fill(false);
    const deriv = (cf) => cf.slice(1).map((v, i) => v * (i + 1));
    for (let k = 0; k < n; k++) {
        if (done[k]) continue;
        const mag = Math.max(1, Math.hypot(zr[k], zi[k]));
        const cl = [k];
        for (let j = k + 1; j < n; j++) if (!done[j] && Math.hypot(zr[j] - zr[k], zi[j] - zi[k]) < 1e-5 * mag) cl.push(j);
        if (cl.length < 2) continue;
        let cr = 0, ci = 0;
        for (const j of cl) { cr += zr[j] / cl.length; ci += zi[j] / cl.length; }
        let q = a.slice();
        for (let t = 1; t < cl.length; t++) q = deriv(q);
        const m = q.length - 1;
        for (let s = 0; s < 8 && m >= 1; s++) {
            let pr = q[m], pi = 0, dr = 0, di = 0;
            for (let t = m - 1; t >= 0; t--) {
                const ndr = dr * cr - di * ci + pr, ndi = dr * ci + di * cr + pi;
                dr = ndr; di = ndi;
                const npr = pr * cr - pi * ci + q[t], npi = pr * ci + pi * cr;
                pr = npr; pi = npi;
            }
            const dd = dr * dr + di * di;
            if (dd === 0) break;
            const sr = (pr * dr + pi * di) / dd, si = (pi * dr - pr * di) / dd;
            cr -= sr; ci -= si;
            if (Math.hypot(sr, si) < 1e-16 * mag) break;
        }
        for (const j of cl) { zr[j] = cr; zi[j] = ci; done[j] = true; }
    }
    for (let k = 0; k < n; k++) {
        // a couple of Newton polishing steps for simple roots
        for (let s = 0; s < 2 && !done[k]; s++) {
            const [pr, pi, dr, di] = evalP(zr[k], zi[k]);
            const dd = dr * dr + di * di;
            if (dd === 0) break;
            zr[k] -= (pr * dr + pi * di) / dd;
            zi[k] -= (pi * dr - pr * di) / dd;
        }
        const mag = Math.max(1, Math.hypot(zr[k], zi[k]));
        let im = zi[k];
        if (Math.abs(im) < 1e-10 * mag) im = 0;
        else if (Math.abs(im) < 1e-6 * mag) {
            // a multiple real root splits into a tiny complex cluster: snap when p(re) is zero to rounding
            const x = zr[k];
            let p = 0, scale = 0;
            for (let j = n; j >= 0; j--) { p = p * x + a[j]; scale = scale * Math.abs(x) + Math.abs(a[j]); }
            if (Math.abs(p) <= 1e-12 * scale) im = 0;
        }
        roots.push({ re: zr[k], im });
    }
    return roots.sort((u, v) => u.re - v.re || u.im - v.im);
}
