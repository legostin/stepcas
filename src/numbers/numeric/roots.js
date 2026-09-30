// numeric/roots — root finders (bisection, Brent, Newton, all roots on a segment) and one-dimensional optimisation.

import { numDerivative } from './calculus.js';
import { EPS, evalSafe, fail, fin, needFn, needInterval, numLinspace } from './common.js';

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
