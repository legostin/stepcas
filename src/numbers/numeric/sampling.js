// numeric/sampling — sampling functions for plots (adaptive, with breaks at poles).

import { evalSafe, fin, needFn, needInterval, numLinspace } from './common.js';

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
                xa = xm;
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
