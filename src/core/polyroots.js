// core/polyroots — all complex roots of a polynomial with double coefficients (Aberth–Ehrlich); used by exact code to
// locate roots before it checks them exactly, and re-exported by numbers/numeric.

/**
 * All complex roots of a polynomial with real (double) coefficients, ascending order
 * [c0, c1, …, cn] (Aberth–Ehrlich iteration + Newton polish) → [{re, im}] sorted by re, then im.
 */
export function numPolyRoots(coefs) {
    let c = Array.from(coefs, Number);
    while (c.length && c[c.length - 1] === 0) c.pop();
    if (c.length < 2) return [];
    const roots = [];
    while (c[0] === 0 && c.length > 1) {
        roots.push({ re: 0, im: 0 });
        c = c.slice(1);
    }
    const n = c.length - 1;
    if (n === 0) return roots;
    const lead = c[n];
    const a = c.map((v) => v / lead);
    // initial guesses on a circle (Cauchy-type bound)
    let R = 0;
    for (let k = 0; k < n; k++) R = Math.max(R, Math.abs(a[k]) ** (1 / (n - k)));
    R = Math.max(R, 1e-3);
    const zr = new Float64Array(n),
        zi = new Float64Array(n);
    for (let k = 0; k < n; k++) {
        const t = (2 * Math.PI * k) / n + 0.4;
        zr[k] = R * Math.cos(t);
        zi[k] = R * Math.sin(t);
    }
    const evalP = (xr, xi) => {
        let pr = a[n],
            pi = 0,
            dr = 0,
            di = 0;
        for (let k = n - 1; k >= 0; k--) {
            const ndr = dr * xr - di * xi + pr,
                ndi = dr * xi + di * xr + pi;
            dr = ndr;
            di = ndi;
            const npr = pr * xr - pi * xi + a[k],
                npi = pr * xi + pi * xr;
            pr = npr;
            pi = npi;
        }
        return [pr, pi, dr, di];
    };
    for (let it = 0; it < 800; it++) {
        let maxStep = 0;
        for (let k = 0; k < n; k++) {
            const [pr, pi, dr, di] = evalP(zr[k], zi[k]);
            if (pr === 0 && pi === 0) continue;
            const dd = dr * dr + di * di;
            if (dd === 0) {
                zr[k] += 1e-8 * (1 + Math.abs(zr[k]));
                continue;
            }
            // ratio = p / p'
            const qr = (pr * dr + pi * di) / dd,
                qi = (pi * dr - pr * di) / dd;
            let sr = 0,
                si = 0;
            for (let j = 0; j < n; j++) {
                if (j === k) continue;
                const xr = zr[k] - zr[j],
                    xi = zi[k] - zi[j];
                const m = xr * xr + xi * xi;
                if (m === 0) continue;
                sr += xr / m;
                si -= xi / m;
            }
            // w = ratio / (1 − ratio·sum)
            const tr = 1 - (qr * sr - qi * si),
                ti = -(qr * si + qi * sr);
            const tm = tr * tr + ti * ti;
            const wr = (qr * tr + qi * ti) / tm,
                wi = (qi * tr - qr * ti) / tm;
            zr[k] -= wr;
            zi[k] -= wi;
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
        let cr = 0,
            ci = 0;
        for (const j of cl) {
            cr += zr[j] / cl.length;
            ci += zi[j] / cl.length;
        }
        let q = a.slice();
        for (let t = 1; t < cl.length; t++) q = deriv(q);
        const m = q.length - 1;
        for (let s = 0; s < 8 && m >= 1; s++) {
            let pr = q[m],
                pi = 0,
                dr = 0,
                di = 0;
            for (let t = m - 1; t >= 0; t--) {
                const ndr = dr * cr - di * ci + pr,
                    ndi = dr * ci + di * cr + pi;
                dr = ndr;
                di = ndi;
                const npr = pr * cr - pi * ci + q[t],
                    npi = pr * ci + pi * cr;
                pr = npr;
                pi = npi;
            }
            const dd = dr * dr + di * di;
            if (dd === 0) break;
            const sr = (pr * dr + pi * di) / dd,
                si = (pi * dr - pr * di) / dd;
            cr -= sr;
            ci -= si;
            if (Math.hypot(sr, si) < 1e-16 * mag) break;
        }
        for (const j of cl) {
            zr[j] = cr;
            zi[j] = ci;
            done[j] = true;
        }
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
            let p = 0,
                scale = 0;
            for (let j = n; j >= 0; j--) {
                p = p * x + a[j];
                scale = scale * Math.abs(x) + Math.abs(a[j]);
            }
            if (Math.abs(p) <= 1e-12 * scale) im = 0;
        }
        roots.push({ re: zr[k], im });
    }
    return roots.sort((u, v) => u.re - v.re || u.im - v.im);
}
