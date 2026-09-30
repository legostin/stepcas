// numeric/interpolation — interpolation and polynomial helpers on doubles.

import { fail } from './common.js';
import { pointsOf } from './statistics.js';
import { msg } from '../../i18n/index.js';

// ---------------------------------------------------------------- interpolation and polynomials

/** Lagrange interpolation through points [[x, y]] → {fn(x), coefs: [c0, c1, …] ascending}. */
export function numLagrange(points) {
    const P = pointsOf(points);
    const n = P.length;
    if (!n) throw fail(msg('numbers.numeric.interpolation.at_least_one_point_is_required'), 'range');
    const xs = P.map((p) => p[0]),
        ys = P.map((p) => p[1]);
    for (let i = 0; i < n; i++)
        for (let j = i + 1; j < n; j++) {
            if (xs[i] === xs[j]) throw fail(msg('numbers.numeric.interpolation.two_points_share_same_x_so'), 'degenerate');
        }
    // barycentric weights for evaluation
    const w = xs.map((xi, i) => 1 / xs.reduce((prod, xj, j) => (j === i ? prod : prod * (xi - xj)), 1));
    const fn = (x) => {
        let num = 0,
            den = 0;
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
        for (let k = 0; k < coefs.length; k++) {
            next[k + 1] += coefs[k];
            next[k] -= coefs[k] * xs[i];
        }
        next[0] += dd[i];
        coefs = next;
    }
    return { fn, coefs };
}

export { numPolyRoots } from '../../core/polyroots.js';
