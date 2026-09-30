// numeric/statistics — descriptive statistics, regression, special functions and probability distributions.

import { fail, fin } from './common.js';
import { numBrent } from './roots.js';
import { msg } from '../../i18n/index.js';

// ---------------------------------------------------------------- statistics

function nums(xs, min = 1) {
    if (!Array.isArray(xs) && !ArrayBuffer.isView(xs)) throw fail(msg('numbers.numeric.statistics.list_of_numbers_is_required'), 'type');
    const a = Array.from(xs, Number);
    if (a.length < min)
        throw fail(
            msg('numbers.numeric.statistics.at_least_number_required', {
                min,
                p: (lng) => (min === 1 ? msg('numbers.numeric.statistics.formula').in(lng) : msg('numbers.numeric.statistics.s').in(lng)),
            }),
            'range',
        );
    if (!a.every(fin)) throw fail(msg('numbers.numeric.statistics.data_contain_non_numbers'), 'nan');
    return a;
}
function sumAccurate(a) {
    // Neumaier summation
    let s = 0,
        c = 0;
    for (const v of a) {
        const t = s + v;
        c += Math.abs(s) >= Math.abs(v) ? s - t + v : v - t + s;
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
    return [...cnt.entries()]
        .filter(([, c]) => c === max)
        .map(([v]) => v)
        .sort((p, q) => p - q);
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
    if (!(p >= 0 && p <= 1)) throw fail(msg('numbers.numeric.statistics.quantile_level_must_be_between_0'), 'range');
    const h = (a.length - 1) * p;
    const lo = Math.floor(h);
    return lo + 1 < a.length ? a[lo] + (h - lo) * (a[lo + 1] - a[lo]) : a[lo];
}

/** Pearson correlation coefficient r. */
export function statCorrelation(xs, ys) {
    const x = nums(xs, 2),
        y = nums(ys, 2);
    if (x.length !== y.length) throw fail(msg('numbers.numeric.statistics.lists_have_different_lengths'), 'range');
    const mx = statMean(x),
        my = statMean(y);
    let sxy = 0,
        sxx = 0,
        syy = 0;
    for (let i = 0; i < x.length; i++) {
        const dx = x[i] - mx,
            dy = y[i] - my;
        sxy += dx * dy;
        sxx += dx * dx;
        syy += dy * dy;
    }
    if (sxx === 0 || syy === 0) return NaN;
    return sxy / Math.sqrt(sxx * syy);
}

export function pointsOf(points) {
    const P = Array.from(points, (p) => (Array.isArray(p) ? [Number(p[0]), Number(p[1])] : [Number(p.x), Number(p.y)]));
    if (!P.every(([x, y]) => fin(x) && fin(y))) throw fail(msg('numbers.numeric.statistics.points_must_be_pairs_of_numbers'), 'type');
    return P;
}

/** Least-squares line y = a·x + b → {a, b, r, r2, slope: a, intercept: b}. Points: [[x, y]] or [{x, y}]. */
export function statLinearRegression(points) {
    const P = pointsOf(points);
    if (P.length < 2) throw fail(msg('numbers.numeric.statistics.at_least_two_points_are_required'), 'range');
    const mx = statMean(P.map((p) => p[0])),
        my = statMean(P.map((p) => p[1]));
    let sxy = 0,
        sxx = 0,
        syy = 0;
    for (const [x, y] of P) {
        sxy += (x - mx) * (y - my);
        sxx += (x - mx) ** 2;
        syy += (y - my) ** 2;
    }
    if (sxx === 0) throw fail(msg('numbers.numeric.statistics.all_points_have_same_x_so'), 'degenerate');
    const a = sxy / sxx,
        b = my - a * mx;
    const r = syy === 0 ? 1 : sxy / Math.sqrt(sxx * syy);
    return { a, b, r, r2: syy === 0 ? 1 : r * r, slope: a, intercept: b };
}

/** Householder QR least squares: minimise |A·x − y| (A is m×n, m ≥ n, full rank). */
function lstsq(A, y) {
    const m = A.length,
        n = A[0].length;
    const R = A.map((r) => r.slice());
    const b = y.slice();
    for (let k = 0; k < n; k++) {
        let norm = 0;
        for (let i = k; i < m; i++) norm += R[i][k] * R[i][k];
        norm = Math.sqrt(norm);
        if (norm === 0) throw fail(msg('numbers.numeric.statistics.problem_is_degenerate'), 'degenerate');
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
        if (Math.abs(R[i][i]) < 1e-300) throw fail(msg('numbers.numeric.statistics.problem_is_degenerate'), 'degenerate');
        x[i] = s / R[i][i];
    }
    return x;
}

/** Least-squares polynomial of the given degree → {coefs: [c0, c1, …] (ascending), r2}. */
export function statPolyFit(points, degree) {
    const P = pointsOf(points);
    degree = Math.floor(degree);
    if (!(degree >= 0)) throw fail(msg('numbers.numeric.statistics.degree_must_be_non_negative_integer'), 'range');
    if (P.length < degree + 1) throw fail(msg('numbers.numeric.statistics.degree_needs_at_least_points', { degree, p: degree + 1 }), 'range');
    const xs = P.map((p) => p[0]),
        ys = P.map((p) => p[1]);
    const mx = statMean(xs);
    const sx = Math.max(...xs.map((x) => Math.abs(x - mx))) || 1;
    const A = xs.map((x) => {
        const t = (x - mx) / sx;
        const row = [1];
        for (let j = 1; j <= degree; j++) row.push(row[j - 1] * t);
        return row;
    });
    const d = lstsq(A, ys);
    // expand Σ d_j ((x − mx)/sx)^j into powers of x
    const coefs = new Array(degree + 1).fill(0);
    const binom = (n, k) => {
        let r = 1;
        for (let i = 1; i <= k; i++) r = (r * (n - k + i)) / i;
        return r;
    };
    for (let j = 0; j <= degree; j++) {
        const cj = d[j] / sx ** j;
        for (let k = 0; k <= j; k++) coefs[k] += cj * binom(j, k) * (-mx) ** (j - k);
    }
    const my = statMean(ys);
    let ssr = 0,
        sst = 0;
    for (let i = 0; i < P.length; i++) {
        let v = 0;
        for (let j = degree; j >= 0; j--) v = v * ((xs[i] - mx) / sx) + d[j];
        ssr += (ys[i] - v) ** 2;
        sst += (ys[i] - my) ** 2;
    }
    return { coefs, r2: sst === 0 ? 1 : 1 - ssr / sst };
}

// ---------------------------------------------------------------- special functions and probability

const LANCZOS = [
    0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059, 12.507343278686905, -0.13857109526572012,
    9.9843695780195716e-6, 1.5056327351493116e-7,
];
const FACT = (() => {
    const f = [1];
    for (let i = 1; i <= 170; i++) f.push(f[i - 1] * i);
    return f;
})();

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
    let f = x,
        C = x,
        D = 0;
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
    let term = x,
        sum = x;
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
    if (!(p >= 0 && p <= 1)) throw fail(msg('numbers.numeric.statistics.probability_must_be_between_0_and'), 'range');
    if (p === 0) return -Infinity;
    if (p === 1) return Infinity;
    const a = [-3.969683028665376e1, 2.209460984245205e2, -2.759285104469687e2, 1.38357751867269e2, -3.066479806614716e1, 2.506628277459239];
    const b = [-5.447609879822406e1, 1.615858368580409e2, -1.556989798598866e2, 6.680131188771972e1, -1.328068155288572e1];
    const c = [-7.784894002430293e-3, -3.223964580411365e-1, -2.400758277161838, -2.549732539343734, 4.374664141464968, 2.938163982698783];
    const d = [7.784695709041462e-3, 3.224671290700398e-1, 2.445134137142996, 3.754408661907416];
    const pl = 0.02425;
    let x;
    if (p < pl) {
        const q = Math.sqrt(-2 * Math.log(p));
        x = (((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1);
    } else if (p <= 1 - pl) {
        const q = p - 0.5,
            r = q * q;
        x = ((((((a[0] * r + a[1]) * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * q) / (((((b[0] * r + b[1]) * r + b[2]) * r + b[3]) * r + b[4]) * r + 1);
    } else {
        const q = Math.sqrt(-2 * Math.log(1 - p));
        x = -(((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1);
    }
    for (let i = 0; i < 2; i++) {
        const e = p < 0.5 ? probNormalCdf(x) - p : 1 - p - probNormalCdf(-x);
        const u = e * Math.sqrt(2 * Math.PI) * Math.exp((x * x) / 2);
        x -= u / (1 + (x * u) / 2);
    }
    return mu + sigma * x;
}

/** Binomial coefficient C(n, k) as an exact BigInt (0 outside 0 ≤ k ≤ n). */
export function probChoose(n, k) {
    const N = BigInt(n),
        K0 = BigInt(k);
    if (K0 < 0n || N < 0n || K0 > N) return 0n;
    const K = K0 > N - K0 ? N - K0 : K0;
    let r = 1n;
    for (let i = 1n; i <= K; i++) r = (r * (N - K + i)) / i;
    return r;
}

/** n! as an exact BigInt. */
export function probFactorial(n) {
    const N = BigInt(n);
    if (N < 0n) throw fail(msg('numbers.numeric.statistics.factorial_is_defined_for_non_negative'), 'range');
    let r = 1n;
    for (let i = 2n; i <= N; i++) r *= i;
    return r;
}

/** Arrangements A(n, k) = n!/(n − k)! as an exact BigInt. */
export function probArrangements(n, k) {
    const N = BigInt(n),
        K = BigInt(k);
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
        let s = (x - np) * v,
            ej = 2 * x * v;
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
        let c = 1,
            d = 1 - ((a2 + b2) * x2) / (a2 + 1);
        if (Math.abs(d) < tiny) d = tiny;
        d = 1 / d;
        let h = d;
        for (let m = 1; m <= 1000; m++) {
            const m2 = 2 * m;
            let aa = (m * (b2 - m) * x2) / ((a2 + m2 - 1) * (a2 + m2));
            d = 1 + aa * d;
            if (Math.abs(d) < tiny) d = tiny;
            c = 1 + aa / c;
            if (Math.abs(c) < tiny) c = tiny;
            d = 1 / d;
            h *= d * c;
            aa = (-(a2 + m) * (a2 + b2 + m) * x2) / ((a2 + m2) * (a2 + m2 + 1));
            d = 1 + aa * d;
            if (Math.abs(d) < tiny) d = tiny;
            c = 1 + aa / c;
            if (Math.abs(c) < tiny) c = tiny;
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
        let ap = a,
            sum = 1 / a,
            del = sum;
        for (let n = 1; n < 10000; n++) {
            ap += 1;
            del *= x / ap;
            sum += del;
            if (Math.abs(del) < Math.abs(sum) * 1e-17) break;
        }
        return sum * Math.exp(-x + a * Math.log(x) - gln);
    }
    const tiny = 1e-300;
    let b = x + 1 - a,
        c = 1 / tiny,
        d = 1 / b,
        h = d;
    for (let i = 1; i < 10000; i++) {
        const an = -i * (i - a);
        b += 2;
        d = an * d + b;
        if (Math.abs(d) < tiny) d = tiny;
        c = b + an / c;
        if (Math.abs(c) < tiny) c = tiny;
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
    if (!(df > 0)) throw fail(msg('numbers.numeric.statistics.degrees_of_freedom_must_be_positive'), 'range');
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
        throw fail(msg('numbers.numeric.statistics.probability_must_be_between_0_and'), 'range');
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
