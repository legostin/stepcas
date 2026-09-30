// poly — univariate polynomials over Q (coefficients c[k] of x^k), and linear forms for systems.

import { Q, MathError, bigGcd, bigLcm, bigAbs, bigIsqrt, bigBitLength } from './rational.js';
import { num, sym, add, mul, pow, isConst, numValue } from './ast.js';
import { expand } from './expand.js';
import { toTex } from './print.js';
import { numPolyRoots } from '../numbers/numeric.js';

const MAX_DEG = 10000;
const DIV0 = { ru: 'Деление на нулевой многочлен', en: 'Division by the zero polynomial' };

// ---------------------------------------------------------------- divisors of big integers

function divisorsOf(n) {
    n = bigAbs(n);
    if (n === 0n) return [];
    const primes = [];
    let m = n;
    const addP = (p, e) => primes.push([p, e]);
    for (let p = 2n; p * p <= m && p <= 1000000n; p += p === 2n ? 1n : 2n) {
        if (m % p) continue;
        let e = 0;
        while (m % p === 0n) {
            m /= p;
            e++;
        }
        addP(p, e);
    }
    if (m > 1n) addP(m, 1); // (may be composite for huge inputs — the list is then incomplete)
    let divs = [1n];
    for (const [p, e] of primes) {
        const next = [];
        for (const d of divs) {
            let x = d;
            for (let k = 0; k <= e; k++) {
                next.push(x);
                x *= p;
            }
        }
        divs = next;
        if (divs.length > 20000) break;
    }
    return divs.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

const ENUM_LIMIT = 4000; // |divisors(a0)|·|divisors(an)| up to which every candidate p/q is simply tried
const EPS = 2.220446049250313e-16;

function smallGcd(a, b) {
    while (b) [a, b] = [b, a % b];
    return a;
}

/** ±x/y for x ∈ P, y ∈ Qd (positive divisors), each value once, ascending. */
function allCandidates(P, Qd) {
    const small = P.length && Qd.length && P[P.length - 1] <= 9007199254740991n && Qd[Qd.length - 1] <= 9007199254740991n;
    const Pn = small ? P.map(Number) : null;
    const pos = [];
    for (const y of Qd) {
        const yn = small ? Number(y) : 0;
        for (let i = 0; i < P.length; i++) {
            const coprime = small ? smallGcd(Pn[i], yn) === 1 : bigGcd(P[i], y) === 1n;
            if (coprime) pos.push(new Q(P[i], y));
        }
    }
    const key = pos.map((q) => Number(q.n) / Number(q.d));
    const idx = pos.map((_, i) => i).sort((a, b) => key[a] - key[b] || pos[a].cmp(pos[b]));
    const out = new Array(idx.length * 2);
    for (let i = 0; i < idx.length; i++) {
        out[idx.length - 1 - i] = pos[idx[i]].neg();
        out[idx.length + i] = pos[idx[i]];
    }
    return out;
}

/**
 * Real-root intervals of f (integer coefficients) from Aberth's approximations: every root of f lies
 * in one of the inclusion discs |z − zₖ| ≤ n·|f(zₖ)| / |aₙ·∏(zₖ − zⱼ)| (Braess–Hadeler), rounding of f(zₖ)
 * included; → [[lo, hi]] for the discs that reach the real axis, narrowest first, or null when the numbers do
 * not allow a safe bound.
 */
function realRootIntervals(f) {
    const n = f.degree;
    if (n < 1) return [];
    if (n > 400) return null;
    let bits = 0;
    for (const c of f.c) bits = Math.max(bits, bigBitLength(bigAbs(c.n)));
    if (bits > 1000) return null;
    const a = f.c.map((c) => Number(c.n));
    const zs = numPolyRoots(a);
    if (zs.length !== n) return null;
    // the bound holds for any n distinct points: spread coinciding approximations (a merged cluster) apart
    for (let k = 0; k < n; k++) {
        const same = [];
        for (let j = k + 1; j < n; j++) if (zs[j].re === zs[k].re && zs[j].im === zs[k].im) same.push(j);
        const rho = 1e-9 * Math.max(1, Math.hypot(zs[k].re, zs[k].im));
        same.forEach((j, i) => {
            const t = (2 * Math.PI * (i + 1)) / (same.length + 1);
            zs[j] = { re: zs[k].re + rho * Math.cos(t), im: zs[k].im + rho * Math.sin(t) };
        });
    }
    const lead = Math.abs(a[n]);
    const out = [];
    for (let k = 0; k < n; k++) {
        const { re, im } = zs[k];
        let pr = 0, pi = 0, S = 0;
        const r = Math.hypot(re, im);
        for (let j = n; j >= 0; j--) {
            const t = pr * re - pi * im + a[j];
            pi = pr * im + pi * re;
            pr = t;
            S = S * r + Math.abs(a[j]);
        }
        const err = Math.hypot(pr, pi) + (8 * n + 8) * EPS * S;
        let prod = lead;
        for (let j = 0; j < n; j++) if (j !== k) prod *= Math.hypot(re - zs[j].re, im - zs[j].im);
        const rad = (n * err / prod) * (1 + 1e-6) + 4 * EPS * r;
        if (!Number.isFinite(rad) || !(prod > 0)) return null;
        if (Math.abs(im) <= rad) out.push([re - rad, re + rad]);
    }
    return out.sort((u, v) => u[1] - u[0] - (v[1] - v[0]));
}

/**
 * Rational roots of p0 (primitive, p0(0) ≠ 0) among p/q with p | a0 and q ∈ Qd, found without trying every
 * candidate: the real roots are located numerically (realRootIntervals) and only the candidates inside those
 * intervals are tried — exactly. Narrow intervals go first; every root found is divided out and the rest is
 * located again (a cluster like 1 and 1.0000000003 separates once its neighbours are gone); an interval that
 * still holds too many candidates after that is searched in full, so no rational root is missed. Short integer
 * ranges are tested for p | a0 directly (independent of the divisor list of a0), long ones use getP() — the
 * sorted divisors of a0. → Q[] (the roots, as candidates) or null (no safe bound: try everything).
 */
function nearCandidates(p0, getP, Qd) {
    let f = p0;
    const a0 = bigAbs(p0.c[0].n);
    let P = null, Pf = null;
    const needP = () => {
        if (!P) {
            P = getP();
            Pf = P.map(Number);
        }
    };
    const lower = (x) => {
        let lo = 0, hi = Pf.length;
        while (lo < hi) {
            const m = (lo + hi) >> 1;
            if (Pf[m] < x) lo = m + 1;
            else hi = m;
        }
        return lo;
    };
    // integer ranges [from, to] of numerators for one interval: [{q, sgn, from, to}]
    const ranges = ([lo, hi]) => {
        const out = [];
        for (const q of Qd) {
            const qf = Number(q);
            for (const sgn of [1, -1]) {
                const x0 = sgn > 0 ? lo * qf : -hi * qf;
                const x1 = sgn > 0 ? hi * qf : -lo * qf;
                if (x1 < 1) continue;
                // the integers inside [x0, x1], widened by far more than the rounding of lo·q
                const from = Math.max(1, Math.ceil(x0 - Math.abs(x0) * 1e-12));
                const to = Math.floor(x1 + Math.abs(x1) * 1e-12);
                if (to >= from) out.push({ q, sgn, from, to });
            }
        }
        return out;
    };
    const cost = (rs) => {
        let c = 0;
        for (const { from, to } of rs) {
            if (to - from <= 16) c += to - from + 1;
            else {
                needP();
                c += lower(to + 1) - lower(from);
            }
        }
        return c;
    };
    const found = new Map();
    const tryRanges = (rs) => {
        for (const { q, sgn, from, to } of rs) {
            const test = (x) => {
                if (bigGcd(x, q) !== 1n) return;
                const c = new Q(sgn > 0 ? x : -x, q);
                const key = c.toString();
                if (found.has(key) || f.degree < 1 || !f.evalAt(c).isZero()) return;
                found.set(key, c);
                const lin = new Poly([new Q(-c.n), new Q(c.d)]);
                do f = f.divmod(lin).q;
                while (f.degree >= 1 && f.evalAt(c).isZero());
            };
            if (to - from <= 16) {
                for (let x = BigInt(from), end = BigInt(to); x <= end; x++) if (a0 % x === 0n) test(x);
            } else {
                needP();
                for (let i = lower(from); i < Pf.length && Pf[i] <= to; i++) test(P[i]);
            }
        }
    };
    const CAP = 50000;
    let pending = [];
    for (let round = 0; round < 8 && f.degree >= 1; round++) {
        const iv = realRootIntervals(f);
        if (!iv) {
            if (!round) return null;
            for (const rs of pending) tryRanges(rs);   // the last good bound still covers every root
            break;
        }
        const before = found.size;
        pending = [];
        for (const I of iv) {
            const rs = ranges(I);
            if (cost(rs) > CAP) pending.push(rs);
            else tryRanges(rs);
        }
        if (!pending.length) break;
        if (found.size === before || round === 7) {
            for (const rs of pending) tryRanges(rs);   // no progress: search the wide intervals in full
            break;
        }
    }
    return [...found.values()].sort((x, y) => x.cmp(y));
}

// ---------------------------------------------------------------- AST → Poly

function direct(n, v) {
    switch (n.type) {
        case 'num':
            return new Poly([n.value]);
        case 'sym':
            return n.name === v && !isConst(n) ? new Poly([Q.ZERO, Q.ONE]) : null;
        case 'add': {
            let s = new Poly([]);
            for (const a of n.args) {
                const p = direct(a, v);
                if (!p) return null;
                s = s.add(p);
            }
            return s;
        }
        case 'mul': {
            let s = new Poly([Q.ONE]);
            for (const a of n.args) {
                const p = direct(a, v);
                if (!p) return null;
                s = s.mul(p);
                if (s.degree > MAX_DEG) return null;
            }
            return s;
        }
        case 'neg': {
            const p = direct(n.arg, v);
            return p && p.neg();
        }
        case 'div': {
            const a = direct(n.num, v);
            const b = a && direct(n.den, v);
            if (!b || b.degree !== 0) return null;
            return a.scale(b.c[0].inv());
        }
        case 'pow': {
            const e = numValue(n.exp);
            if (!e || !e.isInt() || e.isNeg() || e.gt(MAX_DEG)) return null;
            const b = direct(n.base, v);
            if (!b || b.degree * Number(e.n) > MAX_DEG) return null;
            return b.pow(Number(e.n));
        }
        default:
            return null;
    }
}

// ---------------------------------------------------------------- Poly

export class Poly {
    /** @param {Array} coeffs  c[k] is the coefficient of x^k (anything Q.of accepts) */
    constructor(coeffs = []) {
        const c = coeffs.map((x) => Q.of(x));
        let n = c.length;
        while (n > 0 && c[n - 1].isZero()) n--;
        this.c = Object.freeze(c.slice(0, n));
        Object.freeze(this);
    }

    /** From coefficients, lowest degree first: fromCoeffs([6, -5, 1]) = x² − 5x + 6. */
    static fromCoeffs(lowToHigh) {
        return new Poly(lowToHigh);
    }

    /** From coefficients, highest degree first: fromDescending([1, -5, 6]) = x² − 5x + 6. */
    static fromDescending(highToLow) {
        return new Poly([...highToLow].reverse());
    }

    /** c·x^k */
    static monomial(c, k) {
        const a = new Array(k + 1).fill(Q.ZERO);
        a[k] = Q.of(c);
        return new Poly(a);
    }

    /** ∏ (x − r) */
    static fromRoots(roots) {
        let p = new Poly([Q.ONE]);
        for (const r of roots) p = p.mul(new Poly([Q.of(r).neg(), Q.ONE]));
        return p;
    }

    /**
     * Polynomial in varName with rational coefficients, or null (other variables, π, √2, sin x, x^(−1)…).
     * A relation lhs = rhs gives lhs − rhs. Tries the node as is, then its expanded form.
     */
    static fromNode(node, varName = 'x') {
        if (node.type === 'rel') {
            if (node.op !== '=') return null;
            const a = Poly.fromNode(node.lhs, varName);
            const b = a && Poly.fromNode(node.rhs, varName);
            return b ? a.sub(b) : null;
        }
        if (node.type === 'chain' || node.type === 'list') return null;
        const p = direct(node, varName);
        if (p) return p;
        try {
            return direct(expand(node), varName);
        } catch {
            return null;
        }
    }

    /** Degree; −1 for the zero polynomial. */
    get degree() {
        return this.c.length - 1;
    }

    /** Leading coefficient (0 for the zero polynomial). */
    get lead() {
        return this.c.length ? this.c[this.c.length - 1] : Q.ZERO;
    }

    coeff(k) {
        return this.c[k] ?? Q.ZERO;
    }

    /** Coefficients from the highest degree down. */
    descending() {
        return [...this.c].reverse();
    }

    isZero() {
        return this.c.length === 0;
    }

    equals(p) {
        return this.c.length === p.c.length && this.c.every((x, k) => x.eq(p.c[k]));
    }

    add(p) {
        const n = Math.max(this.c.length, p.c.length);
        const out = [];
        for (let k = 0; k < n; k++) out.push(this.coeff(k).add(p.coeff(k)));
        return new Poly(out);
    }

    sub(p) {
        return this.add(p.neg());
    }

    neg() {
        return new Poly(this.c.map((x) => x.neg()));
    }

    scale(q) {
        q = Q.of(q);
        return new Poly(this.c.map((x) => x.mul(q)));
    }

    mul(p) {
        if (this.isZero() || p.isZero()) return new Poly([]);
        const out = new Array(this.c.length + p.c.length - 1).fill(Q.ZERO);
        for (let i = 0; i < this.c.length; i++) {
            if (this.c[i].isZero()) continue;
            for (let j = 0; j < p.c.length; j++) out[i + j] = out[i + j].add(this.c[i].mul(p.c[j]));
        }
        return new Poly(out);
    }

    pow(n) {
        if (!Number.isInteger(n) || n < 0) throw new TypeError('Poly.pow needs a non-negative integer');
        if (Math.max(this.degree, 0) * n > MAX_DEG) throw new MathError({ ru: 'Слишком большая степень', en: 'The degree is too large' }, null, null, 'too-big');
        let r = new Poly([Q.ONE]);
        let b = this;
        while (n > 0) {
            if (n & 1) r = r.mul(b);
            n >>= 1;
            if (n) b = b.mul(b);
        }
        return r;
    }

    /** {q, r} with this = q·p + r, deg r < deg p. */
    divmod(p) {
        if (p.isZero()) throw new MathError(DIV0, null, null, 'div0');
        const pd = p.degree;
        if (this.degree < pd) return { q: new Poly([]), r: this };
        const r = [...this.c];
        const q = new Array(this.degree - pd + 1).fill(Q.ZERO);
        const L = p.lead;
        for (let k = this.degree - pd; k >= 0; k--) {
            const t = r[k + pd].div(L);
            q[k] = t;
            if (t.isZero()) continue;
            for (let j = 0; j <= pd; j++) r[k + j] = r[k + j].sub(t.mul(p.c[j]));
        }
        return { q: new Poly(q), r: new Poly(r) };
    }

    /**
     * Long division step by step (деление уголком): {quotient, remainder, steps: [{dividend, term, product,
     * remainder}]} — at each step term = lead(dividend)/lead(p)·x^k, product = term·p, remainder = dividend − product.
     */
    longDivision(p) {
        if (p.isZero()) throw new MathError(DIV0, null, null, 'div0');
        const steps = [];
        let cur = this;
        let quotient = new Poly([]);
        while (!cur.isZero() && cur.degree >= p.degree) {
            const term = Poly.monomial(cur.lead.div(p.lead), cur.degree - p.degree);
            const product = term.mul(p);
            const next = cur.sub(product);
            steps.push({ dividend: cur, term, product, remainder: next });
            quotient = quotient.add(term);
            cur = next;
        }
        return { quotient, remainder: cur, steps };
    }

    /**
     * Horner's scheme at a: {top: coefficients high→low, row: bottom row (same length; the last entry is the
     * value), value: p(a), quotient: p(x) = (x − a)·quotient + value}.
     */
    horner(a) {
        a = Q.of(a);
        const top = this.descending();
        const row = [];
        let acc = Q.ZERO;
        for (const c of top) {
            acc = acc.mul(a).add(c);
            row.push(acc);
        }
        const value = row.length ? row[row.length - 1] : Q.ZERO;
        return { top, row, value, quotient: Poly.fromDescending(row.slice(0, -1)) };
    }

    evalAt(x) {
        x = Q.of(x);
        let acc = Q.ZERO;
        for (let k = this.c.length - 1; k >= 0; k--) acc = acc.mul(x).add(this.c[k]);
        return acc;
    }

    /** Numeric value at a double (for plotting). */
    evalNumber(x) {
        let acc = 0;
        for (let k = this.c.length - 1; k >= 0; k--) acc = acc * x + this.c[k].toNumber();
        return acc;
    }

    derivative() {
        return new Poly(this.c.slice(1).map((x, k) => x.mul(k + 1)));
    }

    monic() {
        return this.isZero() ? this : this.scale(this.lead.inv());
    }

    /** Monic greatest common divisor (zero if both are zero). */
    gcd(p) {
        let a = this;
        let b = p;
        while (!b.isZero()) [a, b] = [b, a.divmod(b).r];
        return a.monic();
    }

    /** c with sign of the leading coefficient such that this / c has coprime integer coefficients. */
    content() {
        if (this.isZero()) return Q.ZERO;
        let g = 0n;
        let l = 1n;
        for (const x of this.c) {
            if (x.isZero()) continue;
            g = bigGcd(g, x.n);
            l = bigLcm(l, x.d);
        }
        const c = new Q(g, l);
        return this.lead.isNeg() ? c.neg() : c;
    }

    /** Integer coefficients, gcd 1, positive leading coefficient. */
    primitive() {
        return this.isZero() ? this : this.scale(this.content().inv());
    }

    /** Candidates ±p/q of the rational root theorem (p | free term, q | leading coefficient), zero roots aside. */
    rootCandidates() {
        const p = this.primitive();
        let k = 0;
        while (k < p.c.length && p.c[k].isZero()) k++;
        if (k >= p.c.length) return [];
        if (p.degree - k < 1) return [];
        return allCandidates(divisorsOf(p.c[k].n), divisorsOf(p.lead.n));
    }

    /**
     * Rational roots with multiplicities, ascending; the array also carries .candidates for the steps.
     * Few candidates (≤ ENUM_LIMIT pairs p/q) are all tried exactly; for many (735134400x⁵ − x − 735134400 has
     * ~74 000) the roots are located numerically first, with rigorous inclusion discs, and only the candidates
     * inside those discs are tried — exactly, so nothing inexact is ever returned and no rational root is missed.
     */
    rationalRoots() {
        const roots = [];
        if (this.isZero()) {
            roots.candidates = [];
            return roots;
        }
        let p = this.primitive();
        let k = 0;
        while (p.c.length && p.c[0].isZero()) {
            p = new Poly(p.c.slice(1));
            k++;
        }
        if (k) roots.push({ root: Q.ZERO, mult: k });
        const full = this;
        let cands = null;
        if (p.degree >= 1) {
            const P = divisorsOf(p.c[0].n);
            const Qd = divisorsOf(p.lead.n);
            cands = P.length * Qd.length <= ENUM_LIMIT ? allCandidates(P, Qd) : nearCandidates(p, () => P, Qd) ?? allCandidates(P, Qd);
        }
        for (const c of cands ?? []) {
            if (p.degree < 1) break;
            let m = 0;
            while (p.degree >= 1 && p.evalAt(c).isZero()) {
                p = p.divmod(new Poly([c.neg(), Q.ONE])).q;
                m++;
            }
            if (m) roots.push({ root: c, mult: m });
        }
        roots.sort((a, b) => a.root.cmp(b.root));
        // the full candidate list (for the steps) is built only when someone reads it
        let list = null;
        Object.defineProperty(roots, 'candidates', {
            enumerable: true,
            configurable: true,
            get: () => (list ??= full.rootCandidates()),
            set: (v) => { list = v; },
        });
        return roots;
    }

    /** Yun's square-free decomposition: [{poly (monic), mult}] with this ∝ ∏ poly^mult. */
    squareFree() {
        if (this.degree < 1) return [];
        const f = this.monic();
        const out = [];
        const f1 = f.derivative();
        let a = f.gcd(f1);
        let b = f.divmod(a).q;
        let c = f1.divmod(a).q;
        let d = c.sub(b.derivative());
        let i = 1;
        while (b.degree > 0) {
            a = b.gcd(d);
            if (a.degree > 0) out.push({ poly: a, mult: i });
            b = b.divmod(a).q;
            c = d.divmod(a).q;
            d = c.sub(b.derivative());
            i++;
            if (i > MAX_DEG) break;
        }
        return out;
    }

    /**
     * Factorisation over Q: {constant, factors: [{poly, mult}]}, factors primitive with integer coefficients and
     * positive leading coefficient; linear factors from rational roots, quartics split into two quadratics
     * when possible, the rest left as irreducible-or-unknown pieces. this = constant · ∏ poly^mult.
     */
    factor() {
        if (this.isZero()) return { constant: Q.ZERO, factors: [] };
        if (this.degree === 0) return { constant: this.c[0], factors: [] };
        const factors = [];
        for (const { poly: s, mult } of this.squareFree()) {
            let q = s.primitive();
            for (const { root } of q.rationalRoots()) {
                const lin = new Poly([new Q(-root.n), new Q(root.d)]);
                factors.push({ poly: lin, mult });
                q = q.divmod(lin).q;
            }
            if (q.degree >= 1) {
                q = q.primitive();
                const split = q.degree === 4 ? splitQuartic(q) : null;
                if (split) for (const h of split) factors.push({ poly: h, mult });
                else factors.push({ poly: q, mult });
            }
        }
        factors.sort((a, b) => a.poly.degree - b.poly.degree || cmpPoly(a.poly, b.poly));
        let leads = Q.ONE;
        for (const { poly, mult } of factors) leads = leads.mul(poly.lead.pow(mult));
        return { constant: this.lead.div(leads), factors };
    }

    /** Discriminant for degree 2 and 3, else null. */
    discriminant() {
        if (this.degree === 2) {
            const [c, b, a] = this.c;
            return b.mul(b).sub(a.mul(c).mul(4));
        }
        if (this.degree === 3) {
            const [d, c, b, a] = this.c;
            return b.mul(b).mul(c).mul(c)
                .sub(a.mul(c.pow(3)).mul(4))
                .sub(b.pow(3).mul(d).mul(4))
                .sub(a.mul(a).mul(d).mul(d).mul(27))
                .add(a.mul(b).mul(c).mul(d).mul(18));
        }
        return null;
    }

    /** Canonical AST (descending powers): x^2 - 5x + 6. */
    toNode(varName = 'x') {
        const X = sym(varName);
        const terms = [];
        for (let k = this.degree; k >= 0; k--) {
            const c = this.c[k];
            if (c.isZero()) continue;
            if (k === 0) {
                terms.push(num(c));
                continue;
            }
            const m = k === 1 ? X : pow(X, num(k));
            terms.push(c.isOne() ? m : mul(num(c), m));
        }
        if (!terms.length) return num(0);
        return terms.length === 1 ? terms[0] : add(terms);
    }

    toTex(varName = 'x', lang = 'ru') {
        return toTex(this.toNode(varName), { lang });
    }

    toString(varName = 'x') {
        const parts = [];
        for (let k = this.degree; k >= 0; k--) {
            const c = this.c[k];
            if (c.isZero()) continue;
            const x = k === 0 ? '' : k === 1 ? varName : `${varName}^${k}`;
            const a = c.abs();
            const coef = k > 0 && a.isOne() ? '' : a.isInt() || k === 0 ? a.toString() : `(${a})`;
            const sep = parts.length ? (c.isNeg() ? ' - ' : ' + ') : c.isNeg() ? '-' : '';
            parts.push(sep + coef + x);
        }
        return parts.length ? parts.join('') : '0';
    }
}

function cmpPoly(a, b) {
    for (let k = a.c.length - 1; k >= 0; k--) {
        const c = a.coeff(k).cmp(b.coeff(k));
        if (c) return c;
    }
    return 0;
}

// (p1 x² + q1 x + r1)(p2 x² + q2 x + r2) with integers, for a primitive quartic without rational roots
function splitQuartic(q) {
    const [e, d, c, b, a] = q.c.map((x) => x.n);
    if (e === 0n) return null;
    const pa = divisorsOf(a);
    const re = divisorsOf(e);
    if (pa.length * re.length > 4000) return null;
    const mk = (r, qq, p) => new Poly([new Q(r), new Q(qq), new Q(p)]).primitive();
    for (const p1 of pa) {
        const p2 = a / p1;
        for (const r0 of re) {
            for (const r1 of [r0, -r0]) {
                const r2 = e / r1;
                const det = p2 * r1 - p1 * r2;
                if (det !== 0n) {
                    const n1 = b * r1 - p1 * d;
                    const n2 = p2 * d - r2 * b;
                    if (n1 % det || n2 % det) continue;
                    const q1 = n1 / det;
                    const q2 = n2 / det;
                    if (p1 * r2 + q1 * q2 + r1 * p2 === c) return [mk(r1, q1, p1), mk(r2, q2, p2)];
                } else {
                    const C = c - p1 * r2 - r1 * p2;
                    const disc = b * b - 4n * p2 * p1 * C;
                    if (disc < 0n) continue;
                    const s = bigIsqrt(disc);
                    if (s * s !== disc) continue;
                    for (const num2 of [b + s, b - s]) {
                        if (num2 % (2n * p2)) continue;
                        const q1 = num2 / (2n * p2);
                        if ((b - p2 * q1) % p1) continue;
                        const q2 = (b - p2 * q1) / p1;
                        if (q1 * r2 + r1 * q2 === d && p1 * r2 + q1 * q2 + r1 * p2 === c) return [mk(r1, q1, p1), mk(r2, q2, p2)];
                    }
                }
            }
        }
    }
    return null;
}

// ---------------------------------------------------------------- linear forms

function lin(n, vars) {
    switch (n.type) {
        case 'num':
            return { c: new Map(), k: n.value };
        case 'sym':
            if (!isConst(n) && vars.includes(n.name)) return { c: new Map([[n.name, Q.ONE]]), k: Q.ZERO };
            return null;
        case 'add': {
            const c = new Map();
            let k = Q.ZERO;
            for (const a of n.args) {
                const r = lin(a, vars);
                if (!r) return null;
                for (const [v, q] of r.c) c.set(v, (c.get(v) ?? Q.ZERO).add(q));
                k = k.add(r.k);
            }
            return { c, k };
        }
        case 'neg': {
            const r = lin(n.arg, vars);
            return r && scaleLin(r, Q.MINUS_ONE);
        }
        case 'mul': {
            let acc = { c: new Map(), k: Q.ONE };
            for (const a of n.args) {
                const r = lin(a, vars);
                if (!r) return null;
                const rc = [...r.c.values()].some((q) => !q.isZero());
                const ac = [...acc.c.values()].some((q) => !q.isZero());
                if (rc && ac) return null;
                acc = rc ? scaleLin(r, acc.k) : scaleLin(acc, r.k);
            }
            return acc;
        }
        case 'div': {
            const a = lin(n.num, vars);
            const b = a && lin(n.den, vars);
            if (!b || [...b.c.values()].some((q) => !q.isZero()) || b.k.isZero()) return null;
            return scaleLin(a, b.k.inv());
        }
        case 'pow': {
            const e = numValue(n.exp);
            if (!e || !e.isInt()) return null;
            if (e.isZero()) return { c: new Map(), k: Q.ONE };
            if (e.isOne()) return lin(n.base, vars);
            const b = lin(n.base, vars);
            if (!b || [...b.c.values()].some((q) => !q.isZero())) return null;
            if (b.k.isZero() && e.isNeg()) return null;
            try {
                return { c: new Map(), k: b.k.pow(e.n) };
            } catch {
                return null;
            }
        }
        default:
            return null;
    }
}

function scaleLin(r, q) {
    const c = new Map();
    for (const [v, x] of r.c) c.set(v, x.mul(q));
    return { c, k: r.k.mul(q) };
}

/**
 * Linear form over Q: {coeffs: {x: Q, y: Q, …} (every listed variable, zeros included), constant: Q} such that
 * node = Σ coeffs·var + constant; for a relation lhs op rhs it describes lhs − rhs. Null when not linear in
 * `vars` with rational coefficients (or when other variables appear).
 */
export function linearForm(node, vars = ['x']) {
    vars = Array.isArray(vars) ? vars : [vars];
    if (node.type === 'rel') {
        const a = linearForm(node.lhs, vars);
        const b = a && linearForm(node.rhs, vars);
        if (!b) return null;
        const coeffs = {};
        for (const v of vars) coeffs[v] = a.coeffs[v].sub(b.coeffs[v]);
        return { coeffs, constant: a.constant.sub(b.constant) };
    }
    let r = lin(node, vars);
    if (!r) {
        try {
            r = lin(expand(node), vars);
        } catch {
            r = null;
        }
    }
    if (!r) return null;
    const coeffs = {};
    for (const v of vars) coeffs[v] = r.c.get(v) ?? Q.ZERO;
    return { coeffs, constant: r.k };
}
