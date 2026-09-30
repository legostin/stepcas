// linalg/qpoly — polynomials over Q for characteristic polynomials (internal).

import { Q, bigGcd, rootExtract } from '../core/rational.js';
import { ntDivisors } from '../numbers/theory/index.js';
import { numPolyRoots } from '../numbers/numeric/index.js';
import { Poly } from '../core/poly.js';
import { qt } from './common.js';

// ---------------------------------------------------------------- polynomials over Q (internal)

export const ptrim = (a) => {
    const b = a.slice();
    while (b.length > 1 && b[b.length - 1].isZero()) b.pop();
    return b;
};
export const padd = (a, b) => ptrim(Array.from({ length: Math.max(a.length, b.length) }, (_, i) => (a[i] ?? Q.ZERO).add(b[i] ?? Q.ZERO)));
export const psub = (a, b) =>
    padd(
        a,
        b.map((c) => c.neg()),
    );
export function pmul(a, b) {
    const out = new Array(a.length + b.length - 1).fill(Q.ZERO);
    for (let i = 0; i < a.length; i++) {
        if (a[i].isZero()) continue;
        for (let j = 0; j < b.length; j++) out[i + j] = out[i + j].add(a[i].mul(b[j]));
    }
    return ptrim(out);
}
export const pdeg = (a) => {
    const t = ptrim(a);
    return t.length === 1 && t[0].isZero() ? -1 : t.length - 1;
};
const peval = (a, x) => a.reduceRight((acc, c) => acc.mul(x).add(c), Q.ZERO);
export function pdiv(a, b) {
    let r = ptrim(a);
    const d = ptrim(b);
    const db = d.length - 1;
    const lead = d[db];
    const q = new Array(Math.max(1, r.length - db)).fill(Q.ZERO);
    while (pdeg(r) >= db && pdeg(r) >= 0) {
        const k = r.length - 1 - db;
        const c = r[r.length - 1].div(lead);
        q[k] = c;
        for (let i = 0; i <= db; i++) r[k + i] = r[k + i].sub(c.mul(d[i]));
        r = ptrim(r.slice(0, r.length - 1).length ? r.slice(0, r.length - 1) : [Q.ZERO]);
        if (r.length === 1 && r[0].isZero()) break;
    }
    return { q: ptrim(q), r };
}
/** Polynomial TeX in descending powers: \lambda^{3} - 6\lambda^{2} + 11\lambda - 6. */
export function ptex(a, v = '\\lambda') {
    const t = ptrim(a);
    let s = '';
    for (let k = t.length - 1; k >= 0; k--) {
        const c = t[k];
        if (c.isZero()) continue;
        const ac = c.abs();
        const coef = k > 0 && ac.isOne() ? '' : qt(ac);
        const mon = k === 0 ? '' : k === 1 ? v : `${v}^{${k}}`;
        const term = `${coef}${mon}`;
        s += s === '' ? (c.isNeg() ? `-${term}` : term) : ` ${c.isNeg() ? '-' : '+'} ${term}`;
    }
    return s || '0';
}
export function intPrimitive(a) {
    let den = 1n;
    for (const c of a) den = (den / bigGcd(den, c.d)) * c.d;
    let ints = a.map((c) => c.n * (den / c.d));
    let g = 0n;
    for (const x of ints) g = bigGcd(g, x);
    if (g > 1n) ints = ints.map((x) => x / g);
    return ints;
}
const babs = (x) => (x < 0n ? -x : x);

/** Rational roots with multiplicities and the remaining factor: {roots: [{root, mult}], rest}. */
export function rationalRootsQ(a) {
    let rest = ptrim(a);
    const roots = [];
    let zero = 0;
    while (pdeg(rest) > 0 && rest[0].isZero()) {
        rest = rest.slice(1);
        zero++;
    }
    if (zero) roots.push({ root: Q.ZERO, mult: zero });
    if (pdeg(rest) >= 1) {
        const ints = intPrimitive(rest);
        const a0 = babs(ints[0]),
            an = babs(ints[ints.length - 1]);
        const cands = [];
        if (a0 < 10n ** 15n && an < 10n ** 15n) {
            const P = ntDivisors(a0),
                Qd = ntDivisors(an);
            if (P.length * Qd.length <= 50000) {
                const seen = new Set();
                for (const p of P)
                    for (const q of Qd) {
                        for (const s of [1n, -1n]) {
                            const r = new Q(s * p, q);
                            const key = r.toString();
                            if (!seen.has(key)) {
                                seen.add(key);
                                cands.push(r);
                            }
                        }
                    }
            }
        }
        if (!cands.length) {
            // numeric guidance for huge coefficients: round approximate real roots to p/q with q | an
            const approx = numPolyRoots(rest.map((c) => c.toNumber())).filter((z) => z.im === 0);
            const dens = an < 10n ** 6n ? ntDivisors(an) : [1n];
            for (const z of approx) for (const q of dens) cands.push(new Q(BigInt(Math.round(z.re * Number(q))), q));
        }
        cands.sort((x, y) => x.cmp(y));
        for (const r of cands) {
            let mult = 0;
            while (pdeg(rest) >= 1 && peval(rest, r).isZero()) {
                rest = pdiv(rest, [r.neg(), Q.ONE]).q;
                mult++;
            }
            if (mult) roots.push({ root: r, mult });
        }
    }
    roots.sort((x, y) => x.root.cmp(y.root));
    return { roots, rest };
}

/** A quadratic factor over Z of a primitive integer polynomial of degree ≥ 4, or null. */
export function quadFactor(rest) {
    const ints = intPrimitive(rest);
    const deg = ints.length - 1;
    if (deg < 4) return null;
    const ev = (x) => ints.reduceRight((acc, c) => acc * x + c, 0n);
    const v0 = ev(0n),
        v1 = ev(1n),
        vm = ev(-1n),
        v2 = ev(2n);
    if ([v0, v1, vm].some((v) => v === 0n || babs(v) > 10n ** 12n)) return null;
    const lead = babs(ints[deg]);
    const signed = (v) => {
        const d = ntDivisors(babs(v));
        return [...d, ...d.map((x) => -x)];
    };
    const D0 = signed(v0),
        D1 = signed(v1),
        Dm = signed(vm);
    if (D0.length * D1.length * Dm.length > 400000) return null;
    for (const c of D0) {
        for (const u of D1) {
            for (const w of Dm) {
                // Q(0) = c, Q(1) = u, Q(−1) = w  ⇒  a = (u + w)/2 − c, b = (u − w)/2
                if ((u + w) % 2n !== 0n) continue;
                const a = (u + w) / 2n - c,
                    b = (u - w) / 2n;
                if (a <= 0n || lead % a !== 0n) continue;
                const q2 = 4n * a + 2n * b + c;
                if (q2 === 0n || v2 % q2 !== 0n) continue;
                const cand = [new Q(c), new Q(b), new Q(a)];
                const dv = pdiv(
                    ints.map((x) => new Q(x)),
                    cand,
                );
                if (dv.r.every((x) => x.isZero())) return cand;
            }
        }
    }
    return null;
}

/** Roots of a quadratic a₂x² + a₁x + a₀ over Q: p ± q·√s (s squarefree, may be negative). */
export function quadRoots(qf) {
    const [c, b, a] = qf;
    const D = b.mul(b).sub(new Q(4n).mul(a).mul(c));
    const p = b.neg().div(a.mul(new Q(2n)));
    // √D = √(n/d) = √(n·d)/d = out·√in / d
    const nd = D.n * D.d;
    const { out, in: inn } = rootExtract(nd, 2);
    const qq = new Q(babs(out), D.d).div(a.mul(new Q(2n)).abs());
    return { p, q: qq, s: inn, D };
}
export function surdTex(p, q, s, sign) {
    // p + sign·q·√s, s squarefree (negative → imaginary)
    const imag = s < 0n;
    const rad = babs(s);
    const den = (p.d / bigGcd(p.d, q.d)) * q.d;
    const P = p.n * (den / p.d),
        Rr = q.n * (den / q.d);
    const root = `${Rr === 1n ? '' : Rr.toString()}${rad === 1n ? '' : `\\sqrt{${rad}}`}${imag ? (rad === 1n ? 'i' : '\\,i') : ''}` || '1';
    const num = P === 0n ? `${sign < 0 ? '-' : ''}${root}` : `${P} ${sign < 0 ? '-' : '+'} ${root}`;
    if (den === 1n) return num;
    if (P === 0n) return `${sign < 0 ? '-' : ''}\\frac{${root}}{${den}}`;
    return `\\frac{${num}}{${den}}`;
}

export const toPoly = (coefs) => Poly.fromCoeffs(coefs);
