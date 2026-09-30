// solve/roots — roots, their TeX and the answer of an equation.

import { nodeSome, num, add, neg, mul } from '../core/ast.js';
import { Q } from '../core/rational.js';
import { Poly } from '../core/poly.js';
import { toText } from '../core/print.js';
import { approxC, approxOf, approxTex, close, exactZero, simpOr, tex } from './common.js';
import { IntervalSet, intervalTex, intervalText, parseIntervalSet } from './intervals.js';
import { N_SYM, familiesTex } from './families.js';
import { msg, notation, eachLanguage, decimalIn, DEFAULT_LANGUAGE } from '../i18n/index.js';

// ---------------------------------------------------------------- roots and their TeX

// Root record: {node, approx: number | {re, im}, mult, minPoly?: Poly, approxOnly?: true, complex?: true}
export function mkRoot(node, extra = {}) {
    return { node, approx: approxOf(node), mult: 1, ...extra };
}

export const hasI = (n) => nodeSome(n, (x) => x.type === 'sym' && x.name === 'i' && !x.var);

/** A root that may be non-real (complex coefficients): {node, approx: number | {re, im}, complex?}. */
export function mkRootC(node) {
    const x = approxOf(node);
    if (Number.isFinite(x)) return mkRoot(node);
    const z = approxC(node);
    if (!z) return mkRoot(node);
    if (Math.abs(z.im) <= 1e-12 * Math.max(1, Math.abs(z.re))) return { node, approx: z.re, mult: 1 };
    return { node, approx: z, mult: 1, complex: true };
}

export function qRoot(q, extra = {}) {
    q = Q.of(q);
    return { node: num(q), approx: q.toNumber(), mult: 1, minPoly: new Poly([q.neg(), Q.ONE]), ...extra };
}

export function approxComplexTex(z, lang) {
    if (Math.abs(z.im) < 1e-12) return approxTex(z.re, lang);
    const re = Math.abs(z.re) < 1e-12 ? '' : approxTex(z.re, lang);
    const im = approxTex(Math.abs(z.im), lang);
    const sign = z.im < 0 ? '-' : re ? '+' : '';
    return `${re} ${sign} ${im}i`.trim();
}

function rootValueTex(r, lang) {
    if (r.approxOnly) return `\\approx ${r.complex ? approxComplexTex(r.approx, lang) : approxTex(r.approx, lang)}`;
    return `= ${tex(r.node, lang)}`;
}

/** x_1 = 2;\quad x_2 = 3 (one root: x = 2). */
export function rootsTex(roots, v, lang, start = 1) {
    if (!roots.length) return msg('solve.roots.no_roots').in(lang);
    const idx = roots.length > 1;
    return roots.map((r, k) => `${idx ? `${v}_{${k + start}}` : v} ${rootValueTex(r, lang)}`).join(notation(lang).listWideTex);
}

/** Distinct roots, ascending (complex ones after the real ones); equal roots merge (mult added when sum). */
export function mergeRoots(list, sumMult = false) {
    const out = [];
    for (const r of list) {
        const same = out.find((o) => sameRoot(o, r));
        if (same) {
            if (sumMult) same.mult += r.mult;
            else same.mult = Math.max(same.mult, r.mult);
            if (same.approxOnly && !r.approxOnly) Object.assign(same, { node: r.node, approxOnly: undefined });
            continue;
        }
        out.push({ ...r });
    }
    return out.sort(cmpRoots);
}

export function cmpRoots(a, b) {
    const ar = typeof a.approx === 'number';
    const br = typeof b.approx === 'number';
    if (ar && br) return a.approx - b.approx;
    if (ar !== br) return ar ? -1 : 1;
    return a.approx.re - b.approx.re || a.approx.im - b.approx.im;
}

export function sameRoot(a, b) {
    const ar = typeof a.approx === 'number';
    const br = typeof b.approx === 'number';
    if (ar !== br) return false;
    const near = ar
        ? close(a.approx, b.approx, 1e-9)
        : Math.hypot(a.approx.re - b.approx.re, a.approx.im - b.approx.im) <= 1e-9 * Math.max(1, Math.hypot(a.approx.re, a.approx.im));
    if (!near) return false;
    if (a.approxOnly || b.approxOnly) return true;
    const z = exactZero(add(a.node, neg(b.node)), ar ? undefined : { complex: true });
    return z !== false;
}

// ---------------------------------------------------------------- answers

function approxText(z, lang) {
    const f = (x) => {
        const t = String(Number(x.toFixed(4)));
        return decimalIn(t, lang, { tex: false });
    };
    if (typeof z === 'number') return f(z);
    if (Math.abs(z.im) < 1e-12) return f(z.re);
    return `${f(z.re)} ${z.im < 0 ? '-' : '+'} ${f(Math.abs(z.im))}i`;
}

export function answerOf(res, v) {
    const none = msg('solve.roots.no_roots');
    switch (res.kind) {
        case 'none':
            return { tex: none, text: msg('solve.roots.no_roots_2') };
        case 'all':
        case 'set': {
            const set = res.set;
            if (!set || set.isAll()) {
                return res.kind === 'all' && res.odzPartial
                    ? { tex: msg('solve.roots.any_in_domain', { v }), text: msg('solve.roots.any_number_in_domain') }
                    : { tex: `${v} \\in \\mathbb{R}`, text: msg('solve.roots.any_number') };
            }
            return { tex: eachLanguage((l) => `${v} \\in ${intervalTex(set, l)}`), text: eachLanguage((l) => intervalText(set, l)) };
        }
        case 'roots':
            if (res.families) {
                return {
                    tex: eachLanguage((l) => familiesTex(res.families, v, l)),
                    text: eachLanguage(
                        (l) => `${res.families.map((f) => `${v} = ${toText(simpOr(add(f.base, mul(f.period, N_SYM))), { lang: l })}`).join('; ')}, n ∈ Z`,
                    ),
                };
            }
            return {
                tex: eachLanguage((l) => rootsTex(res.roots, v, l)),
                text: eachLanguage((l) =>
                    res.roots.map((r) => (r.approxOnly ? `≈ ${approxText(r.approx, l)}` : toText(r.node, { lang: l }))).join(notation(l).listText),
                ),
            };
        default:
            return { tex: '', text: res.reason ?? msg('solve.roots.could_not_solve') };
    }
}

export function toIntervalOpt(iv, lang = DEFAULT_LANGUAGE) {
    if (!iv) return null;
    let set;
    if (iv instanceof IntervalSet) set = iv;
    else if (Array.isArray(iv)) set = IntervalSet.interval(iv[0], iv[1], true, true);
    else if (typeof iv === 'string') set = parseIntervalSet(iv, lang);
    else return null;
    if (set.parts.length !== 1 || set.parts[0].lo === null || set.parts[0].hi === null) return null;
    return set;
}

/** Roots of the families that lie in a bounded interval (exact nodes, ascending). */
export function rootsOnInterval(fams, set) {
    const p = set.parts[0];
    const lo = p.lo.x;
    const hi = p.hi.x;
    const out = [];
    for (const f of fams) {
        if (!(f.p > 0)) continue;
        const n0 = Math.ceil((lo - f.b) / f.p - 1e-9);
        const n1 = Math.floor((hi - f.b) / f.p + 1e-9);
        if (n1 - n0 > 400) return null;
        for (let n = n0; n <= n1; n++) {
            const node = simpOr(add(f.base, mul(num(n), f.period)));
            const x = approxOf(node);
            if (set.contains(node)) out.push({ node, approx: x, mult: 1 });
        }
    }
    return mergeRoots(out);
}

/** Remember roots dropped by a sub-solver (they are reported as extraneous with the reason). */
export function reject(ctx, roots, reason) {
    if (!ctx.rejected) return;
    for (const r of roots) if (!ctx.rejected.some((x) => sameRoot(x, r))) ctx.rejected.push({ node: r.node, approx: r.approx, reason });
}
