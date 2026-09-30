// solve/families — periodic families of roots x = base + period·n, n ∈ ℤ: making, merging (a family inside another,
// two halves of one), printing in the school form, listing as roots.

import { sym, add, mul, div, num } from '../core/ast.js';
import { msg, notation, inLanguage } from '../i18n/index.js';
import { simpOr, approxOf, isZeroNode, tex } from './common.js';

export const N_SYM = sym('n');

export const ZZ = (l) => msg('solve.trig.n_z').in(l);

/** A family x = base + period·n; gid groups families that are printed together. */
export function mkFamily(base, period, gid = null) {
    const b = simpOr(base);
    const p = simpOr(period);
    return { base: b, period: p, b: approxOf(b), p: approxOf(p), gid };
}

/** "a + b" of already simplified terms (zeros dropped), printed without re-simplifying. */
export function plusTex(nodes, lang) {
    const ns = nodes.filter((n) => !isZeroNode(n));
    if (!ns.length) return '0';
    return tex(ns.length === 1 ? ns[0] : add(ns), lang);
}

export const signedTex = (t) => (t.startsWith('-') ? ` ${t}` : ` + ${t}`);

export const periodN = (p) => simpOr(mul(p, N_SYM));

export function familyTex(f, v, lang) {
    return `${v} = ${plusTex([f.base, periodN(f.period)], lang)}`;
}

/** Answer lines for a list of families: the group's school form when intact, else one line per family. */
export function familiesTex(fams, v, lang, sep) {
    const lines = [];
    const done = new Set();
    for (const f of fams) {
        if (f.group && !done.has(f.group)) {
            const members = fams.filter((g) => g.group === f.group);
            if (members.length === f.group.size) {
                lines.push(inLanguage(f.group.tex, lang));
                done.add(f.group);
                continue;
            }
        }
        if (f.group && done.has(f.group)) continue;
        lines.push(familyTex(f, v, lang));
    }
    return lines.join(sep ?? notation(lang).listWideTex) + ZZ(lang);
}

export function familiesToRoots(fams) {
    return fams.map((f) => ({ node: simpOr(add(f.base, mul(f.period, N_SYM))), approx: f.b, mult: 1, family: { base: f.base, period: f.period, param: 'n' } }));
}

/** Is family a (base a, period p) contained in family b? */
function famSubset(a, b) {
    const r = a.p / b.p;
    if (Math.abs(r - Math.round(r)) > 1e-9 || Math.round(r) < 1) return false;
    const d = (a.b - b.b) / b.p;
    return Math.abs(d - Math.round(d)) <= 1e-9;
}

/** Drop families contained in others; join m families with a common period into one with period/m. */
export function mergeFamilies(fams) {
    let out = [];
    for (const f of fams) {
        if (out.some((g) => famSubset(f, g))) continue;
        out = out.filter((g) => !famSubset(g, f));
        out.push(f);
    }
    // join: two families with equal period P whose bases differ by an odd multiple of P/2
    let changed = true;
    while (changed) {
        changed = false;
        for (let i = 0; i < out.length && !changed; i++) {
            for (let j = i + 1; j < out.length && !changed; j++) {
                const f = out[i];
                const g = out[j];
                if (Math.abs(f.p - g.p) > 1e-12 * Math.max(1, f.p)) continue;
                const d = (g.b - f.b) / (f.p / 2);
                const r = Math.round(d);
                if (Math.abs(d - r) > 1e-9 || r % 2 === 0) continue;
                const first = Math.abs(g.b) < Math.abs(f.b) - 1e-12 ? g : f;
                const nf = mkFamily(first.base, div(first.period, num(2)));
                out = out.filter((x) => x !== f && x !== g);
                out.push(nf);
                changed = true;
            }
        }
    }
    return out.sort((a, b) => a.p - b.p || a.b - b.b);
}
