// integral/common — what the methods share: constants, TeX, positivity (ln|u| or ln u), the check F′ = f, the answer
// after a substitution and its cleaning. A leaf of integral/: it imports no method and not the engine.

import {
    num,
    sym,
    toNode,
    nodeKey,
    isConst,
    freeVars,
    containsVar,
    add,
    mul,
    fn,
    nodeSize,
    neg,
    nodeChildren,
    div,
    pow,
    mapNode,
    substitute,
} from '../../core/ast.js';
import { Q } from '../../core/rational.js';
import { parse } from '../../core/parse.js';
import { simplify, splitCoeff } from '../../core/simplify.js';
import { calcTex, quickDerivative, prettyForm, niceForm, ratFunctionOf } from '../derivative/index.js';
import { Poly } from '../../core/poly.js';
import { expand } from '../../core/expand.js';
import { rng } from '../../core/random.js';
import { evaluate } from '../../core/evaluate.js';
import { step } from '../../core/steps.js';
import { eachLanguage } from '../../i18n/index.js';

export const N0 = num(0);
export const N1 = num(1);
export const NM1 = num(-1);
export const N2 = num(2);
export const HALF = num(Q.HALF);
export const PI = sym('pi');
export const E_ = sym('e');

export const isNum = (n) => n.type === 'num';
export const isZero = (n) => isNum(n) && n.value.isZero();
export const isOne = (n) => isNum(n) && n.value.isOne();
export const q = (a, b = 1n) => new Q(BigInt(a), BigInt(b));

// ---------------------------------------------------------------- small helpers

export function asNode(x) {
    if (x && typeof x === 'object' && typeof x.type === 'string') return x;
    if (typeof x === 'string') return parse(x);
    return toNode(x);
}

export function simp(node) {
    let s = simplify(node);
    for (let i = 0; i < 3; i++) {
        const t = simplify(s);
        if (nodeKey(t) === nodeKey(s)) break;
        s = t;
    }
    return s;
}

export function trySimp(node) {
    try {
        return simp(node);
    } catch {
        return null;
    }
}

const tall = (s) => /\\frac|\\sqrt|\\left|\\dfrac|\^\{/.test(s);
export const paren = (s) => (tall(s) ? `\\left(${s}\\right)` : `(${s})`);

export function negLeading(n) {
    if (isNum(n)) return n.value.isNeg();
    if (n.type === 'neg') return true;
    if (n.type === 'mul') return n.args.length > 0 && negLeading(n.args[0]);
    return false;
}

export const isVar = (n, v) => n.type === 'sym' && n.name === v && !isConst(n);

/** TeX of ∫ f dv. */
export function iTex(f, v, L) {
    if (isOne(f)) return `\\int d${v}`;
    const s = calcTex(f, L);
    return `\\int ${f.type === 'add' || negLeading(f) ? paren(s) : s}\\,d${v}`;
}

/** TeX of a node for the right-hand side of a step. */
export const tx = (n, L) => calcTex(n, L);

/** A multiplier in front of something: 3, -\frac{1}{2}, (a + 1). */
export function coefTex(c, L) {
    if (isOne(c)) return '';
    if (isNum(c) && c.value.eq(-1)) return '-';
    const s = calcTex(c, L);
    return c.type === 'add' ? paren(s) : s;
}

/** "k dx" for a differential: dx, −dx, 3\\,dx, (2x + 1)\\,dx. */
export function dTex(k, v, L) {
    if (isOne(k)) return `d${v}`;
    if (isNum(k) && k.value.eq(-1)) return `-d${v}`;
    const s = calcTex(k, L);
    return `${k.type === 'add' ? paren(s) : s}\\,d${v}`;
}

export function freshVar(f, v) {
    const used = new Set([...freeVars(f), v]);
    for (const t of ['t', 'u', 'w', 's', 'z', 'p', 'r']) if (!used.has(t)) return t;
    return 't_1';
}

/** Linear in v with coefficients free of v: {k, b} (nodes, k ≠ 0), else null. */
export function linearParts(L, v) {
    if (!containsVar(L, v)) return null;
    let k;
    try {
        k = simp(quickDerivative(L, v));
    } catch {
        return null;
    }
    if (containsVar(k, v) || isZero(k)) return null;
    const b = trySimp(add(L, mul(NM1, k, sym(v))));
    if (!b || containsVar(b, v)) return null;
    return { k, b };
}

// ---------------------------------------------------------------- positivity (ln|u| or ln u)

export function surelyPositive(u, v) {
    if (isNum(u)) return u.value.isPos();
    if (isConst(u)) return u.name === 'pi' || u.name === 'e';
    if (u.type === 'pow') {
        if (isConst(u.base) && u.base.name === 'e') return true;
        if (isNum(u.base) && u.base.value.isPos()) return true;
        if (surelyPositive(u.base, v)) return true;
        return false;
    }
    if (u.type === 'mul') return u.args.every((f) => surelyPositive(f, v));
    if (u.type === 'fn') return u.name === 'cosh' || u.name === 'exp';
    if (u.type === 'add') {
        // Σ nonnegative with a positive constant; or a quadratic with no real roots
        let pos = false;
        let ok = true;
        for (const t of u.args) {
            if (isNum(t)) {
                if (t.value.isPos()) pos = true;
                else ok = false;
            } else if (!nonNegative(t)) ok = false;
        }
        if (ok && pos) return true;
        const P = Poly.fromNode(u, v);
        if (P && P.degree === 2 && P.lead.isPos() && P.discriminant().isNeg()) return true;
        return false;
    }
    return false;
}

function nonNegative(t) {
    const { coef, rest } = splitCoeff(t);
    if (coef.isNeg() || rest === null) return !coef.isNeg();
    const fs = rest.type === 'mul' ? rest.args : [rest];
    return fs.every((f) => {
        if (f.type === 'pow' && isNum(f.exp) && f.exp.value.isInt() && f.exp.value.n % 2n === 0n) return true;
        if (f.type === 'pow' && isNum(f.exp) && f.exp.value.d % 2n === 0n) return true; // even roots, where defined
        if (f.type === 'pow' && isConst(f.base) && f.base.name === 'e') return true;
        if (f.type === 'fn' && (f.name === 'abs' || f.name === 'cosh')) return true;
        if (isNum(f) || (isConst(f) && f.name !== 'i')) return true;
        return false;
    });
}

export function lnAbs(u, v) {
    return surelyPositive(u, v) ? fn('ln', u) : fn('ln', fn('abs', u));
}

// ---------------------------------------------------------------- the check: F′ = f on the domain

const RANGES = [
    [0.2, 1.8],
    [-1.8, -0.2],
    [2, 6],
    [-6, -2],
    [0.05, 0.95],
    [-0.95, -0.05],
    [6, 20],
    [-20, -6],
    [20, 200],
    [-200, -20],
];

/**
 * Is F an antiderivative of f? true / false / null (too few usable points). Points where f is finite but F
 * is not count as a failure (ln x for 1/x is wrong for x < 0).
 */
export function checkAnti(F, f, v, opts = {}) {
    let dF;
    try {
        dF = quickDerivative(F, v);
    } catch {
        return null;
    }
    // exact check first: F′ − f expands to 0 (then only the domain matters; big coefficients such as
    // those of ∫x²⁰eˣ lose too much precision in floating point to compare numerically)
    let exact = false;
    if (nodeSize(dF) + nodeSize(f) < 600) {
        try {
            const d = simp(expand(add(dF, neg(f))));
            exact = isZero(d);
        } catch {
            exact = false;
        }
    }
    const r = rng(opts.seed ?? 4242);
    const others = [...new Set([...freeVars(F), ...freeVars(f)])].filter((w) => w !== v);
    let usable = 0;
    let bad = 0;
    for (let k = 0; k < 40; k++) {
        const env = {};
        for (const w of others) env[w] = r.real(0.6, 1.9);
        const [lo, hi] = RANGES[k % RANGES.length];
        env[v] = r.real(lo, hi);
        let fv;
        let dv;
        let Fv;
        try {
            fv = evaluate(f, env);
            if (!Number.isFinite(fv) || Math.abs(fv) > 1e10) continue;
            dv = evaluate(dF, env);
            Fv = evaluate(F, env);
        } catch {
            return null;
        }
        if (!Number.isFinite(Fv) || !Number.isFinite(dv)) {
            // f is defined here but the answer is not: allowed only at isolated points
            const env2 = { ...env, [v]: env[v] * (1 + 1e-6) + 1e-7 };
            let F2;
            try {
                F2 = evaluate(F, env2);
            } catch {
                return null;
            }
            if (!Number.isFinite(F2)) bad++;
            if (bad >= 2) return false;
            continue;
        }
        usable++;
        if (!exact && Math.abs(dv - fv) > 1e-6 * Math.max(1, Math.abs(fv), Math.abs(dv))) return false;
        if (usable >= 14) break;
    }
    if (exact) return true;
    return usable >= 3 ? true : null;
}

/** Pre-order transform: fnc(node) → replacement (not descended into) or undefined to go deeper. */
export function mapPre(n, fnc) {
    const r = fnc(n);
    if (r !== undefined) return r;
    const kids = nodeChildren(n);
    if (!kids.length) return n;
    const nk = kids.map((c) => mapPre(c, fnc));
    if (nk.every((c, i) => c === kids[i])) return n;
    switch (n.type) {
        case 'add':
            return add(nk);
        case 'mul':
            return mul(nk);
        case 'div':
            return div(nk[0], nk[1]);
        case 'neg':
            return neg(nk[0]);
        case 'pow':
            return pow(nk[0], nk[1]);
        case 'fn':
            return fn(n.name, ...nk);
        default:
            return n;
    }
}

export function plainish(n, L) {
    return toTextSafe(prettyForm(n), L);
}

function toTextSafe(n, L) {
    try {
        let s = calcTex(n, L);
        s = s
            .replace(/\\left|\\right/g, '')
            .replace(/\\operatorname\{(\w+)\}/g, '$1')
            .replace(/\\cdot/g, '·')
            .replace(/\\,/g, ' ');
        s = s
            .replace(/\\frac\{([^{}]*)\}\{([^{}]*)\}/g, '($1)/($2)')
            .replace(/\\sqrt\{([^{}]*)\}/g, '√($1)')
            .replace(/\^\{(-?\d+)\}/g, (m, d) => supDigits(d))
            .replace(/\\([a-z]+)/g, '$1');
        return s.replace(/[{}]/g, '').replace(/\s+/g, ' ').trim();
    } catch {
        return '';
    }
}

export function cleanAnti(F, v) {
    let G = simp(F);
    // atan(tan u) = u up to a piecewise constant — fine for an antiderivative
    G = simp(mapNode(G, (m) => (m.type === 'fn' && m.name === 'atan' && m.args[0].type === 'fn' && m.args[0].name === 'tan' ? m.args[0].args[0] : undefined)));
    // ln|u| with u > 0 everywhere (after a substitution t = eˣ, …) is just ln u
    G = simp(
        mapNode(G, (m) =>
            m.type === 'fn' && m.name === 'ln' && m.args[0].type === 'fn' && m.args[0].name === 'abs' && surelyPositive(m.args[0].args[0], v)
                ? fn('ln', m.args[0].args[0])
                : undefined,
        ),
    );
    if (G.type === 'add') {
        const kept = G.args.filter((t) => containsVar(t, v));
        if (kept.length && kept.length < G.args.length) G = simp(add(kept));
    }
    return niceForm(G, v, { fnFractions: false });
}

/** A rational function of v in lowest terms as a node (a polynomial when the denominator is a number), else null. */
export function canonicalRational(node, v) {
    const r = ratFunctionOf(node, v);
    if (!r) return null;
    if (r.den.degree < 1) return trySimp(r.num.scale(r.den.coeff(0).inv()).toNode(v));
    return trySimp(div(r.num.toNode(v), r.den.toNode(v)));
}

export function substResult(f, ctx, { t, uNode, g, title, text, rule, dtTex }) {
    const { v } = ctx;
    const g0 = trySimp(g);
    if (!g0) return null;
    // after t = tg(x/2) and the like the fraction comes out nested: −2/(((t²−1)/(t²+1) − 1)(t²+1)) is just 1
    const gs = canonicalRational(g0, t) ?? g0;
    const r = ctx.integrate(gs, { v: t });
    if (!r) return null;
    const F = substitute(r.F, { [t]: uNode });
    return {
        F,
        method: rule,
        step: step({
            title,
            tex: eachLanguage(
                (L) =>
                    `${iTex(f, v, L)} = \\left[${t} = ${tx(uNode, L)},\\ ${dtTex(L)}\\right] = ${iTex(gs, t, L)} = ${tx(trySimp(r.F) ?? r.F, L)} = ${tx(trySimp(F) ?? F, L)}`,
            ),
            text,
            rule,
            sub: [r.step],
        }),
    };
}

const SUP = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹', '-': '⁻' };

export const supDigits = (d) => [...d].map((c) => SUP[c]).join('');

export const qn = (x) => num(x);
