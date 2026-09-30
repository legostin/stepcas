// solve/common — small helpers shared by the solvers: bilingual text, TeX, safe simplification, numbers, trees.

import { toTex } from '../core/print.js';
import { step as mkStep } from '../core/steps.js';
import { num, sym, freeVars, neg, mul, add, fn, nodeKey, mapNode, nodeChildren, containsVar } from '../core/ast.js';
import { Q, bigGcd } from '../core/rational.js';
import { simplify } from '../core/simplify.js';
import { expand, collectTerms } from '../core/expand.js';
import { evaluate } from '../core/evaluate.js';
import { msg, eachLanguage, decimalIn, DEFAULT_LANGUAGE } from '../i18n/index.js';

// ---------------------------------------------------------------- small helpers

export const pick = (x, lang) => (typeof x === 'string' ? x : (x?.[lang] ?? ''));
export const tex = (node, lang = DEFAULT_LANGUAGE, o = {}) => toTex(node, { ...o, lang });
export const texB = (node, o = {}) => eachLanguage((l) => tex(node, l, o));

export function S(title, o = {}) {
    const s = mkStep({ title, tex: o.tex, text: o.text, rule: o.rule, sub: o.sub });
    if (o.final) s.final = true;
    return s;
}

export const N0 = num(0);
export const N1 = num(1);
export const PI = sym('pi');

/** Simplify without throwing (null on failure). */
export function simp(node, opts) {
    try {
        return simplify(node, opts);
    } catch {
        return null;
    }
}

/** Simplify, falling back to the node itself. */
export function simpOr(node, opts) {
    return simp(node, opts) ?? node;
}

/** Expanded canonical form (null on failure). */
export function expd(node, opts) {
    try {
        return expand(node, opts);
    } catch {
        return null;
    }
}

/** Real numeric value (NaN on failure). */
export function approxOf(node, env = {}) {
    try {
        const x = evaluate(node, env);
        return typeof x === 'number' ? x : NaN;
    } catch {
        return NaN;
    }
}

/** Complex value {re, im} (null on failure). */
export function approxC(node, env = {}) {
    try {
        const z = evaluate(node, env, { complex: true });
        return z && Number.isFinite(z.re) && Number.isFinite(z.im) ? { re: z.re, im: z.im } : null;
    } catch {
        return null;
    }
}

/** true / false when a constant expression is exactly zero or not, null when unknown. */
export function exactZero(node, opts) {
    for (const f of [simp, expd]) {
        const s = f(node, opts);
        if (s && s.type === 'num') return s.value.isZero();
    }
    return null;
}

export const close = (a, b, tol = 1e-9) => Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b));

/** Is the node free of letters (a constant, possibly with π, e, √)? */
export const isConstNode = (n) => freeVars(n).length === 0;

/** Round a double to a short decimal node (for approximate roots); it prints as a decimal (2{,}0946), not a fraction. */
export function approxNode(x, digits = 6, decimal = true) {
    if (!Number.isFinite(x) || Math.abs(x) < 1e-12) return num(0);
    const s = Number(x.toPrecision(digits)).toString();
    try {
        return num(Q.of(s), decimal && /^-?\d+\.\d+$/.test(s) ? s : undefined);
    } catch {
        return num(Q.of(Math.round(x * 1e6) / 1e6));
    }
}

/** A short decimal for showing an approximate value inside a substitution: 4 decimals (like approxTex), a real minus. */
export function approxShowNode(x) {
    if (!Number.isFinite(x)) return num(0);
    const a = Math.abs(x);
    const s = a !== 0 && (a < 1e-3 || a >= 1e15) ? Number(a.toPrecision(5)).toString() : Number(a.toFixed(4)).toString();
    const node = /^\d+(\.\d+)?$/.test(s) ? num(Q.of(s), s.includes('.') ? s : undefined) : approxNode(a, 5);
    return x < 0 && !(node.type === 'num' && node.value.isZero()) ? neg(node) : node;
}
export const approxShowComplex = (z) => {
    if (Math.abs(z.im) < 1e-12) return approxShowNode(z.re);
    const im = Math.abs(z.im);
    const imNode = Math.abs(im - 1) < 5e-5 ? sym('i') : mul(approxShowNode(im), sym('i'));
    const imPart = z.im < 0 ? neg(imNode) : imNode;
    return Math.abs(z.re) < 5e-5 ? imPart : add(approxShowNode(z.re), imPart);
};

/** Σ|terms| of a side at the root (the scale for a numeric «= 0»: 735134400x⁵ − x − 735134400 cancels to ~1e-6). */
export function termScale(node, complex) {
    const terms = node.type === 'add' ? node.args : [node];
    let s = 0;
    for (const t of terms) {
        const val = complex ? approxC(t) : approxOf(t);
        const m = complex ? (val ? Math.hypot(val.re, val.im) : NaN) : Math.abs(val);
        if (Number.isFinite(m)) s += m;
    }
    return s;
}

/** Number TeX for approximate values in the language's notation: 1{,}2346 or 1.2346. */
export function approxTex(x, lang, digits = 4) {
    if (!Number.isFinite(x)) return '\\text{—}';
    let s = Number(x.toFixed(digits)).toString();
    if (s === '-0') s = '0';
    if (/e/.test(s)) s = x.toExponential(3);
    return decimalIn(s, lang);
}

export const sq = (n) => fn('sqrt', n);

/** gcd of two rationals: gcd(p₁q₂, p₂q₁)/(q₁q₂). */
export const qGcd = (a, b) => new Q(bigGcd(a.n * b.d, b.n * a.d), a.d * b.d);

/** TeX of a rational in brackets when negative (for substitutions): (-5), \left(-\frac{1}{2}\right). */
export function parQ(q, lang = DEFAULT_LANGUAGE) {
    const t = tex(num(q), lang);
    if (!q.isNeg()) return t;
    return q.isInt() ? `(${t})` : `\\left(${t}\\right)`;
}

// ---------------------------------------------------------------- tree helpers

/** Replace every subtree equal to `target` by `repl`. */
export function replaceNode(node, target, repl) {
    const key = nodeKey(target);
    return mapNode(node, (n) => (nodeKey(n) === key ? repl : undefined));
}

/** Outermost nodes matching pred (not looking inside a match). */
export function outermost(node, pred) {
    const out = [];
    const seen = new Set();
    const walk = (n) => {
        if (pred(n)) {
            const k = nodeKey(n);
            if (!seen.has(k)) {
                seen.add(k);
                out.push(n);
            }
            return;
        }
        for (const c of nodeChildren(n)) walk(c);
    };
    walk(node);
    return out;
}

/** Is the equation already "X = Y" (either way round)? */
export function isolated(lhs, rhs, X, Y) {
    const l = nodeKey(simpOr(lhs));
    const r = nodeKey(simpOr(rhs));
    const x = nodeKey(simpOr(X));
    const y = nodeKey(simpOr(Y));
    return (l === x && r === y) || (l === y && r === x);
}

export const TMP = '__u';

/** E = α·U + β in the placeholder U (α constant ≠ 0) → {alpha, beta} or null. */
export function linearIn(E, name, v) {
    let ct;
    try {
        ct = collectTerms(E, name);
    } catch {
        return null;
    }
    if (!ct || ![...ct.keys()].every((d) => d === 0 || d === 1) || !ct.has(1)) return null;
    const alpha = ct.get(1);
    if (containsVar(alpha, v) || freeVars(alpha).length) return null;
    return { alpha, beta: ct.get(0) ?? N0 };
}

export const orTex = (l) => msg('solve.common.or').in(l);
