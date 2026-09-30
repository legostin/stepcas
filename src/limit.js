// limit — limits with steps in the style of a Russian university course: substitution, «limit
// arithmetic» with infinities, and for indeterminate forms: factor and cancel (rational functions),
// divide by the highest power (x → ±∞), the conjugate for differences of roots, equivalent infinitesimals
// (sin u ~ u, 1 − cos u ~ u²/2, eᵘ − 1 ~ u, ln(1 + u) ~ u, (1 + u)ᵃ − 1 ~ au, …), the second remarkable
// limit for 1^∞, e^(lim v·ln u) for 0⁰ and ∞⁰, and L'Hôpital's rule (at most 5 rounds, only for 0/0 and ∞/∞).
// Every answer comes with a table of values approaching the point and is cross-checked against it; when
// the symbolic methods fail, the numeric estimate is returned and clearly marked ≈.
// Also: taylorPolynomial (exact coefficients f⁽ᵏ⁾(a)/k!) and taylorRemainderBound (Lagrange form, numeric M).

import { Q, MathError } from './rational.js';
import { num, sym, add, mul, div, neg, pow, fn, isConst, containsVar, freeVars, nodeKey, substitute, toNode, nodeChildren, mapNode } from './ast.js';
import { parse } from './parse.js';
import { simplify, canonContext, splitCoeff } from './simplify.js';
import { expand, combineFractions } from './expand.js';
import { evaluate } from './evaluate.js';
import { toText } from './print.js';
import { step } from './steps.js';
import { quickDerivative, niceForm, prettyForm, calcTex, ratFunctionOf } from './diff.js';
import { Poly } from './poly.js';

const N0 = num(0);
const N1 = num(1);
const NM1 = num(-1);
const N2 = num(2);
const HALF = num(Q.HALF);
const INF = sym('inf');
const E_ = sym('e');
const PI = sym('pi');

const isNum = (n) => n.type === 'num';
const qn2 = (q) => num(q);
const isZeroN = (n) => isNum(n) && n.value.isZero();
const T_ = (ru, en) => ({ ru, en });

function asNode(x) {
    if (x && typeof x === 'object' && typeof x.type === 'string') return x;
    if (typeof x === 'string') return parse(x);
    if (x === Infinity) return INF;
    if (x === -Infinity) return neg(INF);
    return toNode(x);
}

function simp(n) {
    let s = simplify(n);
    for (let i = 0; i < 3; i++) {
        const t = simplify(s);
        if (nodeKey(t) === nodeKey(s)) break;
        s = t;
    }
    return s;
}

function trySimp(n) {
    try {
        return simp(n);
    } catch {
        return null;
    }
}

function bt(f) {
    const ru = f('ru');
    const en = f('en');
    return ru === en ? ru : { ru, en };
}

const tx = (n, L) => calcTex(n, L);
const tall = (s) => /\\frac|\\sqrt|\\left|\^\{/.test(s);
const paren = (s) => (tall(s) ? `\\left(${s}\\right)` : `(${s})`);
const paren2 = (s, n) => (n.type === 'add' ? paren(s) : s);
/** "a = b = c" without repeating equal neighbours. */
const chainEq = (parts) => parts.filter((x, i, a) => x && (i === 0 || x !== a[i - 1])).join(' = ');
/** An expression after \lim: a sum goes in brackets. */
const lt = (n, L) => (n.type === 'add' ? paren(tx(n, L)) : tx(n, L));

// ---------------------------------------------------------------- the point

/** {a: node | null, x: number (±Infinity for ∞), side: 'left' | 'right' | 'both'} */
function makePoint(aNode, side) {
    const s = trySimp(aNode) ?? aNode;
    if (isConst(s) && s.name === 'inf') return { a: null, x: Infinity, side: 'left' };
    if (s.type === 'mul' && s.args.length === 2 && isNum(s.args[0]) && s.args[0].value.isNeg() && isConst(s.args[1]) && s.args[1].name === 'inf') return { a: null, x: -Infinity, side: 'right' };
    const x = evaluate(s);
    if (!Number.isFinite(x)) throw new MathError({ ru: 'Точка должна быть числом или ±∞', en: 'The point must be a number or ±∞' }, null, null, 'range');
    return { a: s, x, side };
}

function atPoint(P, h) {
    if (P.x === Infinity) return 1 / h;
    if (P.x === -Infinity) return -1 / h;
    const scale = Math.max(1, Math.abs(P.x));
    return P.side === 'left' ? P.x - h * scale : P.x + h * scale;
}

function arrowTex(P, v, L) {
    void L;
    if (P.x === Infinity) return `${v} \\to +\\infty`;
    if (P.x === -Infinity) return `${v} \\to -\\infty`;
    const a = tx(P.a, L);
    const sup = P.side === 'left' ? '^{-}' : P.side === 'right' ? '^{+}' : '';
    return `${v} \\to ${sup ? `{${a}}${sup}` : a}`;
}

const limTex = (P, v, L) => `\\lim_{${arrowTex(P, v, L)}}`;

function safeEval(n) {
    try {
        const y = evaluate(n);
        return typeof y === 'number' ? y : NaN;
    } catch {
        return NaN;
    }
}

function evalAt(n, v, x) {
    try {
        const y = evaluate(n, { [v]: x });
        return typeof y === 'number' ? y : NaN;
    } catch {
        return NaN;
    }
}

const HS = [1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8];

/** Sign of n near the point: +1 / −1, 0 when it keeps changing, NaN when undefined. */
function signNear(n, v, P) {
    const signs = new Set();
    let any = false;
    for (const h of Number.isFinite(P.x) ? [1e-4, 1e-6, 1e-8] : [1e-1, 1e-2, 1e-3]) {
        const y = evalAt(n, v, atPoint(P, h));
        if (!Number.isFinite(y) && !(Math.abs(y) === Infinity)) continue;
        if (y === 0) continue;
        any = true;
        signs.add(Math.sign(y));
    }
    if (!any) return NaN;
    return signs.size === 1 ? [...signs][0] : 0;
}

class Split extends Error {}

const negLeadNode = (n) => (isNum(n) && n.value.isNeg()) || n.type === 'neg' || (n.type === 'mul' && isNum(n.args[0]) && n.args[0].value.isNeg());

function negLead(n) {
    if (isNum(n)) return n.value.isNeg();
    if (n.type === 'neg') return true;
    if (n.type === 'mul') return n.args.length > 0 && negLead(n.args[0]);
    return false;
}

/** The sign near the point; for a two-sided limit whose sides differ: 'split'. */
function sideSign(n, v, P) {
    if (P.side !== 'both' || !Number.isFinite(P.x)) return signNear(n, v, P);
    const l = signNear(n, v, { ...P, side: 'left' });
    const r = signNear(n, v, { ...P, side: 'right' });
    if (Number.isNaN(l)) return r;
    if (Number.isNaN(r)) return l;
    if (l !== r) return 'split';
    return l;
}

/** The sign or throw Split (when the answer really depends on the side). */
function sideSignStrict(n, v, P) {
    const s = sideSign(n, v, P);
    if (s === 'split') throw new Split();
    return s;
}

/** An infinity of a known sign, or throw Split for ∞ of varying sign where the sign matters. */
function needSign(L) {
    if (L.k === 'inf' && L.s === 0) throw new Split();
    return L;
}

// ---------------------------------------------------------------- limit values

const fin = (node) => {
    const s = trySimp(node) ?? node;
    let x;
    try {
        x = evaluate(s);
    } catch {
        x = NaN;
    }
    return { k: 'fin', node: s, x };
};
const infV = (s) => ({ k: 'inf', s });
const BND = { k: 'bnd' };
const DNE = { k: 'dne' };

const isZeroV = (L) => L && L.k === 'fin' && (isZeroN(L.node) || (Number.isFinite(L.x) && Math.abs(L.x) < 1e-15 && isZeroN(trySimp(L.node) ?? L.node)));
const isOneV = (L) => L && L.k === 'fin' && isNum(L.node) && L.node.value.isOne();

// ---------------------------------------------------------------- the evaluator

/**
 * Limit of n at the point C.P → LV ({k: 'fin', node, x} | {k: 'inf', s} | BND | DNE) or null.
 * Indeterminate combinations are handed to resolve(), which records its steps in C.log.
 */
function ev(n, C) {
    const { v, P } = C;
    if (++C.work.n > 4000) return null;
    if (!containsVar(n, v)) {
        const f = fin(n);
        return Number.isFinite(f.x) || freeVars(n).length ? f : null;
    }
    switch (n.type) {
        case 'sym':
            return P.a ? fin(P.a) : infV(P.x > 0 ? 1 : -1);
        case 'add':
            return evAdd(n, C);
        case 'mul':
            return evMul(n, C);
        case 'div':
            return evQuot(n, n.num, n.den, C);
        case 'neg': {
            const a = ev(n.arg, C);
            if (!a) return null;
            if (a.k === 'fin') return fin(neg(a.node));
            if (a.k === 'inf') return infV(-a.s);
            return a;
        }
        case 'pow':
            return evPow(n, C);
        case 'fn':
            return evFn(n, C);
        default:
            return null;
    }
}

function evAdd(n, C) {
    const vals = [];
    for (const t of n.args) {
        const L = ev(t, C);
        if (!L) return null;
        vals.push(L);
    }
    const infs = vals.filter((x) => x.k === 'inf');
    if (vals.some((x) => x.k === 'dne')) return infs.length ? null : DNE;
    const pos = infs.some((x) => x.s > 0);
    const negI = infs.some((x) => x.s < 0);
    const uns = infs.some((x) => x.s === 0);
    if (pos && negI && n !== C.root && !Number.isFinite(C.P.x)) {
        // a sum inside a bigger expression: its leading term decides quietly (x² − x → +∞)
        const t = C.P.x < 0 ? trySimp(substitute(n, { [C.v]: neg(sym(C.v)) })) : n;
        const a = t && asym(t, C.v);
        if (a && a.p.isPos() && a.c !== 0) return infV(Math.sign(a.c));
    }
    if ((pos && negI) || (uns && infs.length > 1)) return resolve(n, C, 'inf-inf');
    if (infs.length) return infV(uns ? 0 : pos ? 1 : -1);
    if (vals.some((x) => x.k === 'bnd')) return BND;
    return fin(add(vals.map((x) => x.node)));
}

function splitNumDen(n) {
    // canonical product → numerator factors, denominator factors (positive powers)
    const S = n.type === 'mul' ? n.args : [n];
    const top = [];
    const bot = [];
    for (const f of S) {
        if (f.type === 'pow' && isNum(f.exp) && f.exp.value.isNeg()) bot.push(f.exp.value.eq(-1) ? f.base : pow(f.base, num(f.exp.value.neg())));
        else if (f.type === 'pow' && !isNum(f.exp) && negLead(f.exp)) bot.push(pow(f.base, trySimp(neg(f.exp)) ?? neg(f.exp)));
        else top.push(f);
    }
    return { top, bot };
}

function evMul(n, C) {
    const { v } = C;
    const { top, bot } = splitNumDen(n);
    if (bot.some((f) => containsVar(f, v))) {
        const u = top.length ? (top.length === 1 ? top[0] : mul(top)) : N1;
        const w = bot.length === 1 ? bot[0] : mul(bot);
        return evQuot(n, u, w, C);
    }
    const vals = [];
    for (const f of n.args) {
        const L = ev(f, C);
        if (!L) return null;
        vals.push(L);
    }
    return combineProduct(n, vals, C);
}

function combineProduct(n, vals, C) {
    const zeros = vals.filter(isZeroV);
    const infs = vals.filter((x) => x.k === 'inf');
    const bnds = vals.filter((x) => x.k === 'bnd');
    if (vals.some((x) => x.k === 'dne')) return DNE;
    if (zeros.length && infs.length) return resolve(n, C, '0*inf');
    if (zeros.length) return fin(N0); // bounded × infinitesimal → 0 as well
    if (infs.length && bnds.length) return null;
    if (infs.length) {
        let s = 1;
        for (const x of vals) {
            if (x.k === 'inf') s *= x.s;
            else if (x.k === 'fin') {
                if (!Number.isFinite(x.x)) return null;
                s *= Math.sign(x.x);
            }
        }
        return infV(s);
    }
    if (bnds.length) return BND;
    return fin(mul(vals.map((x) => x.node)));
}

function evQuot(n, u, w, C) {
    const U = ev(u, C);
    const W = ev(w, C);
    if (!U || !W) return null;
    if (U.k === 'dne' || W.k === 'dne') return null;
    const uz = isZeroV(U);
    const wz = isZeroV(W);
    if (uz && wz) return resolve(n, C, '0/0');
    if (U.k === 'inf' && W.k === 'inf') return resolve(n, C, 'inf/inf');
    if (W.k === 'inf') return U.k === 'bnd' || U.k === 'fin' ? fin(N0) : null;
    if (W.k === 'bnd') return null;
    if (wz) {
        if (U.k === 'bnd') return null;
        const s = sideSign(w, C.v, C.P);
        if (s === 'split') return infV(0);
        if (!s || Number.isNaN(s)) return null;
        const su = U.k === 'inf' ? U.s : Math.sign(U.x);
        if (U.k !== 'inf' && !su) return null;
        return infV(su * s);
    }
    if (U.k === 'inf') return infV(U.s * Math.sign(W.x));
    if (U.k === 'bnd') return BND;
    return fin(div(U.node, W.node));
}

function evPow(n, C) {
    const { v } = C;
    const b = n.base;
    const e = n.exp;
    if (!containsVar(e, v)) {
        const r = trySimp(e);
        const rq = r && isNum(r) ? r.value : null;
        if (rq && rq.isNeg()) return evQuot(n, N1, rq.eq(-1) ? b : pow(b, num(rq.neg())), C);
        const B = ev(b, C);
        if (!B) return null;
        if (B.k === 'fin') {
            if (isZeroV(B)) {
                if (rq && rq.isPos()) return fin(N0);
                return null;
            }
            if (B.x < 0 && rq && !rq.isInt() && rq.d % 2n === 0n) return null;
            return fin(pow(B.node, e));
        }
        if (B.k === 'inf') {
            const ex = safeEval(r ?? e);
            if (!(ex > 0)) return ex < 0 ? fin(N0) : null;
            if (rq && rq.isInt() && rq.n % 2n === 0n) return infV(1);
            needSign(B);
            if (B.s > 0) return infV(1);
            if (rq && rq.isInt()) return infV(rq.n % 2n === 0n ? 1 : -1);
            if (rq && rq.d % 2n === 1n) return infV(rq.n % 2n === 0n ? 1 : -1);
            return null;
        }
        if (B.k === 'bnd') return rq && rq.isPos() ? BND : null;
        return null;
    }
    const Ex = ev(e, C);
    if (!Ex) return null;
    if (!containsVar(b, v)) {
        const bx = safeEval(b);
        if (Ex.k === 'fin') return fin(pow(b, Ex.node));
        if (!(bx > 0)) return null;
        if (Ex.k === 'inf') {
            if (bx === 1) return fin(N1);
            needSign(Ex);
            return (bx > 1) === (Ex.s > 0) ? infV(1) : fin(N0);
        }
        return Ex.k === 'bnd' ? BND : null;
    }
    const B = ev(b, C);
    if (!B) return null;
    if (B.k === 'fin' && isOneV(B) && Ex.k === 'inf') return resolve(n, C, '1^inf');
    if (B.k === 'fin' && isZeroV(B) && isZeroV(Ex)) return resolve(n, C, '0^0');
    if (B.k === 'inf' && isZeroV(Ex)) return resolve(n, C, 'inf^0');
    if (B.k === 'fin' && B.x > 0 && Ex.k === 'fin') return fin(pow(B.node, Ex.node));
    if (B.k === 'fin' && isZeroV(B) && Ex.k === 'inf') return needSign(Ex).s > 0 ? fin(N0) : infV(1);
    if (B.k === 'fin' && B.x > 0 && Ex.k === 'inf') {
        if (B.x === 1) return resolve(n, C, '1^inf');
        return (B.x > 1) === (needSign(Ex).s > 0) ? infV(1) : fin(N0);
    }
    if (B.k === 'inf' && B.s > 0 && Ex.k === 'inf') return needSign(Ex).s > 0 ? infV(1) : fin(N0);
    if (B.k === 'inf' && B.s > 0 && Ex.k === 'fin') return Ex.x > 0 ? infV(1) : Ex.x < 0 ? fin(N0) : null;
    return null;
}

const CONT = new Set(['sin', 'cos', 'atan', 'acot', 'sinh', 'cosh', 'tanh', 'asinh', 'exp', 'abs']);

function evFn(n, C) {
    const { v, P } = C;
    const name = n.name;
    if (name === 'log') {
        const base = n.args[0];
        if (containsVar(base, v)) return ev(simp(div(fn('ln', n.args[1]), fn('ln', base))), C);
        const L = ev(fn('ln', n.args[1]), C);
        if (!L) return null;
        if (L.k === 'fin') return fin(div(L.node, fn('ln', base)));
        if (L.k === 'inf') {
            const lb = Math.log(safeEval(base));
            return Number.isFinite(lb) && lb !== 0 ? infV(L.s * Math.sign(lb)) : null;
        }
        return null;
    }
    if (name === 'root') {
        const k = trySimp(n.args[1]);
        if (!k || !isNum(k)) return null;
        return evPow(pow(n.args[0], num(k.value.inv())), C);
    }
    const U = ev(n.args[0], C);
    if (!U) return null;
    if (U.k === 'dne') return null;
    if (U.k === 'bnd') return ['sin', 'cos', 'atan', 'acot', 'tanh', 'abs', 'sign'].includes(name) ? BND : null;
    if (U.k === 'inf') {
        if (U.s === 0 && !['sin', 'cos', 'abs', 'cosh', 'tan', 'cot'].includes(name)) needSign(U);
        const s = U.s;
        switch (name) {
            case 'sin':
            case 'cos':
                return BND;
            case 'atan':
                return fin(mul(num(new Q(BigInt(s), 2n)), PI));
            case 'acot':
                return s > 0 ? fin(N0) : fin(PI);
            case 'tanh':
                return fin(num(s));
            case 'sign':
                return fin(num(s));
            case 'exp':
                return s > 0 ? infV(1) : fin(N0);
            case 'ln':
            case 'lg':
            case 'sqrt':
                return s > 0 ? infV(1) : null;
            case 'abs':
            case 'cosh':
                return infV(1);
            case 'sinh':
            case 'asinh':
                return infV(s);
            case 'acosh':
                return s > 0 ? infV(1) : null;
            case 'coth':
                return fin(num(s));
            default:
                return name === 'tan' || name === 'cot' ? DNE : null;
        }
    }
    // finite argument
    const ux = U.x;
    const u0 = U.node;
    const approachSign = () => sideSignStrict(add(n.args[0], neg(u0)), v, P);
    switch (name) {
        case 'ln':
        case 'lg':
        case 'sqrt': {
            if (ux > 0) return fin(fn(name, u0));
            if (isZeroV(U)) {
                if (name === 'sqrt') return fin(N0);
                const s = sideSignStrict(n.args[0], v, P);
                return s > 0 ? infV(-1) : null;
            }
            return null;
        }
        case 'tan':
        case 'cot':
        case 'sec':
        case 'csc': {
            const test = name === 'tan' || name === 'sec' ? Math.cos(ux) : Math.sin(ux);
            if (Math.abs(test) > 1e-12) return fin(fn(name, u0));
            const s = sideSign(n, v, P);
            if (s === 'split') return infV(0);
            if (!s || Number.isNaN(s)) return null;
            return infV(s);
        }
        case 'asin':
        case 'acos':
            return Math.abs(ux) <= 1 ? fin(fn(name, u0)) : null;
        case 'acosh':
            return ux >= 1 ? fin(fn(name, u0)) : null;
        case 'atanh':
            if (Math.abs(ux) < 1) return fin(fn(name, u0));
            if (Math.abs(ux) === 1) return infV(Math.sign(ux));
            return null;
        case 'coth':
            if (isZeroV(U)) {
                const s = sideSign(n.args[0], v, P);
                if (s === 'split') return infV(0);
                return s ? infV(s) : null;
            }
            return fin(fn(name, u0));
        case 'sign': {
            if (!isZeroV(U)) return fin(num(Math.sign(ux)));
            const s = approachSign();
            return s ? fin(num(s)) : null;
        }
        case 'floor':
        case 'ceil': {
            if (Math.abs(ux - Math.round(ux)) > 1e-12) return fin(fn(name, u0));
            const s = approachSign();
            if (!s) return fin(fn(name, u0));
            const k = Math.round(ux);
            return fin(num(name === 'floor' ? (s > 0 ? k : k - 1) : s > 0 ? k + 1 : k));
        }
        case 'fact':
            return null;
        default:
            if (CONT.has(name)) return fin(fn(name, u0));
            return null;
    }
}

// ---------------------------------------------------------------- indeterminate forms

const FORM_TEX = { '0/0': '\\frac{0}{0}', 'inf/inf': '\\frac{\\infty}{\\infty}', 'inf-inf': '\\infty - \\infty', '0*inf': '0 \\cdot \\infty', '1^inf': '1^{\\infty}', '0^0': '0^{0}', 'inf^0': '\\infty^{0}' };
const FORM_NAME = { '0/0': '0/0', 'inf/inf': '∞/∞', 'inf-inf': '∞ − ∞', '0*inf': '0·∞', '1^inf': '1^∞', '0^0': '0⁰', 'inf^0': '∞⁰' };

function vTex(L, Lg) {
    if (!L) return '?';
    if (L.k === 'fin') return tx(prettyForm(L.node), Lg);
    if (L.k === 'inf') return L.s > 0 ? '+\\infty' : '-\\infty';
    return Lg === 'ru' ? '\\text{не существует}' : '\\text{does not exist}';
}

function resolve(n, C, form) {
    if (C.depth > 8) return null;
    const key = nodeKey(n) + '|' + form;
    if (C.active.has(key)) return null;
    C.active.add(key);
    const C2 = { ...C, depth: C.depth + 1, log: [] };
    let res = null;
    try {
        for (const m of METHODS[form] ?? []) {
            C2.log = [];
            const r = m(n, C2, form);
            if (r && r.val) {
                res = r;
                break;
            }
        }
    } finally {
        C.active.delete(key);
    }
    if (!res) return null;
    C.log.push(step({
        title: res.title,
        tex: res.tex,
        text: res.text,
        rule: res.rule,
        sub: [...(res.sub ?? []), ...C2.log],
    }));
    C.methods.add(res.rule);
    return res.val;
}

function limSub(n, C) {
    // the limit of a transformed expression; its own steps go into C.log
    return ev(n, C);
}

// ---- rational functions

function mRational(n, C, form) {
    const { v, P } = C;
    const r = ratFunctionOf(n, v);
    if (!r) return null;
    if (!Number.isFinite(P.x)) {
        // degree comparison
        const p = r.num;
        const q = r.den;
        const dp = p.degree;
        const dq = q.degree;
        let val;
        if (dp < dq) val = fin(N0);
        else if (dp === dq) val = fin(num(p.lead.div(q.lead)));
        else {
            let s = Math.sign(p.lead.div(q.lead).toNumber());
            if (P.x < 0 && (dp - dq) % 2 === 1) s = -s;
            val = infV(s);
        }
        const k = Math.max(dq, dp > dq ? dq : dp);
        const X = sym(v);
        if (dq === 0 && dp >= 1) {
            // a polynomial: the leading term decides — take x^deg out of the brackets
            const inner = simp(expand(div(p.toNode(v), mul(qn2(q.lead), pow(X, num(dp))))));
            const lead = simp(mul(qn2(p.lead.div(q.lead)), pow(X, num(dp))));
            return {
                val,
                title: T_('Выносим старшую степень', 'Take out the highest power'),
                tex: bt((L) => `${limTex(P, v, L)} ${lt(n, L)} = ${limTex(P, v, L)} ${dp === 1 && p.lead.div(q.lead).isOne() ? tx(X, L) : lt(lead, L)}${inner.type === 'add' ? paren(tx(inner, L)) : ''} = ${vTex(val, L)}`.replace(/\\cdot\s*$/, '')),
                text: T_(`Многочлен при ${v} → ${P.x > 0 ? '+∞' : '−∞'} ведёт себя как его старший член: выносим ${v}${supd(dp)} за скобки, в скобках все слагаемые, кроме первого, стремятся к нулю.`,
                    `As ${v} → ${P.x > 0 ? '+∞' : '−∞'} a polynomial behaves like its leading term: take ${v}${supd(dp)} out of the brackets; inside, every term but the first tends to zero.`),
                rule: 'leading-power',
            };
        }
        return {
            val,
            title: form === 'inf-inf' ? T_('Приводим к общему знаменателю', 'Common denominator') : T_('Делим на старшую степень', 'Divide by the highest power'),
            tex: bt((L) => chainEq([`${limTex(P, v, L)} ${lt(n, L)}`, `${limTex(P, v, L)} ${lt(q.degree > 0 ? div(p.toNode(v), q.toNode(v)) : p.toNode(v), L)}`, k > 0 ? `${limTex(P, v, L)} \\frac{${tx(dividedBy(p, k, v), L)}}{${tx(dividedBy(q, k, v), L)}}` : null, vTex(val, L)])),
            text: dp < dq
                ? T_(`Степень числителя (${dp}) меньше степени знаменателя (${dq}): делим числитель и знаменатель на ${v}${supd(k)}, все слагаемые вида c/${v}ᵐ стремятся к нулю, и предел равен 0.`, `The numerator's degree (${dp}) is less than the denominator's (${dq}): divide both by ${v}${supd(k)}; every term c/${v}ᵐ tends to zero, so the limit is 0.`)
                : dp === dq
                    ? T_(`Степени числителя и знаменателя равны (${dp}): делим оба на ${v}${supd(k)}, и остаётся отношение старших коэффициентов.`, `The degrees are equal (${dp}): divide both by ${v}${supd(k)}; what remains is the ratio of the leading coefficients.`)
                    : T_(`Степень числителя (${dp}) больше степени знаменателя (${dq}), поэтому дробь растёт неограниченно; знак определяют старшие коэффициенты.`, `The numerator's degree (${dp}) exceeds the denominator's (${dq}), so the fraction grows without bound; the leading coefficients fix the sign.`),
            rule: 'rational-infinity',
        };
    }
    // finite point: factor and cancel
    const nd = combineFractionsSafe(n);
    const Pn = nd ? Poly.fromNode(nd.num, v) : null;
    const Pd = nd ? Poly.fromNode(nd.den, v) : null;
    const reduced = r.den.degree < 1 ? simp(div(r.num.toNode(v), r.den.toNode(v))) : div(r.num.toNode(v), r.den.toNode(v));
    const L = ev(simp(reduced), { ...C, depth: C.depth + 1 });
    if (!L) return null;
    const showFactor = Pn && Pd && Pd.degree >= 1;
    const fN = showFactor ? factorTex(Pn, v) : null;
    const fD = showFactor ? factorTex(Pd, v) : null;
    return {
        val: L,
        title: T_('Раскладываем на множители и сокращаем', 'Factor and cancel'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)}${showFactor ? ` = ${limTex(P, v, Lg)} \\frac{${fN(Lg)}}{${fD(Lg)}}` : ''} = ${limTex(P, v, Lg)} ${lt(reduced, Lg)} = ${vTex(L, Lg)}`),
        text: T_(`Числитель и знаменатель обращаются в ноль при ${v} = ${plainNum(P)}, значит, у обоих есть множитель (${v} − ${plainNum(P)}). Раскладываем их на множители, сокращаем этот общий множитель — он не равен нулю, пока ${v} ≠ ${plainNum(P)}, — и после этого подставляем.`,
            `Both the numerator and the denominator vanish at ${v} = ${plainNum(P)}, so both have the factor (${v} − ${plainNum(P)}). Factor them, cancel the common factor (it is nonzero while ${v} ≠ ${plainNum(P)}), and then substitute.`),
        rule: 'factor-cancel',
    };
}

/** P(x)/x^k written from the highest power down, unsimplified: 1 − 4/x + 6/x² … */
function dividedBy(Pl, k, v) {
    const X = sym(v);
    const terms = [];
    for (let i = Pl.degree; i >= 0; i--) {
        const c = Pl.coeff(i);
        if (c.isZero()) continue;
        const e = i - k;
        const pw = e === 0 ? null : e === 1 ? X : pow(X, num(e));
        if (!pw) terms.push(num(c));
        else if (c.isOne()) terms.push(pw);
        else terms.push(mul(num(c), pw));
    }
    if (!terms.length) return N0;
    return terms.length === 1 ? terms[0] : add(terms);
}

function supd(k) {
    const S = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹' };
    return k === 1 ? '' : String(k).split('').map((c) => S[c]).join('');
}

function plainNum(P) {
    try {
        return toText(prettyForm(P.a), { lang: 'en' }).replace(/\bpi\b/g, 'π').replace(/sqrt\(/g, '√(').replace(/\*/g, '·');
    } catch {
        return String(P.x);
    }
}

function combineFractionsSafe(n) {
    try {
        const c = combineFractions(n, { cancel: false });
        return c.type === 'div' ? { num: c.num, den: c.den } : { num: c, den: N1 };
    } catch {
        return null;
    }
}

function factorTex(Pl, v) {
    const { constant, factors } = Pl.factor();
    const fs = [];
    if (!constant.isOne()) fs.push(num(constant));
    for (const { poly, mult } of factors) fs.push(mult === 1 ? poly.toNode(v) : pow(poly.toNode(v), num(mult)));
    const node = fs.length === 0 ? num(constant) : fs.length === 1 ? fs[0] : mul(fs);
    return (L) => calcTex(node, L);
}

// ---- equivalent infinitesimals

const EQUIV_FN = new Set(['sin', 'tan', 'asin', 'atan', 'sinh', 'tanh', 'asinh', 'atanh']);
const FN_RU = { sin: 'sin', tan: 'tg', asin: 'arcsin', atan: 'arctg', sinh: 'sh', tanh: 'th', asinh: 'arsh', atanh: 'arth' };
const FN_EN = { sin: 'sin', tan: 'tan', asin: 'arcsin', atan: 'arctan', sinh: 'sinh', tanh: 'tanh', asinh: 'arsinh', atanh: 'artanh' };

function tendsTo(n, target, C) {
    const L = ev(n, { ...C, log: [], depth: C.depth + 1 });
    if (!L || L.k !== 'fin') return false;
    const d = trySimp(add(L.node, neg(target)));
    return d !== null && isZeroN(d);
}

/** Equivalent of an infinitesimal factor F: {E, ru, en} or null. */
function equivalentOf(F, C) {
    if (F.type === 'fn' && EQUIV_FN.has(F.name) && tendsTo(F.args[0], N0, C)) {
        return { E: F.args[0], ru: `${FN_RU[F.name]} u ~ u`, en: `${FN_EN[F.name]} u ~ u` };
    }
    if (F.type === 'fn' && (F.name === 'ln' || F.name === 'lg') && tendsTo(F.args[0], N1, C)) {
        const E = add(F.args[0], NM1);
        return F.name === 'ln' ? { E, ru: 'ln(1 + u) ~ u', en: 'ln(1 + u) ~ u' } : { E: div(E, fn('ln', num(10))), ru: 'lg(1 + u) ~ u/ln 10', en: 'log₁₀(1 + u) ~ u/ln 10' };
    }
    if (F.type === 'fn' && F.name === 'log' && tendsTo(F.args[1], N1, C)) return { E: div(add(F.args[1], NM1), fn('ln', F.args[0])), ru: 'logₐ(1 + u) ~ u/ln a', en: 'logₐ(1 + u) ~ u/ln a' };
    if (F.type === 'add' && F.args.length === 2) {
        const kIdx = F.args.findIndex((t) => isNum(t));
        if (kIdx < 0) return null;
        const k = F.args[kIdx].value;
        const t1 = F.args[1 - kIdx];
        // F = t1 + k = −k·(Y − 1) with Y = t1/(−k)
        const Y = trySimp(div(t1, num(k.neg())));
        if (!Y) return null;
        const outer = num(k.neg());
        const wrap = (E, ru, en) => ({ E: k.eq(-1) ? E : mul(outer, E), ru, en });
        if (Y.type === 'pow' && !containsVar(Y.base, C.v) && tendsTo(Y.exp, N0, C)) {
            const isE = isConst(Y.base) && Y.base.name === 'e';
            return wrap(isE ? Y.exp : mul(Y.exp, fn('ln', Y.base)), isE ? 'eᵘ − 1 ~ u' : 'aᵘ − 1 ~ u·ln a', isE ? 'eᵘ − 1 ~ u' : 'aᵘ − 1 ~ u·ln a');
        }
        if (Y.type === 'fn' && Y.name === 'cos' && tendsTo(Y.args[0], N0, C)) {
            return wrap(neg(div(pow(Y.args[0], N2), N2)), '1 − cos u ~ u²/2', '1 − cos u ~ u²/2');
        }
        if (Y.type === 'pow' && isNum(Y.exp) && tendsTo(Y.base, N1, C)) {
            return wrap(mul(Y.exp, add(Y.base, NM1)), '(1 + u)ᵃ − 1 ~ a·u', '(1 + u)ᵃ − 1 ~ a·u');
        }
        if (Y.type === 'fn' && Y.name === 'cosh' && tendsTo(Y.args[0], N0, C)) {
            return wrap(div(pow(Y.args[0], N2), N2), 'ch u − 1 ~ u²/2', 'cosh u − 1 ~ u²/2');
        }
    }
    return null;
}

function mEquivalents(n, C) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S) return null;
    const { coef, rest } = splitCoeff(S);
    if (!rest) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    const used = [];
    const out = [num(coef)];
    let changed = false;
    for (const f of fs) {
        const base = f.type === 'pow' && isNum(f.exp) ? f.base : f;
        const e = f.type === 'pow' && isNum(f.exp) ? f.exp : null;
        if (!containsVar(base, v)) {
            out.push(f);
            continue;
        }
        const eq = tendsTo(base, N0, C) ? equivalentOf(base, C) : null;
        if (!eq) {
            out.push(f);
            continue;
        }
        changed = true;
        used.push({ from: base, to: trySimp(eq.E) ?? eq.E, ru: eq.ru, en: eq.en });
        out.push(e ? pow(eq.E, e) : eq.E);
    }
    if (!changed) return null;
    const next = trySimp(mul(out));
    if (!next) return null;
    const C2 = { ...C, depth: C.depth + 1 };
    const L = limSub(next, C2);
    if (!L) return null;
    const laws = [...new Set(used.map((u) => u.ru))];
    const lawsEn = [...new Set(used.map((u) => u.en))];
    return {
        val: L,
        title: T_('Эквивалентные бесконечно малые', 'Equivalent infinitesimals'),
        tex: bt((Lg) => `${used.map((u) => `${tx(u.from, Lg)} \\sim ${tx(u.to, Lg)}`).join(',\\quad ')};\\qquad ${limTex(P, v, Lg)} ${lt(n, Lg)} = ${containsVar(next, v) ? `${limTex(P, v, Lg)} ${paren2(tx(next, Lg), next)} = ` : ''}${vTex(L, Lg)}`),
        text: T_(`Бесконечно малые множители заменяем эквивалентными (${laws.join('; ')}, где u → 0). В произведении и частном такая замена не меняет предела.`,
            `Replace the infinitesimal factors by equivalent ones (${lawsEn.join('; ')}, where u → 0). In a product or a quotient this does not change the limit.`),
        rule: 'equivalents',
    };
}

// ---- conjugate

function rootDeg(t) {
    const { rest } = splitCoeff(t);
    const b = rest ?? t;
    if (b.type === 'pow' && isNum(b.exp) && b.exp.value.n === 1n && (b.exp.value.d === 2n || b.exp.value.d === 3n)) return Number(b.exp.value.d);
    return 0;
}
const isRoot = (t) => rootDeg(t) > 0;

function mConjugate(n, C) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S) return null;
    // find a two-term sum with a square root: the whole expression or a factor (possibly in the denominator)
    const fs = S.type === 'mul' ? S.args : [S];
    for (let i = 0; i < fs.length; i++) {
        const f = fs[i];
        const base = f.type === 'pow' && isNum(f.exp) && f.exp.value.isInt() ? f.base : f;
        const e = base === f ? Q.ONE : f.exp.value;
        if (base.type !== 'add' || base.args.length !== 2 || !base.args.some(isRoot)) continue;
        if (!e.abs().isOne()) continue;
        const [A, B] = base.args;
        const cube = base.args.some((t) => rootDeg(t) === 3);
        // a + b = (a² − b²)/(a − b);  for cube roots a + b = (a³ + b³)/(a² − ab + b²)
        const conj0 = cube ? add(pow(A, N2), neg(mul(A, B)), pow(B, N2)) : add(A, neg(B));
        const conj = trySimp(conj0) ?? conj0;
        const numer = trySimp(expand(cube ? add(pow(A, num(3)), pow(B, num(3))) : add(pow(A, N2), neg(pow(B, N2)))));
        if (!numer) continue;
        const replaced = e.isOne() ? div(numer, conj) : div(conj, numer);
        const next = trySimp(mul([...fs.slice(0, i), replaced, ...fs.slice(i + 1)]));
        if (!next) continue;
        const L = limSub(next, { ...C, depth: C.depth + 1 });
        if (!L) continue;
        return {
            val: L,
            title: T_('Умножаем на сопряжённое', 'Multiply by the conjugate'),
            tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} \\frac{${paren(tx(base, Lg))}${paren(tx(conj, Lg))}}{${tx(conj, Lg)}}${e.isOne() ? '' : '^{-1}'} = ${limTex(P, v, Lg)} ${lt(next, Lg)} = ${vTex(L, Lg)}`),
            text: cube
                ? T_('Разность кубических корней даёт неопределённость. Домножаем до разности кубов: (a − b)(a² + ab + b²) = a³ − b³, и корни уходят из этого множителя.',
                    'The difference of cube roots is indeterminate. Complete it to a difference of cubes: (a − b)(a² + ab + b²) = a³ − b³, which removes the roots from this factor.')
                : T_('Разность с корнем даёт неопределённость. Умножаем и делим на сопряжённое выражение: (a − b)(a + b) = a² − b², и корень уходит из этого множителя.',
                    'The difference with a root is indeterminate. Multiply and divide by the conjugate: (a − b)(a + b) = a² − b², which removes the root from this factor.'),
            rule: 'conjugate',
        };
    }
    return null;
}

// ---- leading terms at ±∞ (algebraic expressions)

/** n ~ c·t^p as t → +∞ (t is the variable): {c: number, p: Q} or null. */
function asym(n, v) {
    switch (n.type) {
        case 'num':
            return n.value.isZero() ? null : { c: n.value.toNumber(), p: Q.ZERO };
        case 'sym':
            if (n.name === v && !isConst(n)) return { c: 1, p: Q.ONE };
            if (isConst(n) && (n.name === 'pi' || n.name === 'e')) return { c: evaluate(n), p: Q.ZERO };
            return null;
        case 'mul': {
            let c = 1;
            let p = Q.ZERO;
            for (const f of n.args) {
                const a = asym(f, v);
                if (!a) return null;
                c *= a.c;
                p = p.add(a.p);
            }
            return { c, p };
        }
        case 'pow': {
            if (!isNum(n.exp)) return null;
            const a = asym(n.base, v);
            if (!a) return null;
            const r = n.exp.value;
            if (a.c < 0 && !r.isInt()) return null;
            return { c: Math.pow(a.c, r.toNumber()), p: a.p.mul(r) };
        }
        case 'add': {
            let best = null;
            let sum = 0;
            for (const t of n.args) {
                const a = asym(t, v);
                if (!a) return null;
                if (!best || a.p.gt(best.p)) {
                    best = { ...a };
                    sum = a.c;
                } else if (a.p.eq(best.p)) sum += a.c;
            }
            if (!best || Math.abs(sum) < 1e-12 * Math.max(1, Math.abs(best.c))) return null;
            return { c: sum, p: best.p };
        }
        default:
            return null;
    }
}

function mLeading(n, C) {
    const { v, P } = C;
    if (Number.isFinite(P.x)) return null;
    let S = trySimp(n);
    if (!S) return null;
    const flip = P.x < 0;
    const work = flip ? trySimp(substitute(S, { [v]: neg(sym(v)) })) : S;
    if (!work) return null;
    const { top, bot } = splitNumDen(work);
    const u = top.length ? mul(top) : N1;
    const w = bot.length ? mul(bot) : N1;
    const au = asym(simp(u), v);
    const aw = asym(simp(w), v);
    if (!au || !aw) return null;
    const p = au.p.sub(aw.p);
    const c = au.c / aw.c;
    let val;
    if (p.isNeg()) val = fin(N0);
    else if (p.isZero()) {
        const exact = exactFromFloat(c);
        if (!exact) return null;
        val = fin(exact);
    } else val = infV(Math.sign(c));
    const k = aw.p;
    return {
        val,
        title: T_('Делим на старшую степень', 'Divide by the highest power'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${vTex(val, Lg)}`),
        text: T_(`При ${v} → ${flip ? '−∞' : '+∞'} в каждой сумме главное — слагаемое со старшей степенью ${v}. Делим числитель и знаменатель на ${v}${k.isOne() ? '' : '^' + k.toString()}${flip ? ' (при отрицательных ' + v + ' корень из ' + v + '² равен −' + v + ')' : ''}: остальные слагаемые стремятся к нулю, и остаётся отношение старших членов.`,
            `As ${v} → ${flip ? '−∞' : '+∞'} each sum is dominated by its highest power of ${v}. Divide the numerator and the denominator by ${v}${k.isOne() ? '' : '^' + k.toString()}${flip ? ' (for negative ' + v + ', √(' + v + '²) = −' + v + ')' : ''}: the other terms tend to zero and the ratio of the leading terms remains.`),
        rule: 'leading-terms',
    };
}

function exactFromFloat(c) {
    if (!Number.isFinite(c)) return null;
    for (const d of [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 25, 100]) {
        const k = Math.round(c * d);
        if (Math.abs(k / d - c) < 1e-10 * Math.max(1, Math.abs(c))) return num(new Q(BigInt(k), BigInt(d)));
    }
    // c = r·√m
    for (const m of [2, 3, 5, 6, 7, 10]) {
        for (const d of [1, 2, 3, 4, 5, 6, 10]) {
            const k = Math.round((c * d) / Math.sqrt(m));
            if (k && Math.abs((k * Math.sqrt(m)) / d - c) < 1e-10 * Math.max(1, Math.abs(c))) return simp(mul(num(new Q(BigInt(k), BigInt(d))), pow(num(m), HALF)));
        }
    }
    return null;
}

// ---- L'Hôpital

function quotientParts(n, v) {
    if (n.type === 'div') return { u: n.num, w: n.den };
    const S = trySimp(n);
    if (!S) return null;
    const { top, bot } = splitNumDen(S);
    if (!bot.length) return null;
    return { u: top.length ? mul(top) : N1, w: bot.length === 1 ? bot[0] : mul(bot) };
}

function mLHopital(n, C, form) {
    const { v, P } = C;
    if ((C.rounds ?? 0) >= 5) return null;
    const qp = quotientParts(n, v);
    if (!qp) return null;
    let du;
    let dw;
    try {
        du = niceForm(quickDerivative(qp.u, v), v);
        dw = niceForm(quickDerivative(qp.w, v), v);
    } catch {
        return null;
    }
    if (isZeroN(trySimp(dw) ?? dw)) return null;
    const uS = niceForm(qp.u, v);
    const wS = niceForm(qp.w, v);
    const next = div(du, dw);
    const nextS = simp(next);
    const tidy = niceForm(nextS, v);
    const L = limSub(nextS, { ...C, depth: C.depth + 1, rounds: (C.rounds ?? 0) + 1 });
    // the rule says nothing when the ratio of the derivatives has no limit ((x + sin x)/x at ∞)
    if (!L || L.k === 'dne' || L.k === 'bnd') return null;
    return {
        val: L,
        title: T_('Правило Лопиталя', "L'Hôpital's rule"),
        tex: bt((Lg) => `${limTex(P, v, Lg)} \\frac{${tx(uS, Lg)}}{${tx(wS, Lg)}} = ${limTex(P, v, Lg)} \\frac{${paren(tx(uS, Lg))}'}{${paren(tx(wS, Lg))}'} = ${limTex(P, v, Lg)} ${lt(next, Lg)}${tx(tidy, Lg) !== tx(next, Lg) ? ` = ${limTex(P, v, Lg)} ${paren2(tx(tidy, Lg), tidy)}` : ''} = ${vTex(L, Lg)}`),
        text: T_(`Неопределённость ${FORM_NAME[form]}: числитель и знаменатель дифференцируемы, производная знаменателя вблизи точки не обращается в ноль. По правилу Лопиталя предел отношения функций равен пределу отношения их производных (если последний существует).`,
            `The form ${FORM_NAME[form]}: numerator and denominator are differentiable and the derivative of the denominator does not vanish near the point. By L'Hôpital's rule the limit of the ratio equals the limit of the ratio of the derivatives (when that exists).`),
        rule: 'lhopital',
    };
}

// ---- ∞/∞: divide the numerator and the denominator by the fastest-growing term

function mDivideDominant(n, C) {
    const { v, P } = C;
    const qp = quotientParts(n, v);
    if (!qp) return null;
    const pool = [...(qp.w.type === 'add' ? qp.w.args : [qp.w]), ...(qp.u.type === 'add' ? qp.u.args : [qp.u])];
    for (const T of pool) {
        const TL = ev(T, { ...C, log: [], depth: C.depth + 1 });
        if (!TL || TL.k !== 'inf') continue;
        let a;
        let b;
        try {
            a = simp(expand(div(qp.u, T)));
            b = simp(expand(div(qp.w, T)));
        } catch {
            continue;
        }
        const C2 = { ...C, depth: C.depth + 1, log: [] };
        const A = ev(a, C2);
        const B = ev(b, C2);
        if (!A || !B || A.k === 'dne' || B.k === 'dne' || A.k === 'bnd' || B.k === 'bnd') continue;
        let val = null;
        if (A.k === 'fin' && B.k === 'fin' && !isZeroV(B)) val = fin(div(A.node, B.node));
        else if (A.k === 'fin' && B.k === 'inf') val = fin(N0);
        else if (A.k === 'inf' && B.k === 'fin' && !isZeroV(B) && Number.isFinite(B.x)) val = infV(A.s * Math.sign(B.x));
        if (!val) continue;
        return {
            val,
            title: T_('Делим на главное слагаемое', 'Divide by the dominant term'),
            tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} \\frac{${tx(a, Lg)}}{${tx(b, Lg)}} = ${vTex(val, Lg)}`),
            text: T_(`Делим числитель и знаменатель на слагаемое ${toText(prettyForm(T), { lang: 'ru' })}, которое растёт быстрее остальных: остальные части стремятся к конечным пределам (ограниченная функция, делённая на бесконечно большую, стремится к нулю).`,
                `Divide the numerator and the denominator by ${toText(prettyForm(T), { lang: 'en' })}, the fastest-growing term: what remains tends to finite limits (a bounded function over an infinitely large one tends to zero).`),
            rule: 'divide-dominant',
            sub: C2.log,
        };
    }
    return null;
}

// ---- split the fraction into a sum ((x + sin x)/x = 1 + sin x/x)

function mSplitFraction(n, C) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'mul' || !S.args.some((f) => f.type === 'add')) return null;
    let X;
    try {
        X = simp(expand(S));
    } catch {
        return null;
    }
    if (X.type !== 'add' || X.args.length > 8 || nodeKey(X) === nodeKey(S)) return null;
    const L = limSub(X, { ...C, depth: C.depth + 1 });
    if (!L) return null;
    return {
        val: L,
        title: T_('Делим почленно', 'Divide term by term'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} ${paren(tx(X, Lg))} = ${vTex(L, Lg)}`),
        text: T_('Делим каждое слагаемое числителя на знаменатель: получается сумма, предел каждого слагаемого находится сразу (ограниченная функция, делённая на бесконечно большую, стремится к нулю).',
            'Divide each term of the numerator by the denominator: the limit of each term of the sum is immediate (a bounded function over an infinitely large one tends to zero).'),
        rule: 'split-fraction',
    };
}

// ---- ∞ − ∞, 0·∞, powers

function mCommonDen(n, C) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'add') return null;
    let cf;
    try {
        cf = combineFractions(S);
    } catch {
        return null;
    }
    if (cf.type !== 'div') return null;
    const L = limSub(simp(cf), { ...C, depth: C.depth + 1 });
    if (!L) return null;
    return {
        val: L,
        title: T_('Приводим к общему знаменателю', 'Bring to a common denominator'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${paren(tx(n, Lg))} = ${limTex(P, v, Lg)} ${lt(cf, Lg)} = ${vTex(L, Lg)}`),
        text: T_('Неопределённость ∞ − ∞: сводим разность дробей к одной дроби — получается неопределённость вида 0/0 или ∞/∞, с которой уже можно работать.', 'The form ∞ − ∞: combine the fractions into one, which gives 0/0 or ∞/∞ that we can handle.'),
        rule: 'common-denominator',
    };
}

function mDominant(n, C) {
    // ∞ − ∞ for a sum: take out the fastest-growing term T: n = T·(1 + Σ others/T)
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'add') return null;
    for (const T of S.args) {
        const TL = ev(T, { ...C, log: [], depth: C.depth + 1 });
        if (!TL || TL.k !== 'inf') continue;
        const rest = trySimp(div(add(S.args.filter((t) => t !== T)), T));
        if (!rest) continue;
        const C2 = { ...C, depth: C.depth + 1, log: [] };
        const R = ev(rest, C2);
        if (!R || R.k !== 'fin') continue;
        const f = R.x + 1;
        if (!Number.isFinite(f) || Math.abs(f) < 1e-12) continue;
        const val = infV(TL.s * Math.sign(f));
        return {
            val,
            title: T_('Выносим главное слагаемое', 'Take out the dominant term'),
            tex: bt((Lg) => `${limTex(P, v, Lg)} ${paren(tx(n, Lg))} = ${limTex(P, v, Lg)} ${T.type === 'add' || T.type === 'mul' ? paren(tx(T, Lg)) : tx(T, Lg)}\\left(${tx(add(N1, rest), Lg)}\\right) = ${vTex(val, Lg)}`),
            text: T_('Выносим за скобки слагаемое, которое растёт быстрее всех: в скобках остаётся величина с конечным ненулевым пределом, поэтому выражение стремится к бесконечности.', 'Take out the fastest-growing term: the bracket tends to a finite nonzero number, so the expression tends to infinity.'),
            rule: 'dominant-term',
            sub: C2.log,
        };
    }
    return null;
}

function mZeroInf(n, C) {
    // u·w with u → 0, w → ∞: write as u / (1/w) or w / (1/u) (logarithms stay on top)
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'mul') return null;
    const zeros = [];
    const infs = [];
    const rest = [];
    for (const f of S.args) {
        const L = ev(f, { ...C, log: [], depth: C.depth + 1 });
        if (L && L.k === 'inf') infs.push(f);
        else if (isZeroV(L)) zeros.push(f);
        else rest.push(f);
    }
    if (!zeros.length || !infs.length) return null;
    const Z = mul([...rest, ...zeros]);
    const W = mul(infs);
    const logOnTop = infs.some((f) => /ln|log|atan|asin|acos/.test(nodeKey(f)));
    const expBelow = zeros.some((f) => f.type === 'pow' && !containsVar(f.base, v));
    const recip = (X) => niceForm(pow(X, NM1), v);
    const q = logOnTop || expBelow ? div(W, recip(Z)) : div(Z, recip(W));
    const L = limSub(q, { ...C, depth: C.depth + 1 });
    if (!L) return null;
    return {
        val: L,
        title: T_('Неопределённость 0·∞ → дробь', 'The form 0·∞ → a fraction'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} ${lt(q, Lg)} = ${vTex(L, Lg)}`),
        text: T_('Произведение бесконечно малой на бесконечно большую переписываем дробью: u·w = u/(1/w). Получается неопределённость 0/0 или ∞/∞.', 'Rewrite the product of an infinitesimal and an infinitely large quantity as a fraction: u·w = u/(1/w), giving 0/0 or ∞/∞.'),
        rule: 'rewrite-fraction',
    };
}

function mSecondRemarkable(n, C) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'pow') return null;
    const B = S.base;
    const Ex = S.exp;
    const inner = trySimp(mul(Ex, add(B, NM1)));
    if (!inner) return null;
    const C2 = { ...C, depth: C.depth + 1, log: [] };
    const L = ev(inner, C2);
    if (!L) return null;
    let val;
    if (L.k === 'fin') val = fin(pow(E_, L.node));
    else if (L.k === 'inf') val = L.s > 0 ? infV(1) : fin(N0);
    else return null;
    return {
        val,
        title: T_('Второй замечательный предел', 'The second remarkable limit'),
        tex: bt((Lg) => {
            const u = niceForm(add(B, NM1), v);
            const uT = u.type === 'add' || negLeadNode(u) ? paren(tx(u, Lg)) : tx(u, Lg);
            const inv = niceForm(pow(u, NM1), v);
            const innerN = niceForm(inner, v);
            const core = `\\left(1 + ${uT}\\right)^{${tx(inv, Lg)}}`;
            const outer = isNum(innerN) && innerN.value.isOne() ? core : `\\left[${core}\\right]^{${tx(innerN, Lg)}}`;
            return chainEq([`${limTex(P, v, Lg)} ${lt(n, Lg)}`, `${limTex(P, v, Lg)} ${outer}`, containsVar(innerN, v) ? `e^{${limTex(P, v, Lg)} ${lt(innerN, Lg)}}` : null, vTex(val, Lg)]);
        }),
        text: T_('Неопределённость 1^∞. Основание записываем как 1 + u, где u → 0, и пользуемся вторым замечательным пределом (1 + u)^(1/u) → e: весь предел равен e в степени lim u·(показатель).',
            'The form 1^∞. Write the base as 1 + u with u → 0 and use the second remarkable limit (1 + u)^(1/u) → e: the whole limit is e to the power lim u·(exponent).'),
        rule: 'second-remarkable',
        sub: C2.log,
    };
}

function mExpLog(n, C, form) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'pow') return null;
    const inner = trySimp(mul(S.exp, fn('ln', S.base)));
    if (!inner) return null;
    const C2 = { ...C, depth: C.depth + 1, log: [] };
    const L = ev(inner, C2);
    if (!L) return null;
    let val;
    if (L.k === 'fin') val = fin(pow(E_, L.node));
    else if (L.k === 'inf') val = L.s > 0 ? infV(1) : fin(N0);
    else return null;
    return {
        val,
        title: T_('Логарифмируем степень', 'Take the logarithm'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = e^{${limTex(P, v, Lg)} ${lt(inner, Lg)}} = ${vTex(val, Lg)}`),
        text: T_(`Неопределённость ${FORM_NAME[form]}: записываем uᵛ = e^(v·ln u). Экспонента непрерывна, поэтому достаточно найти предел показателя v·ln u.`,
            `The form ${FORM_NAME[form]}: write uᵛ = e^(v·ln u). The exponential is continuous, so it is enough to find the limit of v·ln u.`),
        rule: 'exp-log',
        sub: C2.log,
    };
}

const METHODS = {
    '0/0': [mRational, mEquivalents, mConjugate, mLHopital, mSplitFraction],
    'inf/inf': [mRational, mLeading, mConjugate, mLHopital, mSplitFraction, mDivideDominant],
    'inf-inf': [mRational, mConjugate, mCommonDen, mLeading, mDominant],
    '0*inf': [mEquivalents, mRational, mLeading, mZeroInf],
    '1^inf': [mSecondRemarkable, mExpLog],
    '0^0': [mExpLog],
    'inf^0': [mExpLog],
};

// ---------------------------------------------------------------- numeric table and check

function numPoints(P) {
    if (!Number.isFinite(P.x)) return [10, 100, 1e3, 1e4, 1e5, 1e6].map((t) => (P.x > 0 ? t : -t));
    const scale = Math.max(1, Math.abs(P.x));
    const hs = [0.1, 0.01, 0.001, 1e-4, 1e-5, 1e-6];
    return hs.map((h) => (P.side === 'left' ? P.x - h * scale : P.x + h * scale));
}

function tableFor(n, v, P) {
    const sides = P.side === 'both' && Number.isFinite(P.x) ? ['left', 'right'] : [P.side];
    const rows = [];
    for (const side of sides) {
        for (const x of numPoints({ ...P, side })) rows.push({ x, fx: evalAt(n, v, x), side: Number.isFinite(P.x) ? side : null });
    }
    return rows;
}

/** A numeric estimate on one side: {k: 'fin', x} | {k: 'inf', s} | null. */
function numericEstimate(n, v, P) {
    const xs = !Number.isFinite(P.x) ? [1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8].map((t) => (P.x > 0 ? t : -t)) : [1e-1, ...HS].map((h) => atPoint(P, h));
    const ys = xs.map((x) => evalAt(n, v, x));
    const fins = ys.filter(Number.isFinite);
    if (fins.length < 4) return null;
    // growth like c/xᵏ: the same sign, no zeros, a steady growth ratio (round-off noise has none of these)
    const tail = ys.slice(-5);
    if (tail.every((y) => Number.isFinite(y) && y !== 0 && Math.sign(y) === Math.sign(tail[0])) && Math.abs(tail[tail.length - 1]) > 1e4) {
        const r = tail.slice(1).map((y, i) => Math.abs(y / tail[i]));
        if (r.every((q) => q > 1.5) && Math.max(...r) / Math.min(...r) < 3) return { k: 'inf', s: Math.sign(tail[0]) };
    }
    // the clean prefix: while the differences keep shrinking the values converge; once they stop, round-off
    // (or divergence) has taken over and the rest is ignored
    const pre = [];
    for (const y of ys) {
        if (!Number.isFinite(y)) {
            if (pre.length) break;
            continue;
        }
        pre.push(y);
        if (pre.length >= 3) {
            const d1 = Math.abs(pre[pre.length - 2] - pre[pre.length - 3]);
            const d2 = Math.abs(pre[pre.length - 1] - pre[pre.length - 2]);
            if (d2 > 1.1 * d1 && d2 > 1e-12 * Math.max(1, Math.abs(pre[pre.length - 1]))) {
                pre.pop();
                break;
            }
        }
    }
    if (pre.length < 3) return null;
    // geometric convergence (x^(−2/3), e^(−x)…): Aitken's Δ² on the last four clean values
    if (pre.length >= 4) {
        const [y0, y1, y2, y3] = pre.slice(-4);
        const d0 = y1 - y0;
        const d1 = y2 - y1;
        const d2 = y3 - y2;
        const r1 = d1 / d0;
        const r2 = d2 / d1;
        const geometric = d0 !== 0 && d1 !== 0 && r1 > 0 && r2 > 0 && r1 < 0.8 && r2 < 0.8 && Math.abs(r1 - r2) <= 0.01 * Math.max(r1, r2);
        if (geometric && Math.abs(d2 - d1) > 1e-300) {
            const Lx = y3 - (d2 * d2) / (d2 - d1);
            const scale = Math.max(1, Math.abs(y1));
            if (Number.isFinite(Lx) && Math.abs(Lx - y3) < 0.5 * scale) return { k: 'fin', x: Math.abs(Lx) < 1e-9 * scale ? 0 : Lx };
        }
    }
    const a = pre[pre.length - 1];
    const dLast = Math.abs(a - pre[pre.length - 2]);
    if (dLast < 1e-4 * Math.max(1, Math.abs(a))) return { k: 'fin', x: a };
    return null;
}

/** Does the numeric behaviour agree with the symbolic value on this side? 'agree' | 'contradict' | 'unclear' */
function crossCheck(n, v, P, val) {
    const est = numericEstimate(n, v, P);
    const xs = !Number.isFinite(P.x) ? [1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e10, 1e12].map((t) => (P.x > 0 ? t : -t)) : [...HS, 1e-9, 1e-10, 1e-12, 1e-14].map((h) => atPoint(P, h)).filter((x) => x !== P.x);
    const ys = xs.map((x) => evalAt(n, v, x));
    if (val.k === 'fin') {
        const L = val.x;
        if (!Number.isFinite(L)) return 'unclear';
        const errs = ys.filter(Number.isFinite).map((y) => Math.abs(y - L));
        if (errs.some((e) => e <= 1e-4 * Math.max(1, Math.abs(L)))) return 'agree';
        if (est && est.k === 'fin' && Math.abs(est.x - L) > 1e-3 * Math.max(1, Math.abs(L))) return 'contradict';
        if (est && est.k === 'inf') return 'contradict';
        return 'unclear';
    }
    if (val.k === 'inf') {
        const fy = ys.filter(Number.isFinite);
        const lastBig = fy.slice(-3);
        if (lastBig.length && lastBig.every((y) => Math.sign(y) === val.s) && Math.abs(lastBig[lastBig.length - 1]) > 100) return 'agree';
        const tail = fy.slice(-5);
        if (tail.length >= 4 && tail.every((y, i) => Math.sign(y) === val.s && (i === 0 || Math.abs(y) > Math.abs(tail[i - 1]))) && Math.abs(tail[tail.length - 1]) > 10) return 'agree';
        if (est && est.k === 'fin') return 'contradict';
        if (est && est.k === 'inf' && est.s !== val.s) return 'contradict';
        return 'unclear';
    }
    return 'unclear';
}

function fmtNum(x, L) {
    if (!Number.isFinite(x)) return Number.isNaN(x) ? '\\text{—}' : x > 0 ? '+\\infty' : '-\\infty';
    const ax = Math.abs(x);
    let s;
    if (ax !== 0 && (ax >= 1e7 || ax < 1e-5)) {
        const [m, e] = x.toExponential(4).split('e');
        s = `${m.replace(/\.?0+$/, '')} \\cdot 10^{${Number(e)}}`;
    } else {
        s = x.toPrecision(8);
        if (s.includes('.')) s = s.replace(/\.?0+$/, '');
    }
    return L === 'ru' ? s.replace('.', '{,}') : s;
}

function tableStep(rows, v, P, n) {
    const tex = bt((L) => {
        const lines = rows.map((r) => `${fmtNum(r.x, L)} & ${fmtNum(r.fx, L)}`).join(' \\\\ ');
        return `\\begin{array}{r|r} ${v} & f(${v}) \\\\ \\hline ${lines} \\end{array}`;
    });
    void n;
    return step({
        title: T_('Таблица значений', 'Table of values'),
        tex,
        text: Number.isFinite(P.x)
            ? T_(`Значения функции всё ближе к точке ${v} = ${plainNum(P)}${P.side === 'both' ? ' (слева и справа)' : P.side === 'left' ? ' слева' : ' справа'}.`, `Values of the function closer and closer to ${v} = ${plainNum(P)}${P.side === 'both' ? ' (from both sides)' : P.side === 'left' ? ' from the left' : ' from the right'}.`)
            : T_(`Значения функции при всё больших по модулю ${v}.`, `Values of the function for larger and larger |${v}|.`),
        rule: 'table',
    });
}

// ---------------------------------------------------------------- public API

function valueOut(L) {
    if (!L) return null;
    if (L.k === 'fin') return niceForm(L.node);
    if (L.k === 'inf') return L.s > 0 ? 'inf' : '-inf';
    if (L.k === 'dne' || L.k === 'bnd') return 'dne';
    return null;
}

function valueTex(val, L) {
    if (val === 'inf') return '+\\infty';
    if (val === '-inf') return '-\\infty';
    if (val === 'dne') return L === 'ru' ? '\\text{не существует}' : '\\text{does not exist}';
    if (val && typeof val === 'object') return tx(val, L);
    return '?';
}

/** Is f defined at x = a (no 0⁰, no division by zero, no ln 0 …)? */
function definedAt(f, v, x) {
    let ok = true;
    const walk = (n) => {
        if (!ok) return;
        if (n.type === 'pow') {
            const b = evalAt(n.base, v, x);
            const e = evalAt(n.exp, v, x);
            if (b === 0 && !(e > 0)) ok = false;
        }
        if (n.type === 'fn' && (n.name === 'tan' || n.name === 'sec') && Math.abs(Math.cos(evalAt(n.args[0], v, x))) < 1e-12) ok = false;
        if (n.type === 'fn' && (n.name === 'cot' || n.name === 'csc') && Math.abs(Math.sin(evalAt(n.args[0], v, x))) < 1e-12) ok = false;
        nodeChildren(n).forEach(walk);
    };
    walk(f);
    return ok && Number.isFinite(evalAt(f, v, x));
}

/** |u| and sgn u with u → 0 at the point: replace by ±u and ±1 using the sign of u on the side. */
function unfoldAbs(f, v, P) {
    if (!Number.isFinite(P.x)) return f;
    let changed = false;
    const g = mapNodeDeep(f, (m) => {
        if (m.type !== 'fn' || (m.name !== 'abs' && m.name !== 'sign')) return undefined;
        const u = m.args[0];
        const u0 = evalAt(u, v, P.x);
        if (!(Math.abs(u0) < 1e-12)) return undefined;
        const s = sideSignStrict(u, v, P);
        if (!s || Number.isNaN(s)) return undefined;
        changed = true;
        return m.name === 'abs' ? (s > 0 ? u : neg(u)) : num(s);
    });
    return changed ? trySimp(g) ?? f : f;
}

function mapNodeDeep(n, fnc) {
    const r = fnc(n);
    if (r !== undefined) return r;
    const kids = nodeChildren(n);
    if (!kids.length) return n;
    const nk = kids.map((c) => mapNodeDeep(c, fnc));
    if (nk.every((c, i) => c === kids[i])) return n;
    return rebuild(n, nk);
}

function rebuild(n, kids) {
    switch (n.type) {
        case 'add':
            return add(kids);
        case 'mul':
            return mul(kids);
        case 'div':
            return div(kids[0], kids[1]);
        case 'neg':
            return neg(kids[0]);
        case 'pow':
            return pow(kids[0], kids[1]);
        case 'fn':
            return fn(n.name, ...kids);
        default:
            return n;
    }
}

function oneSide(f0, v, P, opts) {
    void opts;
    const C = { v, P, depth: 0, log: [], methods: new Set(), active: new Set(), work: { n: 0 }, rounds: 0, root: null };
    let f = f0;
    // direct substitution (continuity)
    if (P.a && definedAt(f0, v, P.x)) {
        let val = null;
        try {
            const s = simp(substitute(f, { [v]: P.a }));
            const x = evaluate(s);
            if (Number.isFinite(x) && !freeVars(s).length) {
                // continuity check: the values next to the point must approach f(a)
                const sides = P.side === 'both' ? ['left', 'right'] : [P.side];
                const ok = sides.every((side) => {
                    const ys = [1e-6, 1e-8].map((h) => evalAt(f, v, atPoint({ ...P, side }, h)));
                    return ys.every((y) => Number.isFinite(y) && Math.abs(y - x) < 1e-4 * Math.max(1, Math.abs(x)));
                });
                if (ok) val = fin(s);
            }
        } catch {
            val = null;
        }
        if (val) return { L: val, C, method: 'substitution' };
    }
    f = unfoldAbs(f0, v, P);
    C.root = f;
    let L = ev(f, C);
    if (L && L.k === 'inf' && L.s === 0) throw new Split();
    return { L, C, method: C.methods.size ? [...C.methods][C.methods.size - 1] : L ? 'arithmetic' : null };
}

/**
 * Limit of node as v → a. a: node, number, string ('inf', '-inf', 'pi/2', …) or ±Infinity.
 * opts: {steps, side: 'both' | 'left' | 'right'}.
 * → {value: node | 'inf' | '-inf' | 'dne' | null, method, steps, table: [{x, fx, side}], verified,
 *    approx?: number (a numeric estimate when no symbolic method worked; value is null then),
 *    sides?: {left, right} (when a two-sided limit splits), tex}.
 */
// |u| where the sign of u has settled near the point — x → ±∞ or a one-sided approach — is ±u there
function settleAbs(f, v, P) {
    if (P.side === 'both' && Number.isFinite(P.x)) return f;
    const probes = Number.isFinite(P.x)
        ? [1e-3, 1e-4, 1e-6, 1e-8].map((h) => P.x + (P.side === 'left' ? -h : h) * Math.max(1, Math.abs(P.x)))
        : [1e3, 1e4, 1e5, 1e6, 1e8].map((t) => (P.x > 0 ? t : -t));
    let changed = false;
    const g = mapNode(f, (n) => {
        if (n.type !== 'fn' || n.name !== 'abs' || !containsVar(n.args[0], v)) return undefined;
        const signs = probes.map((x) => Math.sign(evalAt(n.args[0], v, x)));
        if (!signs.every((z) => z === signs[0]) || !(signs[0] === 1 || signs[0] === -1)) return undefined;
        changed = true;
        const inner = settleAbs(n.args[0], v, P);
        return signs[0] > 0 ? inner : neg(inner);
    });
    if (!changed) return f;
    try {
        return simp(g);
    } catch {
        return g;
    }
}

export function limit(node, v = 'x', a = 0, opts = {}) {
    node = asNode(node);
    if (node.type === 'rel' || node.type === 'list' || node.type === 'chain') throw new MathError({ ru: 'Нужна формула функции', en: 'A formula is needed' }, null, null, 'not-expr');
    const others = freeVars(node).filter((w) => w !== v);
    const side = opts.side ?? 'both';
    let P = makePoint(asNode(a), side);
    let f;
    try {
        f = simp(node);
    } catch {
        f = node;
    }
    // x·ln x at 0: the function lives only on one side of the point, so the limit is taken from that side
    let domainSide = null;
    if (P.side === 'both' && Number.isFinite(P.x) && !others.length) {
        const scale = Math.max(1, Math.abs(P.x));
        const lives = (dir) => [1e-3, 1e-5, 1e-7].some((h) => !Number.isNaN(evalAt(f, v, P.x + dir * h * scale)));
        const l = lives(-1), r = lives(1);
        if (l !== r) {
            domainSide = r ? 'right' : 'left';
            P = { ...P, side: domainSide };
        }
    }
    if (!others.length) f = settleAbs(f, v, P);
    const wantSteps = !!opts.steps;
    const steps = [];
    const table = others.length ? [] : tableFor(f, v, P);
    const head = (L) => `${limTex(P, v, L)} ${lt(node, L)}`;
    if (wantSteps) {
        steps.push(step({ title: T_('Что ищем', 'What we look for'), tex: bt(head), rule: 'start' }));
        if (domainSide) {
            steps.push(step({
                title: T_('Где определена функция', 'Where the function is defined'),
                text: domainSide === 'right'
                    ? T_(`Левее точки ${v} = ${plainNum(P)} функция не определена, поэтому к точке можно подойти только справа: предел — правосторонний.`, `Left of ${v} = ${plainNum(P)} the function is undefined, so the point can only be approached from the right: the limit is one-sided.`)
                    : T_(`Правее точки ${v} = ${plainNum(P)} функция не определена, поэтому к точке можно подойти только слева: предел — левосторонний.`, `Right of ${v} = ${plainNum(P)} the function is undefined, so the point can only be approached from the left: the limit is one-sided.`),
                rule: 'domain-side',
            }));
        }
    }
    let result;
    let sidesInfo = null;
    const run = (PP) => {
        try {
            return oneSide(f, v, PP, opts);
        } catch (e) {
            if (e instanceof Split) return { split: true };
            if (e instanceof MathError) return { L: null, C: { log: [], methods: new Set() } };
            throw e;
        }
    };
    result = run(P);
    if (result.split) {
        const l = run({ ...P, side: 'left' });
        const r = run({ ...P, side: 'right' });
        const vl = l.split ? null : l.L;
        const vr = r.split ? null : r.L;
        sidesInfo = { left: valueOut(vl), right: valueOut(vr) };
        const same = vl && vr && vl.k === vr.k && (vl.k !== 'fin' || Math.abs(vl.x - vr.x) < 1e-12) && (vl.k !== 'inf' || vl.s === vr.s);
        if (wantSteps) {
            steps.push(step({ title: T_('Предел слева', 'Limit from the left'), tex: bt((L) => `${limTex({ ...P, side: 'left' }, v, L)} ${tx(node, L)} = ${valueTex(sidesInfo.left, L)}`), rule: 'left', sub: l.C?.log ?? [] }));
            steps.push(step({ title: T_('Предел справа', 'Limit from the right'), tex: bt((L) => `${limTex({ ...P, side: 'right' }, v, L)} ${tx(node, L)} = ${valueTex(sidesInfo.right, L)}`), rule: 'right', sub: r.C?.log ?? [] }));
        }
        result = same ? { L: vl, C: l.C, method: l.method } : { L: vl && vr ? DNE : null, C: { log: [], methods: new Set() }, method: 'one-sided', splitDiffer: !!(vl && vr) };
    }
    let L = result.L;
    let method = result.method;
    let verified = false;
    let approx;
    // cross-check against the numbers
    if (L && !others.length && (L.k === 'fin' || L.k === 'inf')) {
        const sides = P.side === 'both' && Number.isFinite(P.x) ? ['left', 'right'] : [P.side];
        const checks = sides.map((s) => crossCheck(f, v, { ...P, side: s }, L));
        const usable = sides.filter((s) => numericEstimate(f, v, { ...P, side: s }) || tableFor(f, v, { ...P, side: s }).some((r) => Number.isFinite(r.fx)));
        if (checks.includes('contradict')) {
            L = null;
            method = null;
        } else verified = checks.includes('agree') || !usable.length;
    }
    if (L && (L.k === 'dne' || L.k === 'bnd') && !others.length) verified = true;
    if (!L && !others.length) {
        // numeric fallback
        const sides = P.side === 'both' && Number.isFinite(P.x) ? ['left', 'right'] : [P.side];
        const ests = sides.map((s) => numericEstimate(f, v, { ...P, side: s }));
        if (ests.every(Boolean)) {
            const [e1, e2] = ests;
            const agreeSides = !e2 || (e1.k === e2.k && (e1.k === 'inf' ? e1.s === e2.s : Math.abs(e1.x - e2.x) < 1e-3 * Math.max(1, Math.abs(e1.x))));
            if (!agreeSides) {
                L = DNE;
                method = 'numeric';
                sidesInfo = { left: e1.k === 'inf' ? (e1.s > 0 ? 'inf' : '-inf') : null, right: e2.k === 'inf' ? (e2.s > 0 ? 'inf' : '-inf') : null, leftApprox: e1.k === 'fin' ? e1.x : undefined, rightApprox: e2.k === 'fin' ? e2.x : undefined };
            } else if (e1.k === 'inf') {
                L = infV(e1.s);
                method = 'numeric';
            } else {
                approx = e1.x;
                method = 'numeric';
            }
        }
    }
    const value = approx !== undefined ? null : valueOut(L);
    if (value === null && approx === undefined) method = null;
    const tex = approx !== undefined
        ? bt((Lg) => `${head(Lg)} \\approx ${fmtNum(approx, Lg)}`)
        : value !== null
            ? bt((Lg) => `${head(Lg)} = ${valueTex(value, Lg)}`)
            : null;
    if (wantSteps) {
        if (method === 'substitution') {
            steps.push(step({
                title: T_('Подставляем', 'Substitute'),
                tex: bt((Lg) => `${head(Lg)} = ${valueTex(value, Lg)}`),
                text: T_(`Функция определена и непрерывна в точке ${v} = ${plainNum(P)}, поэтому предел равен её значению в этой точке.`, `The function is defined and continuous at ${v} = ${plainNum(P)}, so the limit is its value there.`),
                rule: 'substitution',
            }));
        } else if (result.C && result.C.log && !result.split) {
            const form = firstForm(f, v, P);
            if (form) {
                steps.push(step({
                    title: T_('Определяем вид неопределённости', 'Identify the indeterminate form'),
                    tex: bt((Lg) => `${head(Lg)} = \\left[${FORM_TEX[form]}\\right]`),
                    text: T_(`Подстановка даёт неопределённость ${FORM_NAME[form]}: сразу ответ не получить, выражение нужно преобразовать.`, `Substitution gives the indeterminate form ${FORM_NAME[form]}: the expression has to be transformed first.`),
                    rule: 'form',
                }));
            }
            steps.push(...result.C.log);
        }
        if (result.splitDiffer || (L && L.k === 'dne')) {
            steps.push(step({
                title: T_('Предела нет', 'No limit'),
                text: sidesInfo
                    ? T_('Пределы слева и справа различаются, поэтому (двусторонний) предел не существует.', 'The limits from the left and from the right differ, so the (two-sided) limit does not exist.')
                    : T_('Функция колеблется и не приближается ни к какому числу, поэтому предела нет.', 'The function oscillates and approaches no number, so there is no limit.'),
                rule: 'dne',
            }));
        }
        if (table.length) steps.push(tableStep(table, v, P, f));
        if (approx !== undefined) {
            steps.push(step({
                title: T_('Численная оценка', 'Numeric estimate'),
                text: T_('Точными методами предел найти не удалось; по таблице значений он примерно равен указанному числу. Это приближение, а не доказательство.', 'The exact methods did not work; judging by the table of values the limit is approximately this number. It is an estimate, not a proof.'),
                rule: 'numeric',
            }));
        }
        if (tex) {
            const s = step({ title: approx !== undefined ? T_('Ответ (приближённо)', 'Answer (approximate)') : T_('Ответ', 'Answer'), tex, rule: 'answer' });
            s.final = true;
            steps.push(s);
        } else {
            steps.push(step({ title: T_('Не получилось', 'Not found'), text: T_('Найти этот предел не удалось ни точными методами, ни по таблице значений.', 'This limit could not be found either exactly or from a table of values.'), rule: 'fail' }));
        }
    }
    const out = { value, method, steps, table, verified, tex };
    if (approx !== undefined) out.approx = approx;
    if (sidesInfo) out.sides = sidesInfo;
    if (domainSide) out.domainSide = domainSide;
    return out;
}

function firstForm(f, v, P) {
    // the form of the top-level expression after naive substitution (for the explanation)
    const C = { v, P, depth: 99, log: [], methods: new Set(), active: new Set(), work: { n: 0 }, rounds: 0 };
    const S = trySimp(f) ?? f;
    try {
        if (S.type === 'add') {
            const vals = S.args.map((t) => ev(t, C));
            if (vals.some((x) => x && x.k === 'inf' && x.s > 0) && vals.some((x) => x && x.k === 'inf' && x.s < 0)) return 'inf-inf';
        }
        if (S.type === 'pow' && containsVar(S.exp, v) && containsVar(S.base, v)) {
            const B = ev(S.base, C);
            const Ex = ev(S.exp, C);
            if (isOneV(B) && Ex && Ex.k === 'inf') return '1^inf';
            if (isZeroV(B) && isZeroV(Ex)) return '0^0';
            if (B && B.k === 'inf' && isZeroV(Ex)) return 'inf^0';
        }
        const q = quotientParts(S, v);
        if (q) {
            const U = ev(q.u, C);
            const W = ev(q.w, C);
            if (isZeroV(U) && isZeroV(W)) return '0/0';
            if (U && W && U.k === 'inf' && W.k === 'inf') return 'inf/inf';
        }
        if (S.type === 'mul') {
            const vals = S.args.map((t) => ev(t, C));
            if (vals.some(isZeroV) && vals.some((x) => x && x.k === 'inf')) return '0*inf';
        }
    } catch {
        return null;
    }
    return null;
}

// ---------------------------------------------------------------- Taylor polynomials

function factorialQ(k) {
    let r = 1n;
    for (let i = 2n; i <= BigInt(k); i++) r *= i;
    return r;
}

/**
 * Taylor polynomial of degree n at a: {poly (node in powers of (v − a)), coeffs: [nodes c₀…cₙ] (exact
 * where possible), terms: [{k, coeff, term}], tex, steps}. cₖ = f⁽ᵏ⁾(a)/k! (a limit when f⁽ᵏ⁾ has a
 * removable singularity at a).
 */
export function taylorPolynomial(node, v = 'x', a = 0, n = 5, opts = {}) {
    node = asNode(node);
    if (!Number.isInteger(n) || n < 0 || n > 20) throw new MathError({ ru: 'Степень многочлена Тейлора — от 0 до 20', en: 'The degree must be from 0 to 20' }, null, null, 'range');
    const A = simp(asNode(a));
    const X = sym(v);
    let d = simp(node);
    const coeffs = [];
    const derivs = [];
    for (let k = 0; k <= n; k++) {
        if (k > 0) d = quickDerivative(d, v);
        derivs.push(d);
        let val = null;
        try {
            val = simp(substitute(d, { [v]: A }));
            if (!Number.isFinite(evaluate(val)) && !freeVars(val).length) val = null;
        } catch {
            val = null;
        }
        if (!val) {
            const L = limit(d, v, A);
            if (!L.value || typeof L.value !== 'object') throw new MathError({ ru: `Производная порядка ${k} не определена в точке — многочлена Тейлора нет`, en: `The derivative of order ${k} is undefined at the point: no Taylor polynomial` }, null, null, 'undefined');
            val = L.value;
        }
        coeffs.push(simp(div(val, num(factorialQ(k)))));
    }
    const shift = isZeroN(A) ? X : add(X, neg(A));
    const terms = [];
    for (let k = 0; k <= n; k++) {
        if (isZeroN(coeffs[k])) continue;
        const pw = k === 0 ? N1 : k === 1 ? shift : pow(shift, num(k));
        terms.push({ k, coeff: coeffs[k], term: k === 0 ? coeffs[k] : mul(coeffs[k], pw) });
    }
    const C = canonContext();
    const poly = terms.length ? C.add(terms.map((t) => C.mul([t.coeff, t.k === 0 ? N1 : t.k === 1 ? C.simplify(shift) : C.pow(C.simplify(shift), num(t.k))]))) : N0;
    // ascending powers, as Taylor polynomials are written
    const termNode = (t) => {
        if (t.k === 0) return t.coeff;
        const pw = t.k === 1 ? shift : pow(shift, num(t.k));
        if (isNum(t.coeff)) return t.coeff.value.isOne() ? pw : t.coeff.value.eq(-1) ? neg(pw) : mul(t.coeff, pw);
        return mul(t.coeff, pw);
    };
    const polyShown = terms.length ? (terms.length === 1 ? termNode(terms[0]) : add(terms.map(termNode))) : N0;
    const tex = bt((L) => `T_{${n}}(${v}) = ${tx(polyShown, L)}`);
    const steps = [];
    if (opts.steps) {
        steps.push(step({
            title: T_('Формула Тейлора', "Taylor's formula"),
            tex: `T_{n}(${v}) = \\sum_{k=0}^{n} \\frac{f^{(k)}(a)}{k!}(${v} - a)^{k}`,
            text: T_('Коэффициенты — производные в точке, делённые на факториалы: многочлен совпадает с функцией в точке вместе с n первыми производными.', 'The coefficients are the derivatives at the point divided by factorials: the polynomial matches the function and its first n derivatives there.'),
            rule: 'taylor',
        }));
        for (let k = 0; k <= n; k++) {
            steps.push(step({
                title: T_(`Коэффициент при степени ${k}`, `Coefficient of degree ${k}`),
                tex: bt((L) => `\\frac{f^{(${k})}(${tx(A, L)})}{${k}!} = ${tx(coeffs[k], L)}`),
                rule: 'coefficient',
            }));
        }
        const s = step({ title: T_('Многочлен Тейлора', 'Taylor polynomial'), tex, rule: 'answer' });
        s.final = true;
        steps.push(s);
    }
    return { poly: polyShown, polyCanonical: poly, coeffs, terms, tex, steps };
}

/**
 * Lagrange bound of the remainder |f(x) − Tₙ(x)| ≤ M·|x − a|ⁿ⁺¹/(n + 1)! with M = max |f⁽ⁿ⁺¹⁾| on the
 * segment between a and x (sampled numerically, with a small safety margin). → {bound, M, tex}.
 */
export function taylorRemainderBound(node, v = 'x', a = 0, n = 5, x = 1) {
    node = asNode(node);
    const A = evaluate(simp(asNode(a)));
    const X = typeof x === 'number' ? x : evaluate(simp(asNode(x)));
    let d = simp(node);
    for (let k = 0; k <= n; k++) d = quickDerivative(d, v);
    const lo = Math.min(A, X);
    const hi = Math.max(A, X);
    let M = 0;
    const N = 400;
    for (let i = 0; i <= N; i++) {
        const t = lo + ((hi - lo) * i) / N;
        const y = Math.abs(evalAt(d, v, t));
        if (!Number.isFinite(y)) return { bound: Infinity, M: Infinity, tex: null };
        M = Math.max(M, y);
    }
    M *= 1.0001;
    const fact = Number(factorialQ(n + 1));
    const bound = (M * Math.abs(X - A) ** (n + 1)) / fact;
    const tex = bt((L) => `\\left|R_{${n}}\\right| \\le \\frac{M\\,|${v} - a|^{${n + 1}}}{${n + 1}!} \\approx ${fmtNum(bound, L)}`);
    return { bound, M, tex };
}
