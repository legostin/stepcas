// calculus/limit/evaluator — limit arithmetic on the expression tree: substitution, infinities, where a form is indeterminate.

import { containsVar, freeVars, neg, substitute, sym, add, pow, num, mul, div, fn } from '../../core/ast.js';
import { Q } from '../../core/rational.js';
import { BND, DNE, PI, fin, infV, isOneV, isZeroV, needSign, safeEval, sideSign, sideSignStrict, asym, splitNumDen } from './common.js';
import { resolve } from './forms.js';
import { isNum, simp, trySimp, N0, N1 } from '../display.js';

// ---------------------------------------------------------------- the evaluator

/**
 * A fresh context for ev(): the variable, the point, the log of steps, the work budget — and ev itself, which the
 * resolvers of indeterminate forms call back through C.ev (they cannot import it: ev imports them).
 */
export function limitContext(v, P, extra = {}) {
    return { v, P, depth: 0, log: [], methods: new Set(), active: new Set(), work: { n: 0 }, rounds: 0, root: null, ev, ...extra };
}

/**
 * Limit of n at the point C.P → LV ({k: 'fin', node, x} | {k: 'inf', s} | BND | DNE) or null.
 * Indeterminate combinations are handed to resolve(), which records its steps in C.log.
 */
export function ev(n, C) {
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
            return bx > 1 === Ex.s > 0 ? infV(1) : fin(N0);
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
        return B.x > 1 === needSign(Ex).s > 0 ? infV(1) : fin(N0);
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
