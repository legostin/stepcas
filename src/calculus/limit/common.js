// calculus/limit/common — helpers, the point a (finite, ±∞, one-sided) and limit values (finite, ±∞, does not exist).

import { num, sym, neg, isConst, pow } from '../../core/ast.js';
import { Q, MathError } from '../../core/rational.js';
import { evaluate } from '../../core/evaluate.js';
import { msg } from '../../i18n/index.js';
import { calcTex, isNum, paren, trySimp, isZero } from '../display.js';

export const PI = sym('pi');

export const paren2 = (s, n) => (n.type === 'add' ? paren(s) : s);
/** "a = b = c" without repeating equal neighbours. */
export const chainEq = (parts) => parts.filter((x, i, a) => x && (i === 0 || x !== a[i - 1])).join(' = ');
/** An expression after \lim: a sum goes in brackets. */
export const lt = (n, L) => (n.type === 'add' ? paren(calcTex(n, L)) : calcTex(n, L));

// ---------------------------------------------------------------- the point

/** {a: node | null, x: number (±Infinity for ∞), side: 'left' | 'right' | 'both'} */
export function makePoint(aNode, side) {
    const s = trySimp(aNode) ?? aNode;
    if (isConst(s) && s.name === 'inf') return { a: null, x: Infinity, side: 'left' };
    if (s.type === 'mul' && s.args.length === 2 && isNum(s.args[0]) && s.args[0].value.isNeg() && isConst(s.args[1]) && s.args[1].name === 'inf')
        return { a: null, x: -Infinity, side: 'right' };
    const x = evaluate(s);
    if (!Number.isFinite(x)) throw new MathError(msg('calculus.limit.common.point_must_be_number_or'), null, null, 'range');
    return { a: s, x, side };
}

export function atPoint(P, h) {
    if (P.x === Infinity) return 1 / h;
    if (P.x === -Infinity) return -1 / h;
    const scale = Math.max(1, Math.abs(P.x));
    return P.side === 'left' ? P.x - h * scale : P.x + h * scale;
}

function arrowTex(P, v, L) {
    void L;
    if (P.x === Infinity) return `${v} \\to +\\infty`;
    if (P.x === -Infinity) return `${v} \\to -\\infty`;
    const a = calcTex(P.a, L);
    const sup = P.side === 'left' ? '^{-}' : P.side === 'right' ? '^{+}' : '';
    return `${v} \\to ${sup ? `{${a}}${sup}` : a}`;
}

export const limTex = (P, v, L) => `\\lim_{${arrowTex(P, v, L)}}`;

export function safeEval(n) {
    try {
        const y = evaluate(n);
        return typeof y === 'number' ? y : NaN;
    } catch {
        return NaN;
    }
}

export function evalAt(n, v, x) {
    try {
        const y = evaluate(n, { [v]: x });
        return typeof y === 'number' ? y : NaN;
    } catch {
        return NaN;
    }
}

export const HS = [1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8];

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

export class Split extends Error {}

export const negLeadNode = (n) => (isNum(n) && n.value.isNeg()) || n.type === 'neg' || (n.type === 'mul' && isNum(n.args[0]) && n.args[0].value.isNeg());

export function negLead(n) {
    if (isNum(n)) return n.value.isNeg();
    if (n.type === 'neg') return true;
    if (n.type === 'mul') return n.args.length > 0 && negLead(n.args[0]);
    return false;
}

/** The sign near the point; for a two-sided limit whose sides differ: 'split'. */
export function sideSign(n, v, P) {
    if (P.side !== 'both' || !Number.isFinite(P.x)) return signNear(n, v, P);
    const l = signNear(n, v, { ...P, side: 'left' });
    const r = signNear(n, v, { ...P, side: 'right' });
    if (Number.isNaN(l)) return r;
    if (Number.isNaN(r)) return l;
    if (l !== r) return 'split';
    return l;
}

/** The sign or throw Split (when the answer really depends on the side). */
export function sideSignStrict(n, v, P) {
    const s = sideSign(n, v, P);
    if (s === 'split') throw new Split();
    return s;
}

/** An infinity of a known sign, or throw Split for ∞ of varying sign where the sign matters. */
export function needSign(L) {
    if (L.k === 'inf' && L.s === 0) throw new Split();
    return L;
}

// ---------------------------------------------------------------- limit values

export const fin = (node) => {
    const s = trySimp(node) ?? node;
    let x;
    try {
        x = evaluate(s);
    } catch {
        x = NaN;
    }
    return { k: 'fin', node: s, x };
};
export const infV = (s) => ({ k: 'inf', s });
export const BND = { k: 'bnd' };
export const DNE = { k: 'dne' };

export const isZeroV = (L) => L && L.k === 'fin' && (isZero(L.node) || (Number.isFinite(L.x) && Math.abs(L.x) < 1e-15 && isZero(trySimp(L.node) ?? L.node)));
export const isOneV = (L) => L && L.k === 'fin' && isNum(L.node) && L.node.value.isOne();

export function splitNumDen(n) {
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

/** n ~ c·t^p as t → +∞ (t is the variable): {c: number, p: Q} or null. */
export function asym(n, v) {
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
