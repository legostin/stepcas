// limit/common — helpers, the point a (finite, ±∞, one-sided) and limit values (finite, ±∞, does not exist).

import { num, sym, neg, toNode, nodeKey, isConst } from '../../core/ast.js';
import { Q, MathError } from '../../core/rational.js';
import { parse } from '../../core/parse.js';
import { simplify } from '../../core/simplify.js';
import { calcTex } from '../derivative/index.js';
import { evaluate } from '../../core/evaluate.js';
import { msg } from '../../i18n/index.js';

export const N0 = num(0);
export const N1 = num(1);
export const NM1 = num(-1);
export const N2 = num(2);
export const HALF = num(Q.HALF);
const INF = sym('inf');
export const E_ = sym('e');
export const PI = sym('pi');

export const isNum = (n) => n.type === 'num';
export const qn2 = (q) => num(q);
export const isZeroN = (n) => isNum(n) && n.value.isZero();
export const T_ = (ru, en) => ({ ru, en });

export function asNode(x) {
    if (x && typeof x === 'object' && typeof x.type === 'string') return x;
    if (typeof x === 'string') return parse(x);
    if (x === Infinity) return INF;
    if (x === -Infinity) return neg(INF);
    return toNode(x);
}

export function simp(n) {
    let s = simplify(n);
    for (let i = 0; i < 3; i++) {
        const t = simplify(s);
        if (nodeKey(t) === nodeKey(s)) break;
        s = t;
    }
    return s;
}

export function trySimp(n) {
    try {
        return simp(n);
    } catch {
        return null;
    }
}

export const tx = (n, L) => calcTex(n, L);
const tall = (s) => /\\frac|\\sqrt|\\left|\^\{/.test(s);
export const paren = (s) => (tall(s) ? `\\left(${s}\\right)` : `(${s})`);
export const paren2 = (s, n) => (n.type === 'add' ? paren(s) : s);
/** "a = b = c" without repeating equal neighbours. */
export const chainEq = (parts) => parts.filter((x, i, a) => x && (i === 0 || x !== a[i - 1])).join(' = ');
/** An expression after \lim: a sum goes in brackets. */
export const lt = (n, L) => (n.type === 'add' ? paren(tx(n, L)) : tx(n, L));

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
    const a = tx(P.a, L);
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

export const isZeroV = (L) => L && L.k === 'fin' && (isZeroN(L.node) || (Number.isFinite(L.x) && Math.abs(L.x) < 1e-15 && isZeroN(trySimp(L.node) ?? L.node)));
export const isOneV = (L) => L && L.k === 'fin' && isNum(L.node) && L.node.value.isOne();
