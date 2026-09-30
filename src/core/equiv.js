// equiv — are two answers the same? (expressions, numbers, sets of roots)
//
// equivalent(a, b):
//   1. exact: expand(simplify(a − b)) is 0 → yes; if that difference is a nonzero polynomial with rational
//      coefficients → no. Canonical simplification may widen domains ((√x)² = x, x/x = 1), and such pairs
//      count as equivalent.
//   2. numeric: ≥ 24 seeded pseudo-random points in several ranges (small, negative, medium, large-ish),
//      non-integer so removable points like x = 1 in (x²−1)/(x−1) are never hit (such pairs are equivalent).
//      Where both sides are finite they must agree within 1e-9 (relative, and absolute near 0); a point
//      where one side is defined and the other is not (|x| ≤ 10) means the domains differ on an interval →
//      not equivalent (so √(x²) ≠ x and ln(x²) ≠ 2 ln x). At least 5 usable points are required.
//   3. if the reals give fewer than 5 usable points (e.g. √(x − 100) on small x, or √ of negatives), the
//      comparison is repeated at complex points with principal branches.
//   Expressions containing the constant i are compared in complex mode from the start.
// Relations: two equations are equivalent when lhs − rhs are proportional (nonzero constant factor);
// inequalities also need a positive factor after turning > into <. Lists compare item by item in order.

import { Q } from './rational.js';
import { num, add, neg, freeVars, nodeSome, isConst } from './ast.js';
import { parse } from './parse.js';
import { simplify } from './simplify.js';
import { expand } from './expand.js';
import { evaluate } from './evaluate.js';
import { Complex } from './complex.js';
import { rng } from './random.js';

const RANGES = [
    [0.1, 2],
    [-2, -0.1],
    [2, 10],
    [-10, -2],
    [0.05, 0.9],
    [10, 40],
    [-40, -10],
    [-0.9, -0.05],
];

function asNode(x, opts) {
    if (x && typeof x === 'object' && typeof x.type === 'string') return x;
    if (typeof x === 'string') return parse(x, opts);
    if (x instanceof Q || typeof x === 'number' || typeof x === 'bigint') return num(x);
    throw new TypeError('expected a node, a string or a number');
}

const usesI = (n) => nodeSome(n, (m) => isConst(m) && m.name === 'i');

function close(a, b, tol) {
    return Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b));
}

function closeC(a, b, tol) {
    const s = Math.max(1, a.abs(), b.abs());
    return Math.abs(a.re - b.re) <= tol * s && Math.abs(a.im - b.im) <= tol * s;
}

// only rationals, variables, +, ·, non-negative integer powers
function isRationalPoly(n) {
    switch (n.type) {
        case 'num':
            return true;
        case 'sym':
            return !isConst(n);
        case 'add':
        case 'mul':
            return n.args.every(isRationalPoly);
        case 'pow':
            return n.exp.type === 'num' && n.exp.value.isInt() && !n.exp.value.isNeg() && isRationalPoly(n.base);
        default:
            return false;
    }
}

function exactDiff(a, b, opts) {
    try {
        const d = expand(add(a, neg(b)), { complex: opts.complex });
        if (d.type === 'num') return d.value.isZero() ? true : false;
        if (isRationalPoly(d)) return false;
    } catch {
        // fall through to sampling
    }
    return null;
}

/**
 * Numeric comparison: returns true / false, or null when there are too few usable points.
 * f(env) → value for side a and b.
 */
function sample(a, b, vars, opts) {
    const r = rng(opts.seed ?? 20260927);
    const tol = opts.tol ?? 1e-9;
    const complexMode = !!opts.complex || usesI(a) || usesI(b);
    let usable = 0;
    let points = 0;
    const N = opts.points ?? 24;
    for (let k = 0; k < N; k++) {
        const env = {};
        let small = true;
        for (const v of vars) {
            const [lo, hi] = RANGES[(k + vars.indexOf(v)) % RANGES.length];
            let x = r.real(lo, hi);
            if (Number.isInteger(x)) x += 1e-7;
            env[v] = x;
            if (Math.abs(x) > 10) small = false;
        }
        points++;
        if (!vars.length && k > 0) break;
        let va;
        let vb;
        try {
            va = evaluate(a, env, { complex: complexMode });
            vb = evaluate(b, env, { complex: complexMode });
        } catch {
            return null;
        }
        if (complexMode) {
            const fa = va.isFinite() && va.abs() < 1e150;
            const fb = vb.isFinite() && vb.abs() < 1e150;
            if (fa && fb) {
                usable++;
                if (!closeC(va, vb, tol)) return false;
            } else if (fa !== fb && small) return false;
        } else {
            const fa = Number.isFinite(va) && Math.abs(va) < 1e150;
            const fb = Number.isFinite(vb) && Math.abs(vb) < 1e150;
            if (fa && fb) {
                usable++;
                if (!close(va, vb, tol)) return false;
            } else if (fa !== fb && small && (Number.isNaN(va) || Number.isNaN(vb))) return false;
        }
    }
    if (!vars.length) return usable >= 1 ? true : null;
    return usable >= 5 ? true : null;
}

function sampleComplex(a, b, vars, opts) {
    const r = rng((opts.seed ?? 20260927) + 1);
    const tol = opts.tol ?? 1e-9;
    let usable = 0;
    for (let k = 0; k < 24; k++) {
        const env = {};
        for (const v of vars) env[v] = new Complex(r.real(-3, 3), r.real(-3, 3));
        let va;
        let vb;
        try {
            va = evaluate(a, env, { complex: true });
            vb = evaluate(b, env, { complex: true });
        } catch {
            return false;
        }
        const fa = va.isFinite();
        const fb = vb.isFinite();
        if (fa && fb) {
            usable++;
            if (!closeC(va, vb, tol)) return false;
        }
    }
    return usable >= 5;
}

function equivExpr(a, b, opts) {
    const ex = exactDiff(a, b, opts);
    if (ex !== null) return ex;
    const vars = [...new Set([...freeVars(a), ...freeVars(b), ...(opts.vars ?? [])])];
    const s = sample(a, b, vars, opts);
    if (s !== null) return s;
    if (!vars.length) return false;
    return sampleComplex(a, b, vars, opts);
}

const FLIP = { '>': '<', '>=': '<=', '<': '<', '<=': '<=', '=': '=', '!=': '!=' };

function normRel(r) {
    // lhs op rhs → (d, op) with op ∈ {=, !=, <, <=} and d op 0
    if (r.op === '>' || r.op === '>=') return { d: add(r.rhs, neg(r.lhs)), op: FLIP[r.op] };
    return { d: add(r.lhs, neg(r.rhs)), op: r.op };
}

// d1 = k·d2 with a constant k ≠ 0 (k > 0 when positive is set)
function proportional(d1, d2, positive, opts) {
    const vars = [...new Set([...freeVars(d1), ...freeVars(d2), ...(opts.vars ?? [])])];
    const r = rng(opts.seed ?? 20260927);
    let ratio = null;
    let usable = 0;
    for (let k = 0; k < 24; k++) {
        const env = {};
        for (const v of vars) {
            const [lo, hi] = RANGES[(k + vars.indexOf(v)) % RANGES.length];
            env[v] = r.real(lo, hi);
        }
        let x;
        let y;
        try {
            x = evaluate(d1, env);
            y = evaluate(d2, env);
        } catch {
            return false;
        }
        if (!Number.isFinite(x) || !Number.isFinite(y)) continue;
        if (Math.abs(y) < 1e-12 && Math.abs(x) < 1e-12) continue;
        if (Math.abs(y) < 1e-12 || Math.abs(x) < 1e-12) return false;
        const q = x / y;
        if (ratio === null) ratio = q;
        else if (!close(q, ratio, 1e-8)) return false;
        usable++;
    }
    if (usable < 3 || ratio === null) return false;
    return positive ? ratio > 0 : true;
}

/**
 * Are two expressions (nodes or strings) equal as functions? opts: {vars, complex, tol (1e-9), seed}.
 * Strings are parsed with opts. Parse errors propagate as MathError.
 */
export function equivalent(a, b, opts = {}) {
    a = asNode(a, opts);
    b = asNode(b, opts);
    if (a.type === 'list' || b.type === 'list') {
        if (a.type !== 'list' || b.type !== 'list' || a.items.length !== b.items.length) return false;
        return a.items.every((x, k) => equivalent(x, b.items[k], opts));
    }
    if (a.type === 'rel' || b.type === 'rel') {
        if (a.type !== 'rel' || b.type !== 'rel') return false;
        const A = normRel(a);
        const B = normRel(b);
        if (A.op === '=' || A.op === '!=') {
            if (B.op !== A.op) return false;
            return proportional(A.d, B.d, false, opts);
        }
        if (A.op !== B.op) return false;
        return proportional(A.d, B.d, true, opts);
    }
    if (a.type === 'chain' || b.type === 'chain') {
        if (a.type !== 'chain' || b.type !== 'chain' || a.items.length !== b.items.length) return false;
        if (a.ops.join() !== b.ops.join()) return false;
        return a.items.every((x, k) => equivExpr(x, b.items[k], opts));
    }
    return equivExpr(a, b, opts);
}

/**
 * Same number? a, b: nodes, strings, numbers or Q. Exact when both sides simplify exactly, otherwise
 * numeric with opts.tol (default 1e-9, relative). Complex values are compared when i appears.
 */
export function sameValue(a, b, opts = {}) {
    a = asNode(a, opts);
    b = asNode(b, opts);
    const complex = !!opts.complex || usesI(a) || usesI(b);
    try {
        const d = simplify(add(a, neg(b)), { complex });
        if (d.type === 'num') return d.value.isZero();
    } catch {
        // numeric fallback
    }
    const tol = opts.tol ?? 1e-9;
    try {
        if (complex) {
            const x = evaluate(a, {}, { complex: true });
            const y = evaluate(b, {}, { complex: true });
            return x.isFinite() && y.isFinite() && closeC(x, y, tol);
        }
        const x = evaluate(a);
        const y = evaluate(b);
        return Number.isFinite(x) && Number.isFinite(y) && close(x, y, tol);
    } catch {
        return false;
    }
}

function itemsOf(x, opts) {
    if (Array.isArray(x)) return x.map((v) => asNode(v, opts));
    const n = asNode(x, opts);
    return n.type === 'list' ? [...n.items] : [n];
}

/**
 * Same set of values (order-free)? Items are numbers/nodes/strings, or a list node / "1; 2" string.
 * Duplicates are ignored unless {multiset: true}. Items with variables are compared with equivalent().
 */
export function sameSet(listA, listB, opts = {}) {
    let A = itemsOf(listA, opts);
    let B = itemsOf(listB, opts);
    const same = (x, y) => (freeVars(x).length || freeVars(y).length ? equivalent(x, y, opts) : sameValue(x, y, opts));
    const dedupe = (L) => {
        const out = [];
        for (const x of L) if (!out.some((y) => same(x, y))) out.push(x);
        return out;
    };
    if (!opts.multiset) {
        A = dedupe(A);
        B = dedupe(B);
    }
    if (A.length !== B.length) return false;
    const used = new Array(B.length).fill(false);
    for (const x of A) {
        const k = B.findIndex((y, j) => !used[j] && same(x, y));
        if (k < 0) return false;
        used[k] = true;
    }
    return true;
}
