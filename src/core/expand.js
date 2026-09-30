// core/expand — multiply out and collect by powers of a variable (one fraction: fractions.js).
//
// expand(node) simplifies, then distributes products over sums and expands positive integer powers of sums
// (binomial formula for two terms, repeated multiplication otherwise), collecting like terms as it goes.
// Negative and fractional powers of sums stay as atoms (denominators are not expanded); function arguments
// are expanded too. Guard: more than 1000 terms (predicted or produced) → MathError 'too-big',
// e.g. (x + y + z)^60 (1891 terms) is refused while (x + 1)^200 is fine.

import { Q, MathError } from './rational.js';
import { num, nodeKey, containsVar, isConst, summands } from './ast.js';
import { splitCoeff, canonContext } from './simplify.js';
import { msg } from '../i18n/index.js';

const MAX_TERMS = 1000;
const MAX_WORK = 3000000;
const TOO_BIG = msg('core.expand.expanding_would_give_too_many_terms');

const N1 = num(1);
const isNum = (n) => n.type === 'num';

function mulTerms(A, B, C, st) {
    st.work += A.length * B.length;
    if (st.work > MAX_WORK) throw new MathError(TOO_BIG, null, null, 'too-big');
    const acc = new Map();
    for (const a of A) {
        for (const b of B) {
            const p = C.mul([a, b]);
            for (const t of summands(p)) {
                const { coef, rest } = splitCoeff(t);
                const key = rest ? nodeKey(rest) : '#';
                const e = acc.get(key);
                if (e) e.coef = e.coef.add(coef);
                else acc.set(key, { coef, rest });
            }
        }
        if (acc.size > MAX_TERMS) throw new MathError(TOO_BIG, null, null, 'too-big');
    }
    const out = [];
    for (const { coef, rest } of acc.values()) {
        if (coef.isZero()) continue;
        out.push(rest ? C.mul([num(coef), rest]) : num(coef));
    }
    return out.length ? out : [num(0)];
}

function predictedTerms(k, n) {
    // C(n + k − 1, k − 1)
    let r = 1;
    const m = Math.min(k - 1, n);
    for (let j = 1; j <= m; j++) {
        r = (r * (n + k - 1 - m + j)) / j;
        if (r > MAX_TERMS) return Infinity;
    }
    return r;
}

function powTerms(terms, n, C, st) {
    if (predictedTerms(terms.length, n) > MAX_TERMS) throw new MathError(TOO_BIG, null, null, 'too-big');
    if (terms.length === 2) {
        const [a, b] = terms;
        const out = [];
        let binom = 1n;
        const N = BigInt(n);
        for (let j = 0n; j <= N; j++) {
            out.push(C.mul([num(binom), C.pow(a, num(N - j)), C.pow(b, num(j))]));
            binom = (binom * (N - j)) / (j + 1n);
        }
        st.work += n;
        return out;
    }
    let acc = [N1];
    for (let k = 0; k < n; k++) acc = mulTerms(acc, terms, C, st);
    return acc;
}

function X(n, C, st) {
    switch (n.type) {
        case 'num':
        case 'sym':
            return n;
        case 'add':
            return C.add(n.args.map((a) => X(a, C, st)));
        case 'mul': {
            let acc = [N1];
            for (const f of n.args) acc = mulTerms(acc, summands(X(f, C, st)), C, st);
            return C.add(acc);
        }
        case 'pow': {
            const b = X(n.base, C, st);
            const e = X(n.exp, C, st);
            if (b.type === 'add' && isNum(e) && e.value.isInt() && e.value.isPos()) {
                if (e.value.gt(100000)) throw new MathError(TOO_BIG, null, null, 'too-big');
                return C.add(powTerms(b.args, Number(e.value.n), C, st));
            }
            return C.pow(b, e);
        }
        case 'fn':
            return C.fn(
                n.name,
                n.args.map((a) => X(a, C, st)),
            );
        case 'rel':
            return Object.freeze({ type: 'rel', op: n.op, lhs: X(n.lhs, C, st), rhs: X(n.rhs, C, st) });
        case 'chain':
            return Object.freeze({ type: 'chain', items: Object.freeze(n.items.map((a) => X(a, C, st))), ops: n.ops });
        case 'list':
            return Object.freeze({ type: 'list', items: Object.freeze(n.items.map((a) => X(a, C, st))) });
        default:
            throw new TypeError(`expand: unknown node ${n?.type}`);
    }
}

/** Expand products and integer powers of sums; the result is canonical (see simplify.js). opts: {complex}. */
export function expand(node, opts = {}) {
    const C = canonContext({ ...opts, budget: 5000000 });
    return X(C.simplify(node), C, { work: 0 });
}

/**
 * Coefficients by powers of varName after expansion: Map degree (number, descending) → coefficient node
 * (other letters allowed in coefficients). For a relation lhs = rhs it works on lhs − rhs.
 * Null when varName occurs non-polynomially (sin x, √x is fine: degree 0.5; 1/x: degree −1).
 */
export function collectTerms(node, varName = 'x', opts = {}) {
    const C = canonContext(opts);
    let n = node;
    if (n.type === 'rel') n = Object.freeze({ type: 'add', args: Object.freeze([n.lhs, Object.freeze({ type: 'neg', arg: n.rhs })]) });
    const e = expand(n, opts);
    const groups = new Map();
    for (const t of summands(e)) {
        const factors = t.type === 'mul' ? t.args : [t];
        let deg = Q.ZERO;
        const rest = [];
        for (const f of factors) {
            if (f.type === 'sym' && f.name === varName && !isConst(f)) deg = deg.add(Q.ONE);
            else if (f.type === 'pow' && f.base.type === 'sym' && f.base.name === varName && !isConst(f.base) && isNum(f.exp)) deg = deg.add(f.exp.value);
            else if (containsVar(f, varName)) return null;
            else rest.push(f);
        }
        const key = deg.toString();
        const g = groups.get(key);
        const c = C.mul(rest);
        if (g) g.parts.push(c);
        else groups.set(key, { deg, parts: [c] });
    }
    const out = new Map();
    for (const g of [...groups.values()].sort((a, b) => b.deg.cmp(a.deg))) {
        const c = C.add(g.parts);
        if (!(isNum(c) && c.value.isZero())) out.set(g.deg.toNumber(), c);
    }
    return out;
}
