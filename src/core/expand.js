// expand — multiply out, collect by powers of a variable, combine into one fraction.
//
// expand(node) simplifies, then distributes products over sums and expands positive integer powers of sums
// (binomial formula for two terms, repeated multiplication otherwise), collecting like terms as it goes.
// Negative and fractional powers of sums stay as atoms (denominators are not expanded); function arguments
// are expanded too. Guard: more than 1000 terms (predicted or produced) → MathError 'too-big',
// e.g. (x + y + z)^60 (1891 terms) is refused while (x + 1)^200 is fine.

import { Q, MathError, bigGcd, bigLcm } from './rational.js';
import { num, div, freeVars, nodeKey, containsVar, isConst } from './ast.js';
import { splitCoeff, canonContext } from './simplify.js';
import { Poly } from './poly.js';
import { msg } from '../i18n/index.js';

const MAX_TERMS = 1000;
const MAX_WORK = 3000000;
const TOO_BIG = msg('core.expand.expanding_would_give_too_many_terms');

const N1 = num(1);
const isNum = (n) => n.type === 'num';
const termsOf = (n) => (n.type === 'add' ? n.args : [n]);

function mulTerms(A, B, C, st) {
    st.work += A.length * B.length;
    if (st.work > MAX_WORK) throw new MathError(TOO_BIG, null, null, 'too-big');
    const acc = new Map();
    for (const a of A) {
        for (const b of B) {
            const p = C.mul([a, b]);
            for (const t of termsOf(p)) {
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
            for (const f of n.args) acc = mulTerms(acc, termsOf(X(f, C, st)), C, st);
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
            return C.fn(n.name, n.args.map((a) => X(a, C, st)));
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
    for (const t of termsOf(e)) {
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

function contentOf(terms) {
    let g = 0n;
    let l = 1n;
    for (const t of terms) {
        const { coef } = splitCoeff(t);
        if (coef.isZero()) continue;
        g = bigGcd(g, coef.n);
        l = bigLcm(l, coef.d);
    }
    return g === 0n ? Q.ONE : new Q(g, l);
}

function combine(s, C, opts) {
    const terms = termsOf(s);
    // One variable: polynomial denominators are factored over Q first, so the common denominator is the least one
    // built from the factors (1/x + 1/(x² − x) → over x(x − 1), not x(x² − x)).
    // (a single fraction keeps its denominator as it is — only an LCD of several is built from factors)
    const vars = freeVars(s);
    let fv = vars.length === 1 ? vars[0] : null;
    if (fv) {
        const bases = new Set();
        for (const t of terms) {
            const { rest } = splitCoeff(t);
            for (const f of rest === null ? [] : rest.type === 'mul' ? rest.args : [rest]) {
                if (f.type === 'pow' && isNum(f.exp) && f.exp.value.isNeg() && containsVar(f.base, fv)) bases.add(nodeKey(f.base));
            }
        }
        if (bases.size < 2) fv = null;
    }
    const cache = new Map();
    const factored = (base) => {
        const k = nodeKey(base);
        if (cache.has(k)) return cache.get(k);
        let out = null;
        try {
            const P = Poly.fromNode(base, fv);
            if (P && P.degree >= 1 && P.degree <= 24) {
                const fz = P.factor();
                const fs = fz.factors.map(({ poly, mult }) => ({ base: poly.toNode(fv), e: new Q(mult) }));
                if (fs.length && !(fs.length === 1 && fs[0].e.isOne() && fz.constant.isOne())) out = { c: fz.constant, fs };
            }
        } catch {
            out = null;
        }
        cache.set(k, out);
        return out;
    };
    const parts = terms.map((t) => {
        const split = splitCoeff(t);
        let coef = split.coef;
        const rest = split.rest;
        const factors = rest === null ? [] : rest.type === 'mul' ? rest.args : [rest];
        const numF = [];
        const den = new Map();
        const addDen = (base, e) => {
            const k = nodeKey(base);
            const cur = den.get(k);
            den.set(k, { base, e: cur ? cur.e.add(e) : e });
        };
        for (const f of factors) {
            if (f.type === 'pow' && isNum(f.exp) && f.exp.value.isNeg()) {
                const e = f.exp.value.neg();
                const fz = fv && e.isInt() && containsVar(f.base, fv) ? factored(f.base) : null;
                if (fz) {
                    coef = coef.div(fz.c.pow(e));
                    for (const g of fz.fs) addDen(g.base, g.e.mul(e));
                } else addDen(f.base, e);
            } else numF.push(f);
        }
        return { coef, numF, den };
    });
    let lcdQ = 1n;
    const lcd = new Map();
    for (const p of parts) {
        lcdQ = bigLcm(lcdQ, p.coef.d);
        for (const [k, { base, e }] of p.den) {
            const cur = lcd.get(k);
            if (!cur || e.gt(cur.e)) lcd.set(k, { base, e });
        }
    }
    if (lcdQ === 1n && lcd.size === 0) return s;
    const nums = parts.map((p) => {
        const extra = [];
        for (const [k, { base, e }] of lcd) {
            const te = p.den.get(k)?.e ?? Q.ZERO;
            const diff = e.sub(te);
            if (!diff.isZero()) extra.push(C.pow(base, num(diff)));
        }
        return C.mul([num(p.coef.n * (lcdQ / p.coef.d)), ...p.numF, ...extra]);
    });
    let N = expand(C.add(nums), opts);
    let Dq = new Q(lcdQ);
    const Df = [...lcd.values()].map(({ base, e }) => ({ base, e }));
    if (opts.cancel !== false) {
        // numeric content
        const c = contentOf(termsOf(N));
        const g = bigGcd(c.n, Dq.n);
        if (g > 1n) {
            N = C.mul([num(new Q(1n, g)), N]);
            Dq = Dq.div(new Q(g));
        }
        // polynomial factors of the denominator that divide the numerator (one variable)
        const vars = freeVars(N);
        if (vars.length <= 1) {
            const v = vars[0] ?? freeVars(C.mul(Df.map((f) => f.base)))[0];
            let PN = v ? Poly.fromNode(N, v) : null;
            if (PN && !PN.isZero()) {
                let changed = false;
                for (const f of Df) {
                    const PB = Poly.fromNode(f.base, v);
                    if (!PB || PB.degree < 1 || !f.e.isInt()) continue;
                    while (f.e.isPos()) {
                        const { q, r } = PN.divmod(PB);
                        if (!r.isZero()) break;
                        PN = q;
                        f.e = f.e.sub(Q.ONE);
                        changed = true;
                    }
                }
                if (changed) N = PN.toNode(v);
            }
        }
    }
    const D = C.mul([num(Dq), ...Df.filter((f) => !f.e.isZero()).map((f) => C.pow(f.base, num(f.e)))]);
    if (isNum(D) && D.value.isOne()) return N;
    return div(N, D);
}

/**
 * One fraction P/Q over the common denominator (a `div` node; a plain node when the denominator is 1).
 * P is expanded, Q stays factored; common numeric factors, and polynomial factors of Q that divide P
 * (one variable), are cancelled unless {cancel: false}. Relations and lists are handled side by side.
 */
export function combineFractions(node, opts = {}) {
    const C = canonContext(opts);
    const s = C.simplify(node);
    if (s.type === 'rel') return Object.freeze({ type: 'rel', op: s.op, lhs: combine(s.lhs, C, opts), rhs: combine(s.rhs, C, opts) });
    if (s.type === 'list' || s.type === 'chain') {
        const items = Object.freeze(s.items.map((x) => combine(x, C, opts)));
        return Object.freeze(s.type === 'list' ? { type: 'list', items } : { type: 'chain', items, ops: s.ops });
    }
    return combine(s, C, opts);
}

/** Alias of combineFractions (bring to one fraction P/Q). */
export function rationalize(node, opts = {}) {
    return combineFractions(node, opts);
}

/** {num, den} of an expression brought to one fraction (canonical nodes; den = 1 when there is no fraction). */
export function numDen(node, opts = {}) {
    const C = canonContext(opts);
    const s = C.simplify(node);
    if (s.type === 'add') {
        const r = combineFractions(s, opts);
        return r.type === 'div' ? { num: r.num, den: r.den } : { num: r, den: N1 };
    }
    const { coef, rest } = splitCoeff(s);
    const factors = rest === null ? [] : rest.type === 'mul' ? rest.args : [rest];
    const top = [num(new Q(coef.n))];
    const bottom = [num(new Q(coef.d))];
    for (const f of factors) {
        if (f.type === 'pow' && isNum(f.exp) && f.exp.value.isNeg()) bottom.push(C.pow(f.base, num(f.exp.value.neg())));
        else top.push(f);
    }
    return { num: C.mul(top), den: C.mul(bottom) };
}
