// core/fractions — bring an expression to one fraction P/Q: the common denominator (polynomial denominators factored
// over Q first, so it is the least one), the numerator expanded, common factors cancelled.

import { splitCoeff, canonContext } from './simplify.js';
import { bigGcd, bigLcm, Q } from './rational.js';
import { freeVars, containsVar, nodeKey, num, div, summands } from './ast.js';
import { Poly } from './poly.js';
import { expand } from './expand.js';

const N1 = num(1);
const isNum = (n) => n.type === 'num';

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
    const terms = summands(s);
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
        const c = contentOf(summands(N));
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
