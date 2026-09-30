// simplify — canonical form and automatic simplification.
//
// Canonical form (what simplify() returns and what canon* constructors keep):
//   * num values are exact Q (no raw), negative numbers are allowed
//   * add / mul are n-ary and flat; a mul has at most one num, first; like terms and like bases are merged
//   * no div, no neg, no sqrt/root/exp/cbrt: a/b → a·b^(−1), −a → (−1)·a, √x → x^(1/2), exp x → e^x
//   * numeric radicals are m^(1/q) with an integer m ≥ 2 free of q-th powers (√12 → 2√3, 2^(2/3) → ∛4),
//     denominators rationalised (1/√2 → √2/2); √2·√3 → √6; radicals of positive constants with the same
//     exponent ±1/q merge: √2·√π → (2π)^(1/2), 1/(√π·√e) → (πe)^(−1/2)
//   * trig of x + kπ/2 by the reduction formulas: sin(π − x) → sin x, cos(x + π/2) → −sin x, tg(x + π) → tg x
//   * a numeric coefficient times a single sum is distributed: 2(x+1) → 2x + 2 (so x+1−(x+1) → 0)
//   * term order: polynomial-like by degree in the main variable (x, then y, z, t, else the first
//     alphabetically), then total degree, then alphabetical; constants last (rational, radicals, π, i);
//     factor order: number, radicals, π, i, letters, e^…, functions, sums
//   * (x^a)^b → x^(ab) only when b is an integer, or when it is safe for real x (x^(2k))^(1/2) → |x|^k, etc.
//   * i^2 = −1 always; √−4 → 2i, (1+2i)(3−i) → 5+5i, 1/(1+i) → (1−i)/2 only with {complex: true}
//   * x^0 → 1 (also 0^0), 0·anything → 0, x/x → 1 (removable points are not tracked)
// simplify is idempotent, never expands products of sums (see expand.js), and has a work budget:
// runaway inputs throw MathError('too-big'). Explicit division by zero throws MathError('div0').

import { Q, MathError, rootExtract, bigIroot, bigBitLength, bigGcd, bigLcm } from './rational.js';
import { num, sym, isConst, nodeKey, freeVars, nodeSome } from './ast.js';
import { evaluate } from './evaluate.js';
import { msg } from '../i18n/index.js';

const freeze = Object.freeze;
const N0 = num(0);
const N1 = num(1);
const NM1 = num(-1);
const HALF = num(Q.HALF);
const PI = sym('pi');
const E = sym('e');
const I = sym('i');

const mkAdd = (args) => freeze({ type: 'add', args: freeze(args) });
const mkMul = (args) => freeze({ type: 'mul', args: freeze(args) });
const mkPow = (b, e) => freeze({ type: 'pow', base: b, exp: e });
const mkFn = (name, args) => freeze({ type: 'fn', name, args: freeze(args) });

const isNum = (n) => n.type === 'num';
const isC = (n, name) => n.type === 'sym' && !n.var && n.name === name;
const isZeroNode = (n) => isNum(n) && n.value.isZero();

const DIV0 = msg('core.simplify.division_by_zero');
const TOO_BIG = msg('core.simplify.expression_is_too_large_to_simplify');
const BUDGET = 200000;

function makeCtx(opts = {}) {
    return { complex: !!opts.complex, mainVar: opts.mainVar ?? null, ops: 0, budget: opts.budget ?? BUDGET, memo: new Map() };
}

function tick(ctx) {
    if (++ctx.ops > ctx.budget) throw new MathError(TOO_BIG, null, null, 'too-big');
}

// ---------------------------------------------------------------- ordering

function natCmp(a, b) {
    if (a === b) return 0;
    const ra = a.match(/\d+|\D+/g) ?? [];
    const rb = b.match(/\d+|\D+/g) ?? [];
    for (let k = 0; k < Math.min(ra.length, rb.length); k++) {
        const x = ra[k];
        const y = rb[k];
        if (x === y) continue;
        const dx = /^\d/.test(x);
        const dy = /^\d/.test(y);
        if (dx && dy) return Number(x) - Number(y) || (x < y ? -1 : 1);
        return x < y ? -1 : 1;
    }
    return ra.length - rb.length;
}

// sin before cos before tan…, then other names alphabetically
const FN_RANK = { sin: 1, cos: 2, tan: 3, cot: 4, sec: 5, csc: 6 };
function sortKey(node) {
    return nodeKey(node).replace(/(^|[^a-z_])(sin|cos|tan|cot|sec|csc)\(/g, (m, p, f) => `${p}\u0001${FN_RANK[f]}${f}(`);
}

function factorRank(f) {
    if (f.type === 'num') return [0, ''];
    const b = f.type === 'pow' ? f.base : f;
    if (b.type === 'num') return isNum(f.exp ?? N1) ? [1, nodeKey(f)] : [5, nodeKey(f)];
    if (isConstRadical(f)) return [1.5, nodeKey(f)]; // √(2π) right after the numeric radicals
    if (b.type === 'sym') {
        if (isConst(b)) {
            if (b.name === 'pi') return [2, ''];
            if (b.name === 'e') return f.type === 'pow' ? [5, nodeKey(f.exp)] : [2.5, ''];
            if (b.name === 'inf') return [2.7, ''];
            return [3, '']; // i
        }
        return [4, b.name];
    }
    if (b.type === 'fn') return [6, sortKey(b)];
    if (b.type === 'add') return [7, nodeKey(b)];
    return [8, nodeKey(b)];
}

function compareFactors(a, b) {
    const [ra, ka] = factorRank(a);
    const [rb, kb] = factorRank(b);
    if (ra !== rb) return ra - rb;
    return natCmp(ka, kb);
}

const INFO = new WeakMap();

function termInfo(t) {
    let info = INFO.get(t);
    if (info) return info;
    const { rest } = splitCoeff(t);
    const deg = new Map();
    let total = Q.ZERO;
    let nonpoly = 0;
    let hasVar = false;
    let constRank = 0;
    const factors = rest === null ? [] : rest.type === 'mul' ? rest.args : [rest];
    for (const f of factors) {
        const b = f.type === 'pow' ? f.base : f;
        const e = f.type === 'pow' ? f.exp : N1;
        if (b.type === 'sym' && !isConst(b) && isNum(e)) {
            deg.set(b.name, (deg.get(b.name) ?? Q.ZERO).add(e.value));
            total = total.add(e.value);
            hasVar = true;
        } else if (freeVars(f).length) {
            hasVar = true;
            nonpoly++;
        } else if (isC(b, 'i')) constRank = Math.max(constRank, 4);
        else if (isC(b, 'pi') || isC(b, 'e') || isConstRadical(f)) constRank = Math.max(constRank, 2);
        else if (b.type === 'num') constRank = Math.max(constRank, 1);
        else constRank = Math.max(constRank, 3);
    }
    info = { deg, total, nonpoly, hasVar, constRank, key: rest ? sortKey(rest) : '' };
    INFO.set(t, info);
    return info;
}

/** Display order of two canonical terms of a sum (negative: a first). */
export function compareTerms(a, b, mainVar = null) {
    const A = termInfo(a);
    const B = termInfo(b);
    if (A.hasVar !== B.hasVar) return A.hasVar ? -1 : 1;
    if (!A.hasVar) {
        if (A.constRank !== B.constRank) return A.constRank - B.constRank;
        return natCmp(A.key, B.key);
    }
    if (mainVar) {
        const c = (B.deg.get(mainVar) ?? Q.ZERO).cmp(A.deg.get(mainVar) ?? Q.ZERO);
        if (c) return c;
    }
    const ct = B.total.cmp(A.total);
    if (ct) return ct;
    const names = [...new Set([...A.deg.keys(), ...B.deg.keys()])].sort(natCmp);
    for (const v of names) {
        const c = (B.deg.get(v) ?? Q.ZERO).cmp(A.deg.get(v) ?? Q.ZERO);
        if (c) return c;
    }
    if (A.nonpoly !== B.nonpoly) return A.nonpoly - B.nonpoly;
    return natCmp(A.key, B.key);
}

const MAIN_PREF = ['x', 'y', 'z', 't'];

function pickMainVar(terms, ctx) {
    const vars = new Set();
    for (const t of terms) for (const v of freeVars(t)) vars.add(v);
    if (ctx.mainVar && vars.has(ctx.mainVar)) return ctx.mainVar;
    for (const v of MAIN_PREF) if (vars.has(v)) return v;
    return [...vars].sort(natCmp)[0] ?? null;
}

// ---------------------------------------------------------------- helpers

/** Split a canonical term into its rational coefficient and the rest (null for a pure number). */
export function splitCoeff(t) {
    if (t.type === 'num') return { coef: t.value, rest: null };
    if (t.type === 'mul' && t.args[0].type === 'num') {
        const rest = t.args.length === 2 ? t.args[1] : mkMul(t.args.slice(1));
        return { coef: t.args[0].value, rest };
    }
    return { coef: Q.ONE, rest: t };
}

function scale(c, rest) {
    if (rest === null) return num(c);
    if (c.isOne()) return rest;
    if (rest.type === 'mul') return mkMul([num(c), ...rest.args]);
    return mkMul([num(c), rest]);
}

function negLead(x) {
    return (isNum(x) && x.value.isNeg()) || (x.type === 'mul' && isNum(x.args[0]) && x.args[0].value.isNeg());
}

// Radicals of positive constants merge into one: √2·√π → √(2π), 1/(√π·√e) → 1/√(πe).
// Atoms: integers ≥ 2 (already free of q-th powers in canonical radicals), π, e.
const isPosConstAtom = (n) => (isNum(n) && n.value.isInt() && n.value.gt(1)) || isC(n, 'pi') || isC(n, 'e');
const isUnitRadicalExp = (e) => isNum(e) && !e.value.isInt() && (e.value.n === 1n || e.value.n === -1n);

/** (2π)^(1/2), (πe)^(−1/2): a merged radical of positive constants (canonical form keeps it whole). */
function isConstRadical(f) {
    return f.type === 'pow' && f.base.type === 'mul' && isUnitRadicalExp(f.exp) && f.base.args.every(isPosConstAtom);
}

// √(2π) → [√2, √π] while multiplying: the parts may meet other factors (√(2π)·√2 = 2√π, √(3π)/π = √3/√π)
function splitConstRadical(f, ctx) {
    const out = [];
    for (const a of f.base.args) {
        const p = isNum(a) ? numPow(a.value, f.exp.value, ctx) : mkPow(a, f.exp);
        if (p.type === 'mul') out.push(...p.args);
        else out.push(p);
    }
    return out;
}

/** Surely positive for real values of the variables (π, e, positive numbers, e^…, products of those). */
const hasI = (n) => nodeSome(n, (m) => isC(m, 'i'));

function isPositive(n) {
    if (isNum(n)) return n.value.isPos();
    if (isC(n, 'pi') || isC(n, 'e')) return true;
    if (n.type === 'pow') return isPositive(n.base) && !hasI(n.exp);
    if (n.type === 'mul') return n.args.every(isPositive);
    if (n.type === 'fn') return n.name === 'cosh' || n.name === 'exp';
    return false;
}

/** Real numeric value of a constant expression (no variables, no i), else null. */
function constValue(n) {
    if (freeVars(n).length || nodeSome(n, (m) => isC(m, 'i') || isC(m, 'inf'))) return null;
    try {
        const v = evaluate(n);
        return Number.isFinite(v) ? v : null;
    } catch {
        return null;
    }
}

/** a + b·i with rational a, b (b may be 0), else null. */
function gaussian(n) {
    if (isNum(n)) return { re: n.value, im: Q.ZERO };
    if (isC(n, 'i')) return { re: Q.ZERO, im: Q.ONE };
    if (n.type === 'mul' && n.args.length === 2 && isNum(n.args[0]) && isC(n.args[1], 'i')) return { re: Q.ZERO, im: n.args[0].value };
    if (n.type === 'add') {
        let re = Q.ZERO;
        let im = Q.ZERO;
        for (const t of n.args) {
            const g = gaussian(t);
            if (!g || t.type === 'add') return null;
            re = re.add(g.re);
            im = im.add(g.im);
        }
        return { re, im };
    }
    return null;
}

function gaussianNode(g, ctx) {
    const im = g.im.isZero() ? N0 : g.im.isOne() ? I : mkMul([num(g.im), I]);
    return cAdd([num(g.re), im], ctx);
}

function gMul(a, b) {
    return { re: a.re.mul(b.re).sub(a.im.mul(b.im)), im: a.re.mul(b.im).add(a.im.mul(b.re)) };
}

/** Principal square root of a Gaussian rational a + bi (b ≠ 0) when it is again Gaussian rational, else null. */
function gaussSqrt(g) {
    const r = g.re.mul(g.re).add(g.im.mul(g.im)).exactRoot(2);
    if (!r) return null;
    const p = r.add(g.re).div(2).exactRoot(2);
    const q = r.sub(g.re).div(2).exactRoot(2);
    if (!p || !q) return null;
    return { re: p, im: g.im.isNeg() ? q.neg() : q };
}

function gInv(a) {
    const d = a.re.mul(a.re).add(a.im.mul(a.im));
    if (d.isZero()) throw new MathError(DIV0, null, null, 'div0');
    return { re: a.re.div(d), im: a.im.neg().div(d) };
}

/**
 * A canonical sum as c·s: c rational, s with coprime integer-ish coefficients and a positive first term.
 * Returns null when c = 1.
 */
function sumContent(b, ctx) {
    let g = 0n;
    let l = 1n;
    for (const t of b.args) {
        const { coef } = splitCoeff(t);
        g = bigGcd(g, coef.n);
        l = bigLcm(l, coef.d);
    }
    if (g === 0n) return null;
    let c = new Q(g, l);
    if (splitCoeff(b.args[0]).coef.isNeg()) c = c.neg();
    if (c.isOne()) return null;
    const inv = c.inv();
    const terms = b.args.map((t) => {
        const { coef, rest } = splitCoeff(t);
        return scale(coef.mul(inv), rest);
    });
    return { c, s: cAdd(terms, ctx) };
}

// ---------------------------------------------------------------- sums

function cAdd(terms, ctx) {
    tick(ctx);
    const flat = [];
    for (const t of terms) {
        if (t.type === 'add') flat.push(...t.args);
        else flat.push(t);
    }
    let k = Q.ZERO;
    const groups = new Map();
    for (const t of flat) {
        if (t.type === 'num') {
            k = k.add(t.value);
            continue;
        }
        const { coef, rest } = splitCoeff(t);
        const key = nodeKey(rest);
        const g = groups.get(key);
        if (g) g.coef = g.coef.add(coef);
        else groups.set(key, { coef, rest });
    }
    // sin²u + cos²u = 1 (equal coefficients)
    for (const g of groups.values()) {
        const r = g.rest;
        if (g.coef.isZero() || r.type !== 'pow' || !isNum(r.exp) || !r.exp.value.eq(2) || r.base.type !== 'fn' || r.base.name !== 'sin') continue;
        const other = groups.get(nodeKey(mkPow(mkFn('cos', r.base.args), r.exp)));
        if (other && other.coef.eq(g.coef)) {
            k = k.add(g.coef);
            g.coef = Q.ZERO;
            other.coef = Q.ZERO;
        }
    }
    const out = [];
    for (const g of groups.values()) if (!g.coef.isZero()) out.push(scale(g.coef, g.rest));
    if (!k.isZero()) out.push(num(k));
    if (!out.length) return N0;
    if (out.length === 1) return out[0];
    const mv = pickMainVar(out, ctx);
    out.sort((a, b) => compareTerms(a, b, mv));
    // constants only: √2 − 1 rather than −1 + √2 (but −1 + i stays in the a + bi order)
    if (isNum(out[0]) && out[0].value.isNeg() && !negLead(out[1]) && out.every((t) => !termInfo(t).hasVar && termInfo(t).constRank < 4)) {
        out.push(out.shift());
    }
    return mkAdd(out);
}

// ---------------------------------------------------------------- products

// Radicals of positive constants with the same exponent ±1/q merge: √2·√π → √(2π), √π·√e → √(πe).
function mergeConstRadicals(out, coef) {
    if (out.length < 2) return { out, coef };
    const byExp = new Map();
    for (const f of out) {
        if (f.type !== 'pow' || !isUnitRadicalExp(f.exp) || !isPosConstAtom(f.base)) continue;
        const k = f.exp.value.toString();
        if (!byExp.has(k)) byExp.set(k, []);
        byExp.get(k).push(f);
    }
    const merged = new Set();
    const add = [];
    for (const fs of byExp.values()) {
        const e = fs[0].exp.value;
        // 1/√(2π) rather than √2/(2√π): a numeric √m whose m divides the coefficient's denominator joins
        // the constants under the root in the denominator (q = 2 only; an alone √m stays rationalised)
        if (e.eq(new Q(-1n, 2n)) && fs.some((f) => !isNum(f.base))) {
            const pos = byExp.get('1/2');
            if (pos && pos.length === 1 && isNum(pos[0].base) && coef.d % pos[0].base.value.n === 0n) {
                const m = pos[0].base.value.n;
                coef = coef.mul(new Q(m));
                merged.add(pos[0]);
                fs.push(mkPow(num(m), fs[0].exp));
                byExp.delete('1/2');
            }
        }
        if (fs.length < 2 || fs.every((f) => isNum(f.base))) continue;
        for (const f of fs) merged.add(f);
        const bases = fs.map((f) => f.base).sort(compareFactors);
        add.push(mkPow(mkMul(bases), fs[0].exp));
    }
    if (merged.size) out = [...out.filter((f) => !merged.has(f)), ...add];
    return { out, coef };
}

function cMul(factors, ctx) {
    tick(ctx);
    let list = [];
    for (const f of factors) {
        if (f.type === 'mul') list.push(...f.args);
        else if (isConstRadical(f)) list.push(...splitConstRadical(f, ctx));
        else list.push(f);
    }
    let coef = Q.ONE;
    let out = [];
    for (let iter = 0; iter < 8; iter++) {
        coef = Q.ONE;
        const groups = new Map();
        for (const f of list) {
            if (f.type === 'num') {
                coef = coef.mul(f.value);
                continue;
            }
            const base = f.type === 'pow' ? f.base : f;
            const exp = f.type === 'pow' ? f.exp : N1;
            const key = nodeKey(base);
            const g = groups.get(key);
            if (g) g.exps.push(exp);
            else groups.set(key, { base, exps: [exp], orig: f });
        }
        if (coef.isZero()) return N0;
        out = [];
        let again = false;
        const radicals = new Map();
        for (const g of groups.values()) {
            let p;
            if (g.exps.length === 1) p = g.orig;
            else {
                p = cPow(g.base, cAdd(g.exps, ctx), ctx);
                // the merged power may have a new base (|x|^(−2) → x^(−2)) that meets another factor (x):
                // group again, or x·|x|^(−2) would stay x·x^(−2) and a second simplify would change it
                const pb = p.type === 'pow' ? p.base : p;
                if (p.type !== 'num' && p.type !== 'mul' && nodeKey(pb) !== nodeKey(g.base)) again = true;
            }
            if (p.type === 'num') {
                coef = coef.mul(p.value);
                if (coef.isZero()) return N0;
                continue;
            }
            if (p.type === 'pow' && isNum(p.base) && isNum(p.exp) && p.base.value.isInt() && p.base.value.gt(1) && p.exp.value.n === 1n && p.exp.value.d > 1n) {
                const q = p.exp.value.d;
                const r = radicals.get(q);
                if (r) {
                    r.m *= p.base.value.n;
                    r.count++;
                } else radicals.set(q, { m: p.base.value.n, count: 1, node: p });
                continue;
            }
            if (p.type === 'mul') {
                again = true;
                out.push(...p.args);
                continue;
            }
            if (isConstRadical(p)) {
                // merged radicals are merged again at the very end, after their parts met the other factors
                again = true;
                out.push(...splitConstRadical(p, ctx));
                continue;
            }
            out.push(p);
        }
        for (const [q, r] of radicals) {
            if (r.count === 1) {
                out.push(r.node);
                continue;
            }
            const p = numPow(new Q(r.m), new Q(1n, q), ctx);
            if (p.type === 'num') coef = coef.mul(p.value);
            else if (p.type === 'mul') {
                for (const a of p.args) {
                    if (a.type === 'num') coef = coef.mul(a.value);
                    else out.push(a);
                }
            } else out.push(p);
        }
        // √2·√3 → √6 may now meet ∜6 from the other index: group by base once more (√6·∜6 = ∜216)
        if (radicals.size > 1 && [...radicals.values()].some((r) => r.count > 1)) again = true;
        if (!again) break;
        list = coef.isOne() ? out : [num(coef), ...out];
    }
    // complex numbers a+bi multiply out when asked
    if (ctx.complex) {
        const gs = [];
        const rest = [];
        let hasI = false;
        for (const f of out) {
            const gf = f.type === 'add' ? gaussian(f) : null;
            if (gf) gs.push(gf);
            else if (isC(f, 'i') && !hasI) hasI = true;
            else rest.push(f);
        }
        if (gs.length >= 2 || (gs.length === 1 && hasI)) {
            let acc = { re: coef, im: Q.ZERO };
            for (const g of gs) acc = gMul(acc, g);
            if (hasI) acc = gMul(acc, { re: Q.ZERO, im: Q.ONE });
            const gn = gaussianNode(acc, ctx);
            return rest.length ? cMul([...rest, gn], ctx) : gn;
        }
    }
    if (!out.length) return num(coef);
    // 2y(x + 1) rather than y(2x + 2): pull the numeric content out of sums that share the product
    if (out.length > 1 && out.some((f) => f.type === 'add')) {
        let pulled = false;
        out = out.map((f) => {
            if (f.type !== 'add') return f;
            const sc = sumContent(f, ctx);
            if (!sc) return f;
            coef = coef.mul(sc.c);
            pulled = true;
            return sc.s;
        });
        // (3x + 3)·(x + 1)^(−1): the sum became x + 1 and now meets its own power — multiply once more
        if (pulled) {
            const keys = out.map((f) => nodeKey(f.type === 'pow' ? f.base : f));
            if (new Set(keys).size < keys.length) return cMul([num(coef), ...out], ctx);
        }
    }
    // radicals of positive constants with the same exponent ±1/q merge (last: the coefficient is final)
    ({ out, coef } = mergeConstRadicals(out, coef));
    out.sort(compareFactors);
    if (out.length === 1 && out[0].type === 'add' && !coef.isOne()) {
        return cAdd(out[0].args.map((t) => cMul([num(coef), t], ctx)), ctx);
    }
    if (coef.isOne()) return out.length === 1 ? out[0] : mkMul(out);
    return mkMul([num(coef), ...out]);
}

// ---------------------------------------------------------------- powers

function radicalNode(m, q) {
    if (m === 1n) return null;
    for (let g = Number(q); g >= 2; g--) {
        const G = BigInt(g);
        if (q % G !== 0n) continue;
        const r = bigIroot(m, g);
        if (r ** G === m) return radicalNode(r, q / G);
    }
    if (q === 1n) return num(m);
    return mkPow(num(m), num(new Q(1n, q)));
}

function numPow(a, E, ctx) {
    if (E.isInt()) {
        if (a.isZero() && E.isNeg()) throw new MathError(DIV0, null, null, 'div0');
        if (a.isZero() || a.isOne()) return num(a);
        if (a.eq(-1)) return E.n % 2n === 0n ? N1 : NM1;
        const eb = bigBitLength(E.n);
        const bits = Math.max(bigBitLength(a.n), bigBitLength(a.d)) * (eb > 40 ? Infinity : Number(E.abs().n));
        if (bits > 20000) return mkPow(num(a), num(E));
        return num(a.pow(E.n));
    }
    if (a.isZero()) {
        if (E.isNeg()) throw new MathError(DIV0, null, null, 'div0');
        return N0;
    }
    if (a.isOne()) return N1;
    const p = E.n;
    const q = E.d;
    if (a.isNeg()) {
        if (q % 2n === 1n) {
            const r = numPow(a.neg(), E, ctx);
            return p % 2n === 0n ? r : cMul([NM1, r], ctx);
        }
        if (ctx.complex && q === 2n) return cMul([cPow(I, num(p), ctx), numPow(a.neg(), E, ctx)], ctx);
        return mkPow(num(a), num(E));
    }
    if (q > 1000n) return mkPow(num(a), num(E));
    const k = E.floor();
    const s = p - k.n * q;
    const n = a.n;
    const d = a.d;
    const bitsM = bigBitLength(n) * Number(s) + bigBitLength(d) * Number(q - s);
    const kk = k.n < 0n ? -k.n : k.n;
    const bitsK = Math.max(bigBitLength(n), bigBitLength(d)) * (kk > 100000n ? Infinity : Number(kk));
    if (bitsM > 4000 || bitsK > 20000) return mkPow(num(a), num(E));
    const m = n ** s * d ** (q - s);
    const { out, in: inn } = rootExtract(m, Number(q));
    const coef = a.pow(k.n).mul(new Q(out, d));
    const rad = radicalNode(inn, q);
    if (!rad) return num(coef);
    if (rad.type === 'num') return num(coef.mul(rad.value));
    return coef.isOne() ? rad : mkMul([num(coef), rad]);
}

/** t = k·log_b(y) (k rational, also lg for b = 10 and ln for b = e) → {k, y}, else null. */
function logOfBase(t, b) {
    let k = Q.ONE;
    let f = t;
    if (t.type === 'mul' && t.args.length === 2 && isNum(t.args[0])) {
        k = t.args[0].value;
        f = t.args[1];
    }
    if (f.type !== 'fn') return null;
    if (isC(b, 'e')) return f.name === 'ln' ? { k, y: f.args[0] } : null;
    if (f.name === 'lg' && b.value.eq(10)) return { k, y: f.args[0] };
    if (f.name === 'log' && isNum(f.args[0]) && f.args[0].value.eq(b.value)) return { k, y: f.args[1] };
    return null;
}

function cPow(b, e, ctx) {
    tick(ctx);
    if (isNum(e)) {
        const X = e.value;
        if (X.isZero()) return N1;
        if (X.isOne()) return b;
        if (isNum(b)) return numPow(b.value, X, ctx);
        if (isC(b, 'i') && X.isInt()) {
            const k = Number(((X.n % 4n) + 4n) % 4n);
            return [N1, I, NM1, mkMul([NM1, I])][k];
        }
        if (isC(b, 'inf')) return X.isPos() ? b : N0;
        if (b.type === 'pow') {
            if (X.isInt()) return cPow(b.base, cMul([b.exp, e], ctx), ctx);
            if (isNum(b.exp)) {
                const e1 = b.exp.value;
                const prod = e1.mul(X);
                if (e1.n % 2n === 0n && !isPositive(b.base)) return cPow(cFn('abs', [b.base], ctx), num(prod), ctx);
                return cPow(b.base, num(prod), ctx);
            }
            if (isPositive(b.base)) return cPow(b.base, cMul([b.exp, e], ctx), ctx);
            return mkPow(b, e);
        }
        if (ctx.complex && (b.type === 'add' || b.type === 'mul') && X.d === 2n) {
            // √(a + bi) of a Gaussian rational, exactly when it is one: √(3 + 4i) = 2 + i (principal root)
            const g = gaussian(b);
            const r = g && !g.im.isZero() ? gaussSqrt(g) : null;
            if (r) return cPow(gaussianNode(r, ctx), num(new Q(X.n)), ctx);
        }
        if (b.type === 'mul') {
            if (X.isInt()) return cMul(b.args.map((f) => cPow(f, e, ctx)), ctx);
            const pulled = [];
            const rest = [];
            let sign = false;
            for (const f of b.args) {
                if (isNum(f) && f.value.isNeg() && X.d % 2n === 1n && !hasI(b)) {
                    pulled.push(num(f.value.neg()));
                    if (X.n % 2n !== 0n) sign = !sign;
                } else if (isPositive(f)) pulled.push(f);
                else rest.push(f);
            }
            if (!pulled.length) return mkPow(b, e);
            const parts = pulled.map((f) => cPow(f, e, ctx));
            if (rest.length) parts.push(cPow(rest.length === 1 ? rest[0] : cMul(rest, ctx), e, ctx));
            if (sign) parts.push(NM1);
            return cMul(parts, ctx);
        }
        if (b.type === 'fn' && b.name === 'abs' && X.n % 2n === 0n && X.d % 2n === 1n && !hasI(b)) return cPow(b.args[0], e, ctx);
        if (b.type === 'add' && !(ctx.complex && gaussian(b))) {
            // (2x + 2)^n = 2^n (x + 1)^n; (−x − 1)^2 = (x + 1)^2; fractional powers take only a positive content
            const sc = sumContent(b, ctx);
            if (sc && (X.isInt() || sc.c.isPos())) return cMul([numPow(sc.c, X, ctx), cPow(sc.s, e, ctx)], ctx);
            if (sc && !sc.c.abs().isOne()) return cMul([numPow(sc.c.abs(), X, ctx), cPow(cMul([NM1, sc.s], ctx), e, ctx)], ctx);
        }
        if (ctx.complex && X.isInt() && b.type === 'add') {
            const g = gaussian(b);
            if (g && !g.im.isZero() && X.abs().le(256)) {
                let r = { re: Q.ONE, im: Q.ZERO };
                const base = X.isNeg() ? gInv(g) : g;
                for (let k = 0n; k < (X.n < 0n ? -X.n : X.n); k++) r = gMul(r, base);
                return gaussianNode(r, ctx);
            }
        }
        return mkPow(b, e);
    }
    // symbolic exponent
    // a^(k·log_a y + …) = y^k · a^(…): 2^(log_2 3 + log_2 5) = 15, e^(2 ln x + 1) = x²·e
    if ((isNum(b) && b.value.isPos() && !b.value.isOne()) || isC(b, 'e')) {
        const terms = e.type === 'add' ? e.args : [e];
        const logs = [];
        const rest = [];
        for (const t of terms) {
            const L = logOfBase(t, b);
            if (L) logs.push(L);
            else rest.push(t);
        }
        if (logs.length && (e.type === 'add' || !logs[0].k.isOne())) {
            const parts = logs.map(({ k, y }) => cPow(y, num(k), ctx));
            if (rest.length) parts.push(cPow(b, rest.length === 1 ? rest[0] : cAdd(rest, ctx), ctx));
            return cMul(parts, ctx);
        }
    }
    if (isNum(b)) {
        if (b.value.isOne()) return N1;
        if (e.type === 'fn' && e.name === 'log' && isNum(e.args[0]) && e.args[0].value.eq(b.value)) return e.args[1];
        if (e.type === 'fn' && e.name === 'lg' && b.value.eq(10)) return e.args[0];
    }
    if (isC(b, 'e')) {
        if (e.type === 'fn' && e.name === 'ln') return e.args[0];
        if (e.type === 'mul' && e.args.length === 2 && isNum(e.args[0]) && e.args[1].type === 'fn' && e.args[1].name === 'ln') return cPow(e.args[1].args[0], e.args[0], ctx);
        if (ctx.complex) {
            // Euler: e^(iθ) with θ a table multiple of π
            const f = e.type === 'mul' ? e.args : [e];
            if (f.some((x) => isC(x, 'i')) && f.some((x) => isC(x, 'pi')) && f.length <= 3 && (f.length === 2 || isNum(f[0]))) {
                const r = f.length === 3 ? f[0].value : Q.ONE;
                const c = cosPi(r, ctx);
                const s = sinPi(r, ctx);
                if (c && s) return cAdd([c, cMul([s, I], ctx)], ctx);
            }
        }
    }
    if (b.type === 'pow' && isPositive(b.base)) return cPow(b.base, cMul([b.exp, e], ctx), ctx);
    return mkPow(b, e);
}

// ---------------------------------------------------------------- functions

const SIN_TABLE = new Map();
function sinTable(r) {
    if (!SIN_TABLE.size) {
        const ctx = makeCtx();
        SIN_TABLE.set('0', N0);
        SIN_TABLE.set('1/6', HALF);
        SIN_TABLE.set('1/4', cMul([HALF, numPow(Q.TWO, Q.HALF, ctx)], ctx));
        SIN_TABLE.set('1/3', cMul([HALF, numPow(new Q(3n), Q.HALF, ctx)], ctx));
        SIN_TABLE.set('1/2', N1);
    }
    return SIN_TABLE.get(r.toString()) ?? null;
}

/** sin(rπ) for a table angle, else null. */
function sinPi(r, ctx) {
    let x = r.sub(r.div(2).floor().mul(2)); // [0, 2)
    let neg = false;
    if (x.ge(1)) {
        x = x.sub(1);
        neg = true;
    }
    if (x.gt(Q.HALF)) x = Q.ONE.sub(x);
    const v = sinTable(x);
    if (!v) return null;
    return neg ? cMul([NM1, v], ctx) : v;
}

function cosPi(r, ctx) {
    return sinPi(Q.HALF.sub(r), ctx);
}

function piMultiple(x) {
    if (isNum(x) && x.value.isZero()) return Q.ZERO;
    if (isC(x, 'pi')) return Q.ONE;
    if (x.type === 'mul' && x.args.length === 2 && isNum(x.args[0]) && isC(x.args[1], 'pi')) return x.args[0].value;
    return null;
}

const ODD = new Set(['sin', 'tan', 'cot', 'csc', 'asin', 'atan', 'sinh', 'tanh', 'coth', 'asinh', 'atanh']);
const EVEN = new Set(['cos', 'sec', 'cosh']);
const INVERSE_OF = { sin: 'asin', cos: 'acos', tan: 'atan', cot: 'acot', sinh: 'asinh', cosh: 'acosh', tanh: 'atanh' };

let INV_TABLE = null;
function invTable() {
    if (INV_TABLE) return INV_TABLE;
    const ctx = makeCtx();
    const r2 = numPow(Q.TWO, Q.HALF, ctx);
    const r3 = numPow(new Q(3n), Q.HALF, ctx);
    const v = {
        0: N0,
        half: HALF,
        s2: cMul([HALF, r2], ctx),
        s3: cMul([HALF, r3], ctx),
        one: N1,
        r3: r3,
        r33: cMul([num(new Q(1n, 3n)), r3], ctx),
    };
    const t = (pairs) => new Map(pairs.map(([node, q]) => [nodeKey(node), new Q(...q)]));
    INV_TABLE = {
        asin: t([[v[0], [0n]], [v.half, [1n, 6n]], [v.s2, [1n, 4n]], [v.s3, [1n, 3n]], [v.one, [1n, 2n]]]),
        atan: t([[v[0], [0n]], [v.r33, [1n, 6n]], [v.one, [1n, 4n]], [v.r3, [1n, 3n]]]),
        acot: t([[v[0], [1n, 2n]], [v.r3, [1n, 6n]], [v.one, [1n, 4n]], [v.r33, [1n, 3n]]]),
    };
    return INV_TABLE;
}

const piTimes = (r, ctx) => (r.isZero() ? N0 : cMul([num(r), PI], ctx));

// Reduction formulas for an argument shifted by a multiple of π/2: sin(x + 2π) → sin x, cos(π/2 − x) → sin x,
// sin(π − x) → sin x, tg(x + π) → tg x, cos(x + π/2) → −sin x. Other shifts only lose whole periods:
// sin(x + 7π/3) → sin(x + π/3), tg(x + 4π/3) → tg(x + π/3).
const QUARTER = {
    sin: [['sin', 1], ['cos', 1], ['sin', -1], ['cos', -1]],
    cos: [['cos', 1], ['sin', -1], ['cos', -1], ['sin', 1]],
    sec: [['sec', 1], ['csc', -1], ['sec', -1], ['csc', 1]],
    csc: [['csc', 1], ['sec', 1], ['csc', -1], ['sec', -1]],
    tan: [['tan', 1], ['cot', -1]],
    cot: [['cot', 1], ['tan', -1]],
};

function trigShift(name, x, ctx) {
    const k = x.args.findIndex((t) => {
        const m = piMultiple(t);
        return m !== null && !m.isZero();
    });
    if (k < 0) return null;
    const r = piMultiple(x.args[k]);
    const u = cAdd(x.args.filter((_, i) => i !== k), ctx);
    const table = QUARTER[name];
    const r2 = r.mul(2);
    if (r2.isInt()) {
        const n = BigInt(table.length);
        const [nm, s] = table[Number(((r2.n % n) + n) % n)];
        const f = cFn(nm, [u], ctx);
        return s < 0 ? cMul([NM1, f], ctx) : f;
    }
    // whole periods only: the shift goes into (−π, π] (sin, cos, sec, cosec) or (−π/2, π/2] (tg, ctg)
    const period = name === 'tan' || name === 'cot' ? Q.ONE : Q.TWO;
    let rr = r.sub(r.div(period).floor().mul(period)); // [0, period)
    if (rr.gt(period.div(2))) rr = rr.sub(period);
    if (rr.eq(r)) return null;
    return cFn(name, [cAdd([u, piTimes(rr, ctx)], ctx)], ctx);
}

function trig(name, x, ctx) {
    const r = piMultiple(x);
    if (r !== null) {
        const s = sinPi(r, ctx);
        const c = cosPi(r, ctx);
        switch (name) {
            case 'sin':
                if (s) return s;
                break;
            case 'cos':
                if (c) return c;
                break;
            case 'tan':
                if (s && c && !isZeroNode(c)) return cMul([s, cPow(c, NM1, ctx)], ctx);
                if (c && isZeroNode(c)) return mkFn(name, [x]);
                break;
            case 'cot':
                if (s && c && !isZeroNode(s)) return cMul([c, cPow(s, NM1, ctx)], ctx);
                if (s && isZeroNode(s)) return mkFn(name, [x]);
                break;
            case 'sec':
                if (c && !isZeroNode(c)) return cPow(c, NM1, ctx);
                if (c) return mkFn(name, [x]);
                break;
            case 'csc':
                if (s && !isZeroNode(s)) return cPow(s, NM1, ctx);
                if (s) return mkFn(name, [x]);
                break;
            default:
                break;
        }
        // reduction formulas: bring the angle into (0, π/2) — sin(9π/7) = −sin(2π/7), cos(5π/7) = −cos(2π/7)
        let sign = false;
        let rr;
        if (name === 'tan' || name === 'cot') {
            rr = r.sub(r.floor()); // [0, 1)
            if (rr.gt(Q.HALF)) {
                rr = Q.ONE.sub(rr);
                sign = true; // tan(π − t) = −tan t
            }
        } else {
            rr = r.sub(r.div(2).floor().mul(2)); // [0, 2)
            if (rr.ge(1)) {
                rr = rr.sub(1);
                sign = true; // sin(π + t) = −sin t, cos(π + t) = −cos t
            }
            if (rr.gt(Q.HALF)) {
                rr = Q.ONE.sub(rr);
                if (name === 'cos' || name === 'sec') sign = !sign; // cos(π − t) = −cos t
            }
        }
        if (!rr.eq(r) || sign) {
            const f = mkFn(name, [piTimes(rr, ctx)]);
            return sign ? cMul([NM1, f], ctx) : f;
        }
    }
    if (x.type === 'add') {
        const shifted = trigShift(name, x, ctx);
        if (shifted) return shifted;
    }
    if (negLead(x)) {
        const nx = cMul([NM1, x], ctx);
        if (ODD.has(name)) return cMul([NM1, cFn(name, [nx], ctx)], ctx);
        if (EVEN.has(name)) return cFn(name, [nx], ctx);
    }
    if (x.type === 'fn' && x.name === INVERSE_OF[name]) return x.args[0];
    return mkFn(name, [x]);
}

function inverseTrig(name, x, ctx) {
    const T = invTable();
    const neg = negLead(x);
    const ax = neg ? cMul([NM1, x], ctx) : x;
    const key = nodeKey(ax);
    switch (name) {
        case 'asin': {
            const r = T.asin.get(key);
            if (r) return piTimes(neg ? r.neg() : r, ctx);
            break;
        }
        case 'acos': {
            const r = T.asin.get(key);
            if (r) return piTimes(Q.HALF.sub(neg ? r.neg() : r), ctx);
            break;
        }
        case 'atan': {
            const r = T.atan.get(key);
            if (r) return piTimes(neg ? r.neg() : r, ctx);
            break;
        }
        case 'acot': {
            const r = T.acot.get(key);
            if (r) return piTimes(neg ? Q.ONE.sub(r) : r, ctx);
            break;
        }
        default:
            break;
    }
    if (neg && (name === 'asin' || name === 'atan')) return cMul([NM1, mkFn(name, [ax])], ctx);
    if (neg && (name === 'acos' || name === 'acot')) return cAdd([PI, cMul([NM1, mkFn(name, [ax])], ctx)], ctx);
    return mkFn(name, [x]);
}

function primitiveRoot(q) {
    // q = c^k with the largest k (q > 0, q ≠ 1)
    if (q.lt(1)) {
        const [c, k] = primitiveRoot(q.inv());
        return [c.inv(), k];
    }
    const bits = Math.max(bigBitLength(q.n), bigBitLength(q.d));
    if (bits > 512) return [q, 1];
    for (let k = bits; k >= 2; k--) {
        const r = q.exactRoot(k);
        if (r) return [r, k];
    }
    return [q, 1];
}

/** log_b(x) when it is rational, else null. */
function exactLog(b, x) {
    if (!b.isPos() || b.isOne() || !x.isPos()) return null;
    if (x.isOne()) return Q.ZERO;
    const [cb, kb] = primitiveRoot(b);
    const [cx, kx] = primitiveRoot(x);
    if (cb.eq(cx)) return new Q(BigInt(kx), BigInt(kb));
    if (cb.eq(cx.inv())) return new Q(BigInt(-kx), BigInt(kb));
    return null;
}

function cLog(name, base, x, ctx) {
    const mk = () => (name === 'log' ? mkFn('log', [base, x]) : mkFn(name, [x]));
    if (isNum(x) && x.value.isOne()) return N0;
    if (nodeKey(x) === nodeKey(base)) return N1;
    if (x.type === 'pow' && nodeKey(x.base) === nodeKey(base)) return x.exp;
    if (isNum(x) && isNum(base)) {
        const r = exactLog(base.value, x.value);
        if (r) return num(r);
    }
    // log of a rational power of the base times nothing else: lg(√1000) etc. handled above via pow
    return mk();
}

function cAbs(x, ctx) {
    if (isNum(x)) return num(x.value.abs());
    if (x.type === 'fn' && x.name === 'abs') return x;
    if (isPositive(x)) return x;
    if (x.type === 'pow' && isNum(x.exp) && x.exp.value.n % 2n === 0n && x.exp.value.d % 2n === 1n && !hasI(x)) return x;
    if (x.type === 'mul' && isNum(x.args[0])) {
        const c = x.args[0].value.abs();
        const rest = x.args.length === 2 ? x.args[1] : mkMul(x.args.slice(1));
        return cMul([num(c), cAbs(rest, ctx)], ctx);
    }
    if (x.type === 'mul') {
        const pos = x.args.filter(isPositive);
        if (pos.length) {
            const rest = x.args.filter((f) => !isPositive(f));
            return cMul([...pos, cAbs(rest.length === 1 ? rest[0] : mkMul(rest), ctx)], ctx);
        }
    }
    if (isC(x, 'i')) return N1;
    const g = gaussian(x);
    if (g) return cPow(num(g.re.mul(g.re).add(g.im.mul(g.im))), HALF, ctx);
    const v = constValue(x);
    if (v !== null && Math.abs(v) > 1e-12) return v > 0 ? x : cMul([NM1, x], ctx);
    return mkFn('abs', [x]);
}

function cFn(name, args, ctx) {
    tick(ctx);
    const x = args[0];
    switch (name) {
        case 'sqrt':
            return cPow(x, HALF, ctx);
        case 'cbrt':
            return cPow(x, num(new Q(1n, 3n)), ctx);
        case 'root': {
            const n = args[1];
            if (isNum(n) && n.value.isInt() && n.value.isPos()) return cPow(x, num(n.value.inv()), ctx);
            if (isNum(n) && n.value.isZero()) return mkFn('root', args);
            return cPow(x, cPow(n, NM1, ctx), ctx);
        }
        case 'exp':
            return cPow(E, x, ctx);
        case 'log': {
            const b = args[0];
            if (isNum(b) && b.value.eq(10)) return cLog('lg', num(10), args[1], ctx);
            if (isC(b, 'e')) return cLog('ln', E, args[1], ctx);
            return cLog('log', b, args[1], ctx);
        }
        case 'ln':
            return cLog('ln', E, x, ctx);
        case 'lg':
            return cLog('lg', num(10), x, ctx);
        case 'sin':
        case 'cos':
        case 'tan':
        case 'cot':
        case 'sec':
        case 'csc':
            return trig(name, x, ctx);
        case 'asin':
        case 'acos':
        case 'atan':
        case 'acot':
            return inverseTrig(name, x, ctx);
        case 'sinh':
        case 'tanh':
        case 'asinh':
        case 'atanh':
            if (isZeroNode(x)) return N0;
            if (negLead(x)) return cMul([NM1, cFn(name, [cMul([NM1, x], ctx)], ctx)], ctx);
            if (x.type === 'fn' && x.name === INVERSE_OF[name]) return x.args[0];
            return mkFn(name, [x]);
        case 'cosh':
            if (isZeroNode(x)) return N1;
            if (negLead(x)) return cFn(name, [cMul([NM1, x], ctx)], ctx);
            if (x.type === 'fn' && x.name === 'acosh') return x.args[0];
            return mkFn(name, [x]);
        case 'coth':
            if (negLead(x)) return cMul([NM1, cFn(name, [cMul([NM1, x], ctx)], ctx)], ctx);
            return mkFn(name, [x]);
        case 'acosh':
            if (isNum(x) && x.value.isOne()) return N0;
            return mkFn(name, [x]);
        case 'abs':
            return cAbs(x, ctx);
        case 'sign': {
            if (isNum(x)) return num(x.value.sign());
            if (isPositive(x)) return N1;
            const v = constValue(x);
            if (v !== null && Math.abs(v) > 1e-12) return num(Math.sign(v));
            if (negLead(x)) return cMul([NM1, cFn('sign', [cMul([NM1, x], ctx)], ctx)], ctx);
            return mkFn(name, [x]);
        }
        case 'floor':
        case 'ceil': {
            if (isNum(x)) return num(name === 'floor' ? x.value.floor() : x.value.ceil());
            const v = constValue(x);
            if (v !== null && Math.abs(v - Math.round(v)) > 1e-9 && Math.abs(v) < 1e15) return num(name === 'floor' ? Math.floor(v) : Math.ceil(v));
            return mkFn(name, [x]);
        }
        case 'fact': {
            if (isNum(x) && x.value.isInt() && !x.value.isNeg() && x.value.le(1000)) {
                let r = 1n;
                for (let k = 2n; k <= x.value.n; k++) r *= k;
                return num(r);
            }
            return mkFn(name, [x]);
        }
        default:
            return mkFn(name, args);
    }
}

// ---------------------------------------------------------------- entry points

function S(n, ctx) {
    const hit = ctx.memo.get(n);
    if (hit) return hit;
    let r;
    switch (n.type) {
        case 'num':
            r = n.raw ? num(n.value) : n;
            break;
        case 'sym':
            r = n;
            break;
        case 'add':
            r = cAdd(n.args.map((a) => S(a, ctx)), ctx);
            break;
        case 'mul':
            r = cMul(n.args.map((a) => S(a, ctx)), ctx);
            break;
        case 'div':
            r = cMul([S(n.num, ctx), cPow(S(n.den, ctx), NM1, ctx)], ctx);
            break;
        case 'neg':
            r = cMul([NM1, S(n.arg, ctx)], ctx);
            break;
        case 'pow':
            r = cPow(S(n.base, ctx), S(n.exp, ctx), ctx);
            break;
        case 'fn':
            r = cFn(n.name, n.args.map((a) => S(a, ctx)), ctx);
            break;
        case 'rel':
            r = freeze({ type: 'rel', op: n.op, lhs: S(n.lhs, ctx), rhs: S(n.rhs, ctx) });
            break;
        case 'chain':
            r = freeze({ type: 'chain', items: freeze(n.items.map((a) => S(a, ctx))), ops: n.ops });
            break;
        case 'list':
            r = freeze({ type: 'list', items: freeze(n.items.map((a) => S(a, ctx))) });
            break;
        default:
            throw new TypeError(`simplify: unknown node ${n?.type}`);
    }
    ctx.memo.set(n, r);
    return r;
}

/**
 * Canonical simplified form (see the header). opts: {complex: false, mainVar: 'x'}.
 * Throws MathError: 'div0' for an explicit division by zero, 'too-big' when the work budget runs out.
 */
export function simplify(node, opts = {}) {
    return S(node, makeCtx(opts));
}

/** Canonical sum of canonical terms (no re-simplification of the terms themselves). */
export function canonAdd(terms, opts = {}) {
    return cAdd(terms, makeCtx(opts));
}

/** Canonical product of canonical factors. */
export function canonMul(factors, opts = {}) {
    return cMul(factors, makeCtx(opts));
}

/** Canonical power of canonical base and exponent. */
export function canonPow(base, exp, opts = {}) {
    return cPow(base, exp, makeCtx(opts));
}

/** Canonical function application to canonical arguments (sqrt → power, known values, parity…). */
export function canonFn(name, args, opts = {}) {
    return cFn(name, Array.isArray(args) ? args : [args], makeCtx(opts));
}

/**
 * Bound canonical constructors sharing one work budget — for engine modules that build many nodes:
 * const C = canonContext({complex}); C.add([...]), C.mul([...]), C.pow(b, e), C.fn(name, [args]), C.simplify(node).
 */
export function canonContext(opts = {}) {
    const ctx = makeCtx(opts);
    return {
        add: (terms) => cAdd(terms, ctx),
        mul: (factors) => cMul(factors, ctx),
        pow: (b, e) => cPow(b, e, ctx),
        fn: (name, args) => cFn(name, args, ctx),
        simplify: (node) => S(node, ctx),
    };
}
