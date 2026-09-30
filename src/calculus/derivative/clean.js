// derivative/clean — the clean form: equivalent candidates (canonical, one fraction, common factor, tg/ctg) ranked
// by the length of their TeX (niceForm).

import { nodeChildren, nodeKey, freeVars, num, mul, mapNode, sym, pow, isConst, neg, add, div } from '../../core/ast.js';
import { splitCoeff, canonContext, simplify } from '../../core/simplify.js';
import { Q, bigGcd, bigLcm, MathError } from '../../core/rational.js';
import { Poly } from '../../core/poly.js';
import { expand } from '../../core/expand.js';
import { combineFractions } from '../../core/fractions.js';
import { N0, N1, NM1, agree, calcTex, isNum, negLeading, prettyForm, simp } from '../display.js';
import { DEFAULT_LANGUAGE } from '../../i18n/index.js';

// ---------------------------------------------------------------- the clean form

function hasNegPow(n) {
    if (n.type === 'pow' && isNum(n.exp) && n.exp.value.isNeg()) return true;
    return nodeChildren(n).some(hasNegPow);
}

function factorsOf(t) {
    const { coef, rest } = splitCoeff(t);
    const fs = rest === null ? [] : rest.type === 'mul' ? rest.args : [rest];
    const m = new Map();
    for (const f of fs) {
        let base = f;
        let e = Q.ONE;
        if (f.type === 'pow' && isNum(f.exp)) {
            base = f.base;
            e = f.exp.value;
        }
        const k = nodeKey(base);
        const cur = m.get(k);
        if (cur) cur.e = cur.e.add(e);
        else m.set(k, { base, e });
    }
    return { coef, m };
}

/** a·F + b·F·G → F·(a + b·G) when the common factor F holds something other than bare letters. */
function factorCommon(S, opts = {}) {
    if (S.type !== 'add' || S.args.length < 2) return null;
    const terms = S.args.map(factorsOf);
    const common = [];
    for (const [k, { base, e }] of terms[0].m) {
        let pick = e;
        let ok = true;
        for (const t of terms.slice(1)) {
            const g = t.m.get(k);
            if (!g || g.e.isNeg() !== e.isNeg()) {
                ok = false;
                break;
            }
            // positive powers: the smallest; negative powers (denominators): the smallest in absolute value
            if (e.isNeg() ? g.e.gt(pick) : g.e.lt(pick)) pick = g.e;
        }
        if (ok) common.push({ k, base, e: pick });
    }
    if (!common.length) return null;
    if (!common.some((c) => c.base.type !== 'sym' || c.e.isNeg())) return null;
    if (opts.fnFractions === false) {
        // antiderivatives: take out exponentials and radicals, keep sums of trig/log powers expanded
        const expOrRoot = (c) => (c.base.type === 'pow' && !freeVars(c.base.base).length) || !c.e.isInt();
        if (!common.some(expOrRoot) || common.some((c) => c.base.type === 'fn')) return null;
    }
    let g = 0n;
    let l = 1n;
    for (const t of terms) {
        g = bigGcd(g, t.coef.n);
        l = bigLcm(l, t.coef.d);
    }
    let content = g === 0n ? Q.ONE : new Q(g, l);
    if (terms.every((t) => t.coef.isNeg())) content = content.neg();
    const C = canonContext();
    const restTerms = terms.map((t) => {
        const fs = [num(t.coef.div(content))];
        for (const [k, { base, e }] of t.m) {
            const c = common.find((x) => x.k === k);
            const left = c ? e.sub(c.e) : e;
            if (!left.isZero()) fs.push(C.pow(base, num(left)));
        }
        return C.mul(fs);
    });
    const restSum = C.add(restTerms);
    const outer = [];
    if (!content.isOne()) outer.push(num(content));
    for (const c of common) outer.push(C.pow(c.base, num(c.e)));
    if (isNum(restSum)) return C.mul([...outer, restSum]);
    return mul([...outer, restSum]);
}

/** sin u / cos u → tg u, cos u / sin u → ctg u inside products; 1/tgᵏu → ctgᵏu. */
function trigCombine(node) {
    const C = canonContext();
    const FLIP = { tan: 'cot', cot: 'tan' };
    return mapNode(node, (m) => {
        if (m.type === 'pow' && m.base.type === 'fn' && FLIP[m.base.name] && isNum(m.exp) && m.exp.value.isNeg()) {
            return C.pow(C.fn(FLIP[m.base.name], m.base.args), num(m.exp.value.neg()));
        }
        if (m.type !== 'mul') return undefined;
        const sins = new Map();
        const coss = new Map();
        m.args.forEach((f, i) => {
            const b = f.type === 'pow' ? f.base : f;
            const e = f.type === 'pow' ? f.exp : N1;
            if (b.type !== 'fn' || !isNum(e) || !e.value.isInt()) return;
            if (b.name === 'sin') sins.set(nodeKey(b.args[0]), { i, e: e.value, arg: b.args[0] });
            if (b.name === 'cos') coss.set(nodeKey(b.args[0]), { i, e: e.value, arg: b.args[0] });
        });
        const drop = new Set();
        const extra = [];
        for (const [k, s] of sins) {
            const c = coss.get(k);
            if (!c || !s.e.add(c.e).isZero()) continue;
            drop.add(s.i);
            drop.add(c.i);
            if (s.e.isPos()) extra.push(C.pow(C.fn('tan', [s.arg]), num(s.e)));
            else extra.push(C.pow(C.fn('cot', [s.arg]), num(c.e)));
        }
        if (!drop.size) return undefined;
        return C.mul([...m.args.filter((_, i) => !drop.has(i)), ...extra]);
    });
}

/** Polynomial coefficient in its shorter form: expanded or factored (3x² + 3x → 3x(x + 1)). */
function polyShort(P, v, mode = 'short') {
    const expanded = P.toNode(v);
    if (P.degree < 1) return [expanded];
    const { constant, factors } = P.factor();
    const X = sym(v);
    // (x − a)ᵏ(x + a)ᵏ → (x² − a²)ᵏ
    const fl = factors.map((f) => ({ ...f }));
    for (const f of fl) {
        if (f.done || f.poly.degree !== 1 || !f.poly.c[1].isOne() || f.poly.c[0].isZero()) continue;
        const partner = fl.find(
            (g) => !g.done && g !== f && g.mult === f.mult && g.poly.degree === 1 && g.poly.c[1].isOne() && g.poly.c[0].eq(f.poly.c[0].neg()),
        );
        if (partner) {
            partner.done = true;
            f.poly = new Poly([f.poly.c[0].mul(partner.poly.c[0]), Q.ZERO, Q.ONE]);
        }
    }
    const fs = [];
    if (!constant.isOne()) fs.push(num(constant));
    const monos = [];
    for (const { poly, mult, done } of fl) {
        if (done) continue;
        const isX = poly.degree === 1 && poly.c[0].isZero() && poly.c[1].isOne();
        const node = isX ? X : poly.toNode(v);
        (isX ? monos : fs).push(mult === 1 ? node : pow(node, num(mult)));
    }
    fs.splice(constant.isOne() ? 0 : 1, 0, ...monos);
    if (fs.length <= 1 || factors.length === 0) return [expanded];
    if (mode === 'factored') return fs;
    const factored = mul(fs);
    return score(factored) < score(expanded) ? fs : [expanded];
}

/** Collect the terms of a sum by their non-polynomial part: 3x³cos u + 3x²cos u → 3x²(x + 1)cos u. */
function collectFns(X, v) {
    if (X.type !== 'add' || !v) return null;
    const groups = new Map();
    for (const t of X.args) {
        const { coef, rest } = splitCoeff(t);
        const fs = rest === null ? [] : rest.type === 'mul' ? rest.args : [rest];
        let deg = 0;
        const others = [];
        for (const f of fs) {
            if (f.type === 'sym' && f.name === v && !isConst(f)) deg += 1;
            else if (
                f.type === 'pow' &&
                f.base.type === 'sym' &&
                f.base.name === v &&
                !isConst(f.base) &&
                isNum(f.exp) &&
                f.exp.value.isInt() &&
                f.exp.value.isPos() &&
                f.exp.value.le(50)
            )
                deg += Number(f.exp.value.n);
            else others.push(f);
        }
        const key = others.map(nodeKey).join('*');
        let g = groups.get(key);
        if (!g) {
            g = { others, poly: new Poly([]), count: 0 };
            groups.set(key, g);
        }
        g.poly = g.poly.add(Poly.monomial(coef, deg));
        g.count++;
    }
    if (![...groups.values()].some((g) => g.others.length && g.count > 1)) return null;
    const terms = [];
    for (const g of groups.values()) {
        if (g.poly.isZero()) continue;
        const pf = g.others.length ? polyShort(g.poly, v) : [g.poly.toNode(v)];
        if (!g.others.length) {
            terms.push(pf.length === 1 ? pf[0] : mul(pf));
            continue;
        }
        // a coefficient polynomial with a negative leading term goes in with a minus: −(x⁵ − 20x³)·cos x
        if (pf.length === 1 && pf[0].type === 'add' && g.poly.lead.isNeg()) {
            const pos = polyShort(g.poly.neg(), v);
            const posLead = (pos.length === 1 && isNum(pos[0]) ? (pos[0].value.isOne() ? [] : [pos[0]]) : pos).flatMap((x) =>
                x.type === 'mul' ? x.args : [x],
            );
            terms.push(neg(mul([...posLead, ...g.others])));
            continue;
        }
        let lead = pf.length === 1 && isNum(pf[0]) ? (pf[0].value.isOne() ? [] : [pf[0]]) : pf;
        lead = lead.flatMap((x) => (x.type === 'mul' ? x.args : [x]));
        terms.push(mul([...lead, ...g.others]));
    }
    if (!terms.length) return N0;
    return terms.length === 1 ? terms[0] : add(terms);
}

export function score(n) {
    return calcTex(n, DEFAULT_LANGUAGE).replace(/\\left|\\right|\\operatorname|\s+/g, '').length;
}

/** One fraction P/Q with a readable sign (−P/Q rather than (−P)/Q); variants of P: expanded, common factor out, collected, factored. */
function fractionForms(S, v) {
    let cf;
    try {
        cf = combineFractions(S);
    } catch {
        return [];
    }
    if (cf.type !== 'div') return [];
    let N = cf.num;
    const D = cf.den;
    const allNeg = N.type === 'add' ? N.args.every(negLeading) : negLeading(N);
    const C = canonContext();
    let sign = false;
    if (allNeg) {
        sign = true;
        N = C.mul([NM1, N]);
    }
    const tops = [N];
    if (N.type === 'add') {
        for (const c of [factorCommon(N), collectFns(N, v)]) if (c) tops.push(c);
        const P = Poly.fromNode(N, v);
        if (P && P.degree >= 2) {
            const fs = polyShort(P, v, 'factored');
            if (fs.length > 1) tops.push(mul(fs));
        }
    }
    return tops.map((top) => (sign ? neg(div(top, D)) : div(top, D)));
}

/** −c·(a − b)·… → c·(b − a)·…: the minus goes into a sum factor (1 − x² rather than −(x² − 1)). */
function absorbSign(n) {
    if (n.type !== 'mul' || !isNum(n.args[0]) || !n.args[0].value.isNeg()) return null;
    const k = n.args.findIndex((f) => f.type === 'add');
    if (k < 0) return null;
    const C = canonContext();
    const flipped = C.add(n.args[k].args.map((t) => C.mul([NM1, t])));
    const c = n.args[0].value.neg();
    const rest = n.args.slice(1).map((f, i) => (i + 1 === k ? flipped : f));
    return c.isOne() ? (rest.length === 1 ? rest[0] : mul(rest)) : mul([num(c), ...rest]);
}

/**
 * The tidiest equivalent form for answers: canonical (simplify.js), expanded, one fraction, common factor
 * taken out, the minus moved into a bracket, sin/cos → tg/ctg — the shortest TeX wins, and every candidate
 * is checked numerically. Returns a display node (prettyForm). Throws MathError 'div0' for an explicit
 * division by zero.
 */
export function niceForm(node, v = null, opts = {}) {
    let S;
    try {
        S = simp(node);
    } catch (e) {
        if (e instanceof MathError && e.code === 'div0') throw e;
        return prettyForm(node);
    }
    const vv = v ?? freeVars(S)[0] ?? 'x';
    const cands = [S];
    const push = (c) => {
        if (!c) return;
        try {
            if (!cands.some((x) => nodeKey(x) === nodeKey(c))) cands.push(c);
        } catch {
            // malformed candidate — skip
        }
    };
    const tryPush = (f) => {
        try {
            push(f());
        } catch {
            // a candidate that fails to build is simply not offered
        }
    };
    // structural rewrites of the canonical form
    if (hasNegPow(S) && nodeChildren(S).some((c) => c.type !== 'num' && hasNestedFraction(c))) tryPush(() => deepCombine(S));
    tryPush(() => absFix(S));
    if (S.type === 'add' && S.args.some((t) => t.type === 'mul' && t.args.some((f) => f.type === 'add'))) {
        // a sum with bracketed products inside (u·V − ∫v du after integrating by parts): multiply out
        tryPush(() => {
            const X = simp(expand(S));
            return X.type !== 'add' || X.args.length <= 16 ? X : null;
        });
    }
    for (const c of [...cands]) {
        if (c.type === 'mul' && c.args.some((f) => f.type === 'add' || (f.type === 'pow' && f.base.type === 'add'))) {
            tryPush(() => {
                const X = simp(expand(c));
                return X.type !== 'add' || X.args.length <= 12 ? X : null;
            });
        }
    }
    try {
        for (const x of ratCandidates(S, vv)) push(x);
    } catch {
        // not a rational function
    }
    tryPush(() => logCombine(S));
    for (const c of [...cands]) {
        if (c.type !== 'add') continue;
        tryPush(() => factorCommon(c, opts));
        tryPush(() => collectFns(c, vv));
        if (hasNegPow(c)) for (const x of fractionForms(c, vv)) push(x);
    }
    // a fraction may cancel once it is canonical again ((cos x + 1)/(cos x + 1)² → 1/(cos x + 1))
    for (const c of [...cands]) if (c.type === 'div' || c.type === 'neg') tryPush(() => simp(c));
    for (const c of [...cands]) tryPush(() => absorbRadicals(c.type === 'div' || c.type === 'neg' ? simp(c) : c, vv));
    for (const c of [...cands]) tryPush(() => absorbSign(c));
    for (const c of [...cands]) {
        tryPush(() => {
            const t = trigCombine(c);
            return t !== c ? t : null;
        });
    }
    let best = S;
    let bestScore = score(S);
    for (const c of cands.slice(1)) {
        const sc = score(c) + penalty(c, opts);
        if (sc >= bestScore) continue;
        if (agree(c, S, vv, { tol: 1e-9 }).ok === false) continue;
        best = c;
        bestScore = sc;
    }
    return prettyForm(best, { fnFirst: opts.fnFractions === false });
}

// a fraction whose numerator holds a radical reads worse than the sum it came from; for antiderivatives
// (opts.fnFractions === false) the same goes for ln, arctg, … in a numerator
export function penalty(c, opts = {}) {
    const top = c.type === 'neg' ? c.arg : c;
    if (top.type === 'div' && hasRadical(top.num)) return 12;
    if (opts.fnFractions === false) {
        if (top.type === 'div' && hasFn(top.num)) return 1000;
        if (
            top.type === 'mul' &&
            top.args.some((f) => f.type === 'pow' && isNum(f.exp) && f.exp.value.isNeg()) &&
            top.args.some((f) => f.type === 'add' && hasFn(f))
        )
            return 1000;
    }
    return 0;
}

function hasFn(n) {
    if (n.type === 'fn' && n.name !== 'sqrt' && n.name !== 'root' && n.name !== 'abs') return true;
    return nodeChildren(n).some(hasFn);
}

function hasRadical(n) {
    if (n.type === 'pow' && isNum(n.exp) && !n.exp.value.isInt()) return true;
    if (n.type === 'fn' && (n.name === 'sqrt' || n.name === 'root')) return true;
    return nodeChildren(n).some(hasRadical);
}

function hasNestedFraction(n) {
    if (n.type === 'add' && hasNegPow(n)) return true;
    return nodeChildren(n).some(hasNestedFraction);
}

/** Bring every inner sum with fractions to one fraction, bottom-up (so 1/(1/x² + 1) → x²/(x² + 1)). */
function deepCombine(S) {
    return simp(
        mapNode(S, (m) => {
            if (m.type !== 'add' || !hasNegPow(m)) return undefined;
            try {
                return simplify(combineFractions(m));
            } catch {
                return undefined;
            }
        }),
    );
}

/** u^(2k)·|u|^m → |u|^(2k+m): x²/|x| = |x|. */
function absFix(S) {
    const C = canonContext();
    const out = mapNode(S, (m) => {
        if (m.type !== 'mul') return undefined;
        const abs = new Map();
        m.args.forEach((f, i) => {
            const b = f.type === 'pow' ? f.base : f;
            const e = f.type === 'pow' ? f.exp : N1;
            if (b.type === 'fn' && b.name === 'abs' && isNum(e) && e.value.isInt()) abs.set(nodeKey(b.args[0]), { i, e: e.value, b });
        });
        if (!abs.size) return undefined;
        const drop = new Set();
        const extra = [];
        m.args.forEach((f, i) => {
            const b = f.type === 'pow' ? f.base : f;
            const e = f.type === 'pow' ? f.exp : N1;
            const a = abs.get(nodeKey(b));
            if (!a || drop.has(a.i) || !isNum(e) || !e.value.isInt() || e.value.n % 2n !== 0n) return;
            drop.add(i);
            drop.add(a.i);
            extra.push(C.pow(a.b, num(a.e.add(e.value))));
        });
        if (!drop.size) return undefined;
        return C.mul([...m.args.filter((_, i) => !drop.has(i)), ...extra]);
    });
    return out === S ? null : simp(out);
}

/** Polynomial factors that are multiples of a radical's base move under it: (2 − 2x²)/√(1 − x²) → 2√(1 − x²). */
function absorbRadicals(S, v) {
    const C = canonContext();
    const out = mapNode(S, (m) => {
        if (m.type !== 'mul') return undefined;
        const rads = [];
        const polys = [];
        m.args.forEach((f, i) => {
            if (f.type === 'pow' && isNum(f.exp) && !f.exp.value.isInt()) {
                const B = f.base.type === 'add' ? Poly.fromNode(f.base, v) : null;
                if (B && B.degree >= 1) rads.push({ i, B, base: f.base, e: f.exp.value });
                return;
            }
            const isP = f.type === 'pow' && isNum(f.exp) && f.exp.value.isInt() && f.exp.value.isPos() && f.exp.value.le(20);
            const base = isP ? f.base : f;
            if (base.type !== 'add') return;
            const P = Poly.fromNode(base, v);
            if (P && P.degree >= 1) polys.push({ i, P: isP ? P.pow(Number(f.exp.value.n)) : P });
        });
        if (!rads.length || !polys.length) return undefined;
        let changed = false;
        for (const p of polys) {
            for (const r of rads) {
                while (p.P.degree >= r.B.degree) {
                    const { q, r: rem } = p.P.divmod(r.B);
                    if (!rem.isZero()) break;
                    p.P = q;
                    r.e = r.e.add(Q.ONE);
                    changed = true;
                }
            }
        }
        if (!changed) return undefined;
        const skip = new Set([...rads.map((r) => r.i), ...polys.map((p) => p.i)]);
        return C.mul([...m.args.filter((_, i) => !skip.has(i)), ...rads.map((r) => C.pow(r.base, num(r.e))), ...polys.map((p) => p.P.toNode(v))]);
    });
    return out === S ? null : simp(out);
}

/** Prime factorisation of a positive integer (trial division; a big leftover counts as one factor). */
function primeFactors(n) {
    const out = new Map();
    let m = n;
    for (let p = 2n; p * p <= m && p < 100000n; p += p === 2n ? 1n : 2n) {
        while (m % p === 0n) {
            out.set(p, (out.get(p) ?? 0n) + 1n);
            m /= p;
        }
    }
    if (m > 1n) out.set(m, (out.get(m) ?? 0n) + 1n);
    return out;
}

/** A positive numeric constant (rationals and their rational powers) as prime → exponent (Q), else null. */
function numericPrimes(x) {
    const acc = new Map();
    const addQ = (q, e) => {
        if (!q.isPos()) return false;
        for (const [p, k] of primeFactors(q.n)) acc.set(p, (acc.get(p) ?? Q.ZERO).add(e.mul(new Q(k))));
        for (const [p, k] of primeFactors(q.d)) acc.set(p, (acc.get(p) ?? Q.ZERO).sub(e.mul(new Q(k))));
        return true;
    };
    const fs = x.type === 'mul' ? x.args : [x];
    for (const f of fs) {
        if (isNum(f)) {
            if (!addQ(f.value, Q.ONE)) return null;
        } else if (f.type === 'pow' && isNum(f.base) && isNum(f.exp)) {
            if (!addQ(f.base.value, f.exp.value)) return null;
        } else return null;
    }
    return acc;
}

/** c₁·ln r₁ + c₂·ln r₂ + … with numeric rᵢ → c·ln R (½ln 2 + ½ln 3 − ½ln 4 → ½·ln(3/2)). */
function logCombine(S) {
    const terms = S.type === 'add' ? S.args : [S];
    const rest = [];
    const primes = new Map();
    let used = 0;
    for (const t of terms) {
        const { coef, rest: r } = splitCoeff(t);
        if (r && r.type === 'fn' && r.name === 'ln') {
            const f = numericPrimes(r.args[0]);
            if (f) {
                for (const [p, e] of f) primes.set(p, (primes.get(p) ?? Q.ZERO).add(e.mul(coef)));
                used++;
                continue;
            }
        }
        rest.push(t);
    }
    if (!used) return null;
    const exps = [...primes].filter(([, e]) => !e.isZero());
    const C = canonContext();
    if (!exps.length) return rest.length ? C.add(rest) : N0;
    let g = 0n;
    let l = 1n;
    for (const [, e] of exps) {
        g = bigGcd(g, e.n);
        l = bigLcm(l, e.d);
    }
    let c = new Q(g, l);
    if (exps.filter(([, e]) => e.isNeg()).length > exps.length / 2) c = c.neg();
    let R = Q.ONE;
    for (const [p, e] of exps) R = R.mul(new Q(p).pow(e.div(c).n));
    const lnR = mkLn(num(R));
    return C.add([...rest, C.mul([num(c), lnR])]);
}

const mkLn = (x) => Object.freeze({ type: 'fn', name: 'ln', args: Object.freeze([x]) });

/**
 * The expression as a rational function of v with rational coefficients, reduced: {num: Poly, den: Poly}
 * (den primitive with a positive leading coefficient), or null when it is not one (other letters, roots,
 * functions). Works on any AST (it is simplified first).
 */
export function ratFunctionOf(node, v = 'x') {
    let S;
    try {
        S = simp(node);
    } catch {
        return null;
    }
    const r = ratRec(S, v);
    if (!r) return null;
    let { p, q } = r;
    if (q.isZero()) return null;
    const g = p.isZero() ? q : p.gcd(q);
    if (g.degree > 0) {
        p = p.divmod(g).q;
        q = q.divmod(g).q;
    }
    const c = q.content();
    p = p.scale(c.inv());
    q = q.scale(c.inv());
    return { num: p, den: q };
}

function ratRec(n, v) {
    switch (n.type) {
        case 'num':
            return { p: new Poly([n.value]), q: new Poly([Q.ONE]) };
        case 'sym':
            return n.name === v && !isConst(n) ? { p: new Poly([Q.ZERO, Q.ONE]), q: new Poly([Q.ONE]) } : null;
        case 'add': {
            let acc = { p: new Poly([]), q: new Poly([Q.ONE]) };
            for (const a of n.args) {
                const r = ratRec(a, v);
                if (!r) return null;
                acc = { p: acc.p.mul(r.q).add(r.p.mul(acc.q)), q: acc.q.mul(r.q) };
                if (acc.q.degree > 80 || acc.p.degree > 80) return null;
            }
            return acc;
        }
        case 'mul': {
            let acc = { p: new Poly([Q.ONE]), q: new Poly([Q.ONE]) };
            for (const a of n.args) {
                const r = ratRec(a, v);
                if (!r) return null;
                acc = { p: acc.p.mul(r.p), q: acc.q.mul(r.q) };
                if (acc.q.degree > 80 || acc.p.degree > 80) return null;
            }
            return acc;
        }
        case 'pow': {
            if (!isNum(n.exp) || !n.exp.value.isInt() || n.exp.value.abs().gt(40)) return null;
            const b = ratRec(n.base, v);
            if (!b) return null;
            const k = Number(n.exp.value.n);
            const P = b.p.pow(Math.abs(k));
            const R = b.q.pow(Math.abs(k));
            return k >= 0 ? { p: P, q: R } : { p: R, q: P };
        }
        default:
            return null;
    }
}

function ratCandidates(S, v) {
    if (!hasNegPow(S)) return [];
    const r = ratFunctionOf(S, v);
    if (!r) return [];
    if (r.den.degree < 1) return [simp(div(r.num.toNode(v), r.den.toNode(v)))];
    let p = r.num;
    let sign = false;
    if (p.lead.isNeg()) {
        sign = true;
        p = p.neg();
    }
    const out = [];
    const tops = [p.toNode(v), mul(polyShort(p, v, 'factored'))];
    const bots = [r.den.toNode(v), mul(polyShort(r.den, v, 'factored'))];
    for (const top of tops) {
        for (const bot of bots) {
            const t = top.type === 'mul' && top.args.length === 1 ? top.args[0] : top;
            const b = bot.type === 'mul' && bot.args.length === 1 ? bot.args[0] : bot;
            out.push(sign ? neg(div(t, b)) : div(t, b));
        }
    }
    return out;
}
