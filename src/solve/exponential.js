// solve/exponential — powers of a common base and exponential equations.

import { sym, num, fn, containsVar, mul, add, nodeKey, pow, div, neg, numValue, summands } from '../core/ast.js';
import { Q } from '../core/rational.js';
import { linearForm, Poly } from '../core/poly.js';
import { N1, approxOf, exactZero, isolated, qGcd, simpOr, tex, isZeroNode, sumNode } from './common.js';
import { partStep, polyTex, pushPart, solveAnyPoly } from './polynomial.js';
import { solveNodePoly } from './rational.js';
import { mergeRoots } from './roots.js';
import { msg, notation, eachLanguage } from '../i18n/index.js';
import { step } from '../core/steps.js';

// ---------------------------------------------------------------- powers of a common base

export const E_SYM = sym('e');
export const isE = (n) => n.type === 'sym' && n.name === 'e' && !n.var;

/** q = c^k with the smallest c > 1 (k integer, negative for q < 1); q > 0, q ≠ 1. */
function primitivePower(q) {
    if (q.lt(1)) {
        const [c, k] = primitivePower(q.inv());
        return [c, -k];
    }
    const bits = Math.max(q.n.toString(2).length, q.d.toString(2).length);
    for (let k = Math.min(bits, 64); k >= 2; k--) {
        const r = q.exactRoot(k);
        if (r && !r.isOne()) return [r, k];
    }
    return [q, 1];
}

/** base node → {c: Q | 'e', k: Q} with base = c^k, or null. */
export function baseInfo(b) {
    if (b.type === 'num' && b.value.isPos() && !b.value.isOne()) {
        const [c, k] = primitivePower(b.value);
        return { c, k: new Q(BigInt(k)) };
    }
    if (isE(b)) return { c: 'e', k: Q.ONE };
    if (b.type === 'pow' && b.exp.type === 'num') {
        const inner = baseInfo(b.base);
        return inner && { c: inner.c, k: inner.k.mul(b.exp.value) };
    }
    return null;
}

export const sameBase = (a, b) => (a === 'e' || b === 'e' ? a === b : a.eq(b));
export const baseNode = (c) => (c === 'e' ? E_SYM : num(c));

/** R = c^r with rational r → r, else null. */
export function exactPower(c, R) {
    const s = simpOr(R);
    if (s.type === 'num' && s.value.isOne()) return Q.ZERO;
    const bi = s.type === 'num' || isE(s) || s.type === 'pow' ? baseInfo(s) : null;
    if (bi && sameBase(bi.c, c)) return bi.k;
    return null;
}

/** log_c(x) node: ln, lg or log_c. */
export function logNode(c, x) {
    if (c === 'e') return fn('ln', x);
    if (c instanceof Q && c.eq(10)) return fn('lg', x);
    return fn('log', c instanceof Q ? num(c) : c, x);
}

/** log with a base given as a node. */
export function logNodeB(b, x) {
    if (isE(b)) return fn('ln', x);
    if (b.type === 'num' && b.value.eq(10)) return fn('lg', x);
    return fn('log', b, x);
}

// ---------------------------------------------------------------- exponential equations

export function analyzeExp(E, v) {
    let c = null;
    let mixed = false;
    const terms = [];
    const constant = [];
    for (const t of summands(E)) {
        if (!containsVar(t, v)) {
            constant.push(t);
            continue;
        }
        const fs = t.type === 'mul' ? t.args : [t];
        const coefF = [];
        const gs = [];
        const pows = [];
        for (const f of fs) {
            if (!containsVar(f, v)) {
                coefF.push(f);
                continue;
            }
            if (f.type !== 'pow' || containsVar(f.base, v)) return null;
            const bi = baseInfo(f.base);
            if (!bi) return null;
            if (c === null) c = bi.c;
            else if (!sameBase(c, bi.c)) mixed = true;
            gs.push(simpOr(mul(num(bi.k), f.exp)));
            pows.push(f);
        }
        terms.push({ coef: coefF.length ? simpOr(coefF.length === 1 ? coefF[0] : mul(coefF)) : N1, g: gs.length === 1 ? gs[0] : simpOr(add(gs)), pows, t });
    }
    if (!terms.length) return null;
    return { c, terms, constant: simpOr(sumNode(constant)), mixed };
}

/** a^f · b^f → (ab)^f inside each term (numeric bases), or null when nothing merges. */
function mergeSameExponent(E, v) {
    let changed = false;
    const terms = summands(E).map((t) => {
        if (t.type !== 'mul') return t;
        const groups = new Map();
        const rest = [];
        for (const f of t.args) {
            if (f.type === 'pow' && f.base.type === 'num' && f.base.value.isPos() && containsVar(f.exp, v)) {
                const k = nodeKey(f.exp);
                const g = groups.get(k);
                if (g) {
                    g.base = g.base.mul(f.base.value);
                    g.n++;
                } else groups.set(k, { base: f.base.value, exp: f.exp, n: 1 });
            } else rest.push(f);
        }
        if (![...groups.values()].some((g) => g.n > 1)) return t;
        changed = true;
        return mul([...rest, ...[...groups.values()].map((g) => pow(num(g.base), g.exp))]);
    });
    return changed ? simpOr(sumNode(terms)) : null;
}

export function solveExponential(lhs, rhs, E, ctx) {
    const v = ctx.v;
    const merged = mergeSameExponent(E, v);
    if (merged) {
        const r = solveExponential(lhs, rhs, merged, ctx);
        if (!r) return null;
        const pre = step({
            title: msg('solve.exponential.multiply_powers_with_equal_exponents'),
            tex: eachLanguage((l) => `${tex(merged, l)} = 0`),
            text: '$a^{f} \\cdot b^{f} = (ab)^{f}$.',
        });
        return { ...r, steps: [pre, ...r.steps] };
    }
    const info = analyzeExp(E, v);
    if (!info) return null;
    if (info.mixed) return solveExpMixed(info, ctx);
    const { c, terms, constant } = info;
    const cN = baseNode(c);
    const steps = [];
    const positive = msg('solve.exponential.power_of_positive_number_is_always');
    if (terms.length === 1) {
        const { coef, g, pows } = terms[0];
        const R = simpOr(div(neg(constant), coef));
        const single = pows.length === 1;
        const b = single ? pows[0].base : cN;
        const f = single ? pows[0].exp : g;
        const left = single ? pows[0] : pow(cN, g);
        if (!isolated(lhs, rhs, left, R))
            steps.push(step({ title: msg('solve.exponential.isolate_power'), tex: eachLanguage((l) => `${tex(left, l)} = ${tex(R, l)}`) }));
        const Rv = approxOf(R);
        if (!(Rv > 0) || exactZero(R) === true) {
            steps.push(step({ title: msg('solve.exponential.right_side_is_not_positive'), text: positive }));
            return { kind: 'none', roots: [], steps, type: 'exponential' };
        }
        const rb = single ? exactPower(baseInfo(b).c, R) : null;
        const kb = single ? baseInfo(b).k : Q.ONE;
        const rc = exactPower(c, R);
        let sub;
        if (rc !== null) {
            const rOwn = rc.div(kb); // R = b^(rc/kb)
            const rOwnOk = single && rb !== null;
            if (rOwnOk && (rOwn.isInt() || kb.isOne())) {
                steps.push(
                    step({
                        title: msg('solve.exponential.write_right_side_as_power_of', { b: (lng) => tex(b, lng) }),
                        tex: eachLanguage((l) => `${tex(left, l)} = ${tex(pow(b, num(rOwn)), l)}`),
                        text: msg('solve.exponential.bases_are_equal_so_exponents_are'),
                    }),
                );
                sub = ctx.solve(f, num(rOwn));
                pushPart(steps, f, num(rOwn), sub, v);
            } else {
                steps.push(
                    step({
                        title: msg('solve.exponential.write_both_sides_as_powers_of', { cN: (lng) => tex(cN, lng) }),
                        tex: eachLanguage((l) => `${tex(pow(cN, g), l)} = ${tex(pow(cN, num(rc)), l)}`),
                        text: msg('solve.exponential.bases_are_equal_so_we_equate'),
                    }),
                );
                sub = ctx.solve(g, num(rc));
                pushPart(steps, g, num(rc), sub, v);
            }
        } else {
            const Lg = logNodeB(b, R);
            steps.push(
                step({
                    title: msg('solve.exponential.take_logarithm_to_base', { b: (lng) => tex(b, lng) }),
                    tex: eachLanguage((l) => `${tex(f, l)} = ${tex(Lg, l)}`),
                    text: msg('solve.exponential.by_definition_of_logarithm', { b: (lng) => tex(b, lng), p: (lng) => tex(logNodeB(b, sym('a')), lng) }),
                }),
            );
            sub = ctx.solve(f, Lg);
            pushPart(steps, f, Lg, sub, v);
        }
        if (sub.kind === 'unsupported') return null;
        return { ...sub, steps, type: 'exponential' };
    }
    if (terms.length === 2 && isZeroNode(constant)) {
        const K = simpOr(div(neg(terms[1].coef), terms[0].coef));
        const [g1, g2] = [terms[0].g, terms[1].g];
        const Kv = approxOf(K);
        if (!(Kv > 0)) {
            steps.push(step({ title: msg('solve.exponential.powers_of_opposite_signs'), text: positive }));
            return { kind: 'none', roots: [], steps, type: 'exponential' };
        }
        if (exactZero(add(K, num(-1))) === true) {
            steps.push(
                step({
                    title: msg('solve.exponential.write_both_sides_as_powers_of', { cN: (lng) => tex(cN, lng) }),
                    tex: eachLanguage((l) => `${tex(pow(cN, g1), l)} = ${tex(pow(cN, g2), l)}`),
                    text: msg('solve.exponential.bases_are_equal_so_we_equate'),
                }),
            );
            const sub = ctx.solve(g1, g2);
            if (sub.kind === 'unsupported') return null;
            pushPart(steps, g1, g2, sub, v);
            return { ...sub, steps, type: 'exponential' };
        }
        const g = simpOr(add(g1, neg(g2)));
        steps.push(
            step({
                title: msg('solve.exponential.divide_both_sides_by', { p: (lng) => tex(pow(cN, g2), lng) }),
                tex: eachLanguage((l) => `${tex(pow(cN, g), l)} = ${tex(K, l)}`),
                text: msg('solve.exponential.power_is_positive_so_division_is'),
            }),
        );
        const sub = ctx.solve(pow(cN, g), K);
        if (sub.kind === 'unsupported') return null;
        steps.push(...sub.steps);
        return { ...sub, steps, type: 'exponential' };
    }
    // substitution t = c^(m·x)
    const lin = [];
    for (const t of terms) {
        const lf = linearForm(t.g, [v]);
        const k = numValue(t.coef);
        if (!lf || !k || lf.coeffs[v].isZero()) return null;
        lin.push({ m: lf.coeffs[v], s: lf.constant, k, t });
    }
    let m = lin[0].m.abs();
    for (const x of lin) m = qGcd(m, x.m.abs());
    const C0 = numValue(constant);
    if (!C0) return null;
    const coefs = new Map();
    let jmin = 0;
    for (const x of lin) {
        const j = x.m.div(m);
        if (!j.isInt()) return null;
        let cs;
        if (x.s.isZero()) cs = Q.ONE;
        else if (c !== 'e' && x.s.isInt()) cs = c.pow(x.s.n);
        else return null;
        const jj = Number(j.n);
        jmin = Math.min(jmin, jj);
        coefs.set(jj, (coefs.get(jj) ?? Q.ZERO).add(x.k.mul(cs)));
    }
    coefs.set(0, (coefs.get(0) ?? Q.ZERO).add(C0));
    const maxJ = Math.max(...coefs.keys());
    if (maxJ - jmin > 8) return null;
    const arr = new Array(maxJ - jmin + 1).fill(Q.ZERO);
    for (const [j, q] of coefs) arr[j - jmin] = arr[j - jmin].add(q);
    const Pt = new Poly(arr);
    if (Pt.degree < 1) return null;
    const Bq = c !== 'e' && m.isInt() ? c.pow(m.n) : null;
    const tNode = Bq ? pow(num(Bq), sym(v)) : pow(cN, simpOr(mul(num(m), sym(v))));
    const tTex = (l) => tex(tNode, l);
    const tSym = sym('t');
    const rewrites = (l) =>
        lin
            .map((x) => {
                const j = x.m.div(m);
                const cs = x.s.isZero() ? Q.ONE : c.pow(x.s.n);
                const node = simpOr(mul(num(x.k.mul(cs)), pow(tSym, num(j))));
                return `${tex(x.t.t, l)} = ${tex(node, l)}`;
            })
            .join(notation(l).listTex);
    steps.push(
        step({
            title: msg('solve.exponential.substitute_where', { p: (lng) => tTex(lng) }),
            tex: eachLanguage((l) => `${polyTex(Pt, 't', l)} = 0`),
            text: msg('solve.exponential.every_power_is_expressed_through', {
                p: (lng) => rewrites(lng),
                p2: (lng) => (jmin < 0 ? msg('solve.exponential.we_multiplied_both_sides_by_it', { p: -jmin }).in(lng) : ''),
            }),
        }),
    );
    const tr = solveAnyPoly(Pt, { v: 't', domain: 'real' });
    steps.push(
        partStep(
            eachLanguage((l) => `${polyTex(Pt, 't', l)} = 0`),
            tr,
            't',
        ),
    );
    const good = tr.roots.filter((r) => r.approx > 1e-12);
    const bad = tr.roots.filter((r) => !(r.approx > 1e-12));
    if (bad.length) {
        steps.push(
            step({
                title: msg('solve.exponential.drop'),
                tex: eachLanguage((l) => bad.map((r) => `t = ${tex(r.node, l)}`).join(',\\ ')),
                text: msg('solve.exponential.for_every', { p: (lng) => tTex(lng), v }),
            }),
        );
    }
    let roots = [];
    let numeric = !!tr.numeric;
    for (const r of good) {
        const sub = ctx.solve(tNode, r.node);
        if (sub.kind === 'unsupported') return null;
        roots.push(...sub.roots);
        if (sub.numeric) numeric = true;
        steps.push(
            partStep(
                eachLanguage((l) => `${tTex(l)} = ${tex(r.node, l)}`),
                sub,
                v,
            ),
        );
    }
    roots = mergeRoots(roots);
    return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'exponential', numeric };
}

/** a^f = K·b^g with different bases: take logarithms of both sides. */
function solveExpMixed(info, ctx) {
    const { terms, constant } = info;
    if (terms.length !== 2 || !isZeroNode(constant) || terms.some((t) => t.pows.length !== 1)) return null;
    const [A, B] = terms;
    const K = simpOr(div(neg(B.coef), A.coef));
    const steps = [];
    const left = A.pows[0];
    const right = simpOr(mul(K, B.pows[0]));
    steps.push(step({ title: msg('solve.exponential.put_powers_on_different_sides'), tex: eachLanguage((l) => `${tex(left, l)} = ${tex(right, l)}`) }));
    if (!(approxOf(K) > 0)) {
        steps.push(step({ title: msg('solve.exponential.sides_have_opposite_signs'), text: msg('solve.exponential.powers_are_positive_and_coefficient_is') }));
        return { kind: 'none', roots: [], steps, type: 'exponential' };
    }
    const lhs2 = mul(left.exp, fn('ln', left.base));
    const rhs2 = add(fn('ln', K), mul(B.pows[0].exp, fn('ln', B.pows[0].base)));
    const l2 = simpOr(lhs2);
    const r2 = simpOr(rhs2);
    steps.push(
        step({
            title: msg('solve.exponential.take_natural_logarithm_of_both_sides'),
            tex: eachLanguage((l) => `${tex(l2, l)} = ${tex(r2, l)}`),
            text: msg('solve.exponential.both_sides_are_positive_so_we'),
        }),
    );
    const E2 = simpOr(add(l2, neg(r2)));
    const sub = solveNodePoly(E2, ctx);
    if (!sub) return null;
    steps.push(...sub.steps);
    return { ...sub, steps, type: 'exponential' };
}
