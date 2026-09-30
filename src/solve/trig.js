// solve/trig — trigonometric equations: families of roots, substitutions, selection on a segment.

import { sym, numValue, add, mul, div, num, fn, neg, containsVar, freeVars, pow, nodeKey } from '../core/ast.js';
import { collectTerms, numDen } from '../core/expand.js';
import { Q } from '../core/rational.js';
import { Poly } from '../core/poly.js';
import { splitCoeff } from '../core/simplify.js';
import { N0, N1, PI, S, T, approxOf, byLang, exactZero, expd, isConstNode, orTex, outermost, pick, replaceNode, simpOr, tex } from './common.js';
import { isZeroNode, nodeQuadRoots, solveAnyPoly, sumNode } from './polynomial.js';
import { mkRoot, rootsTex } from './roots.js';

// ---------------------------------------------------------------- trigonometric equations

export const TRIG_FN = ['sin', 'cos', 'tan', 'cot'];
const PH = { sin: '__s', cos: '__c', tan: '__t', cot: '__k' };
export const N_SYM = sym('n');
export const ZZ = (l) => (l === 'ru' ? ',\\ n \\in \\mathbb{Z}' : ',\\ n \\in \\mathbb{Z}');

/** u = k·x + s with rational k ≠ 0 and a constant s → {k, s}. */
function linArg(u, v) {
    let ct;
    try {
        ct = collectTerms(u, v);
    } catch {
        return null;
    }
    if (!ct || !ct.has(1) || ![...ct.keys()].every((d) => d === 0 || d === 1)) return null;
    const k = numValue(ct.get(1));
    if (!k || k.isZero()) return null;
    const s = ct.get(0) ?? N0;
    return isConstNode(s) ? { k, s } : null;
}

/** A family x = base + period·n; gid groups families that are printed together. */
export function mkFamily(base, period, gid = null) {
    const b = simpOr(base);
    const p = simpOr(period);
    return { base: b, period: p, b: approxOf(b), p: approxOf(p), gid };
}

/** "a + b" of already simplified terms (zeros dropped), printed without re-simplifying. */
export function plusTex(nodes, lang) {
    const ns = nodes.filter((n) => !isZeroNode(n));
    if (!ns.length) return '0';
    return tex(ns.length === 1 ? ns[0] : add(ns), lang);
}

const signedTex = (t) => (t.startsWith('-') ? ` ${t}` : ` + ${t}`);
export const periodN = (p) => simpOr(mul(p, N_SYM));

export function familyTex(f, v, lang) {
    return `${v} = ${plusTex([f.base, periodN(f.period)], lang)}`;
}

/** Answer lines for a list of families: the group's school form when intact, else one line per family. */
export function familiesTex(fams, v, lang, sep) {
    const lines = [];
    const done = new Set();
    for (const f of fams) {
        if (f.group && !done.has(f.group)) {
            const members = fams.filter((g) => g.group === f.group);
            if (members.length === f.group.size) {
                lines.push(pick(f.group.tex, lang));
                done.add(f.group);
                continue;
            }
        }
        if (f.group && done.has(f.group)) continue;
        lines.push(familyTex(f, v, lang));
    }
    return lines.join(sep ?? (lang === 'ru' ? ';\\quad ' : ',\\quad ')) + ZZ(lang);
}

export function familiesToRoots(fams) {
    return fams.map((f) => ({ node: simpOr(add(f.base, mul(f.period, N_SYM))), approx: f.b, mult: 1, family: { base: f.base, period: f.period, param: 'n' } }));
}

/** Is family a (base a, period p) contained in family b? */
function famSubset(a, b) {
    const r = a.p / b.p;
    if (Math.abs(r - Math.round(r)) > 1e-9 || Math.round(r) < 1) return false;
    const d = (a.b - b.b) / b.p;
    return Math.abs(d - Math.round(d)) <= 1e-9;
}

/** Drop families contained in others; join m families with a common period into one with period/m. */
export function mergeFamilies(fams) {
    let out = [];
    for (const f of fams) {
        if (out.some((g) => famSubset(f, g))) continue;
        out = out.filter((g) => !famSubset(g, f));
        out.push(f);
    }
    // join: two families with equal period P whose bases differ by an odd multiple of P/2
    let changed = true;
    while (changed) {
        changed = false;
        for (let i = 0; i < out.length && !changed; i++) {
            for (let j = i + 1; j < out.length && !changed; j++) {
                const f = out[i];
                const g = out[j];
                if (Math.abs(f.p - g.p) > 1e-12 * Math.max(1, f.p)) continue;
                const d = (g.b - f.b) / (f.p / 2);
                const r = Math.round(d);
                if (Math.abs(d - r) > 1e-9 || r % 2 === 0) continue;
                const first = Math.abs(g.b) < Math.abs(f.b) - 1e-12 ? g : f;
                const nf = mkFamily(first.base, div(first.period, num(2)));
                out = out.filter((x) => x !== f && x !== g);
                out.push(nf);
                changed = true;
            }
        }
    }
    return out.sort((a, b) => a.p - b.p || a.b - b.b);
}

const TRIG_NAME = { sin: T('синус', 'sine'), cos: T('косинус', 'cosine'), tan: T('тангенс', 'tangent'), cot: T('котангенс', 'cotangent') };

/** F(u) = a for u = kx + s → {families, steps}. */
export function basicTrig(F, u, a, ctx) {
    const v = ctx.v;
    const la = linArg(u, v);
    if (!la) return null;
    const aS = simpOr(a);
    const av = approxOf(aS);
    if (!Number.isFinite(av)) return null;
    const eqT = (l) => `${tex(fn(F, u), l)} = ${tex(aS, l)}`;
    const title = byLang((l) => (l === 'ru' ? `Решаем $${eqT(l)}$` : `Solve $${eqT(l)}$`));
    if ((F === 'sin' || F === 'cos') && Math.abs(av) > 1 + 1e-12) {
        return {
            families: [],
            steps: [S(title, { text: T(`${F === 'sin' ? 'Синус' : 'Косинус'} принимает значения только от $-1$ до $1$, а $|${tex(aS)}| > 1$ — корней нет.`, `The ${TRIG_NAME[F].en} only takes values from $-1$ to $1$, and $|${tex(aS, 'en')}| > 1$: no roots.`) })],
        };
    }
    const is = (x) => Math.abs(av - x) < 1e-12 && exactZero(add(aS, num(-x))) !== false;
    const twoPi = mul(num(2), PI);
    const halfPi = mul(num(Q.HALF), PI);
    let uf;
    let A = null;
    let rule;
    let general = false;
    if (F === 'sin') {
        if (is(0)) [uf, rule] = [[[N0, PI]], T('Частный случай: $\\sin t = 0 \\Leftrightarrow t = \\pi n$.', 'A special case: $\\sin t = 0 \\Leftrightarrow t = \\pi n$.')];
        else if (is(1)) [uf, rule] = [[[halfPi, twoPi]], T('Частный случай: $\\sin t = 1 \\Leftrightarrow t = \\frac{\\pi}{2} + 2\\pi n$.', 'A special case: $\\sin t = 1 \\Leftrightarrow t = \\frac{\\pi}{2} + 2\\pi n$.')];
        else if (is(-1)) [uf, rule] = [[[neg(halfPi), twoPi]], T('Частный случай: $\\sin t = -1 \\Leftrightarrow t = -\\frac{\\pi}{2} + 2\\pi n$.', 'A special case: $\\sin t = -1 \\Leftrightarrow t = -\\frac{\\pi}{2} + 2\\pi n$.')];
        else {
            A = simpOr(fn('asin', aS));
            uf = [[A, twoPi], [add(PI, neg(A)), twoPi]];
            general = true;
            rule = T('Формула корней: $\\sin t = a \\Leftrightarrow t = (-1)^n \\arcsin a + \\pi n$ (при $|a| \\le 1$).', 'The root formula: $\\sin t = a \\Leftrightarrow t = \\arcsin a + 2\\pi n$ or $t = \\pi - \\arcsin a + 2\\pi n$ (for $|a| \\le 1$).');
        }
    } else if (F === 'cos') {
        if (is(0)) [uf, rule] = [[[halfPi, PI]], T('Частный случай: $\\cos t = 0 \\Leftrightarrow t = \\frac{\\pi}{2} + \\pi n$.', 'A special case: $\\cos t = 0 \\Leftrightarrow t = \\frac{\\pi}{2} + \\pi n$.')];
        else if (is(1)) [uf, rule] = [[[N0, twoPi]], T('Частный случай: $\\cos t = 1 \\Leftrightarrow t = 2\\pi n$.', 'A special case: $\\cos t = 1 \\Leftrightarrow t = 2\\pi n$.')];
        else if (is(-1)) [uf, rule] = [[[PI, twoPi]], T('Частный случай: $\\cos t = -1 \\Leftrightarrow t = \\pi + 2\\pi n$.', 'A special case: $\\cos t = -1 \\Leftrightarrow t = \\pi + 2\\pi n$.')];
        else {
            A = simpOr(fn('acos', aS));
            uf = [[A, twoPi], [neg(A), twoPi]];
            general = true;
            rule = T('Формула корней: $\\cos t = a \\Leftrightarrow t = \\pm\\arccos a + 2\\pi n$ (при $|a| \\le 1$).', 'The root formula: $\\cos t = a \\Leftrightarrow t = \\pm\\arccos a + 2\\pi n$ (for $|a| \\le 1$).');
        }
    } else if (F === 'tan') {
        A = simpOr(fn('atan', aS));
        uf = [[A, PI]];
        rule = T('Формула корней: $\\operatorname{tg} t = a \\Leftrightarrow t = \\operatorname{arctg} a + \\pi n$.', 'The root formula: $\\tan t = a \\Leftrightarrow t = \\arctan a + \\pi n$.');
    } else {
        A = simpOr(fn('acot', aS));
        uf = [[A, PI]];
        rule = T('Формула корней: $\\operatorname{ctg} t = a \\Leftrightarrow t = \\operatorname{arcctg} a + \\pi n$.', 'The root formula: $\\cot t = a \\Leftrightarrow t = \\operatorname{arccot} a + \\pi n$.');
    }
    // arctg(2 − √3) = π/12 and the like: a rational multiple of π with a small denominator
    let recognized = null;
    if (A && A.type !== 'num' && !(A.type === 'mul' && A.args.some((f) => f.type === 'sym' && f.name === 'pi')) && !(A.type === 'sym' && A.name === 'pi')) {
        const r = approxOf(A) / Math.PI;
        for (let d = 1; d <= 24 && Number.isFinite(r); d++) {
            const n = Math.round(r * d);
            // …and F of that angle really is a (arctg 10¹⁰ is within 1e-10 of π/2, but tg(π/2) is not 10¹⁰)
            const Fv = approxOf(fn(F, mul(num(new Q(BigInt(n), BigInt(d))), PI)));
            if (Math.abs(r * d - n) < 1e-10 && Number.isFinite(Fv) && Math.abs(Fv - av) <= 1e-9 * Math.max(1, Math.abs(av))) {
                const B = simpOr(mul(num(new Q(BigInt(n), BigInt(d))), PI));
                recognized = { from: A, to: B };
                uf = uf.map(([b, P]) => [replaceNode(b, A, B), P]);
                A = B;
                break;
            }
        }
    }
    if (recognized) {
        const f = recognized;
        rule = T(`${rule.ru} Здесь $${tex(f.from)} = ${tex(f.to)}$.`, `${rule.en} Here $${tex(f.from, 'en')} = ${tex(f.to, 'en')}$.`);
    }
    const k = la.k;
    const s = la.s;
    const kn = num(k);
    const fams = uf.map(([b, P]) => mkFamily(div(add(b, neg(s)), kn), div(P, num(k.abs()))));
    const isX = k.isOne() && isZeroNode(simpOr(s));
    // display: the school form for u, then for x
    const shift = simpOr(div(neg(s), kn));
    const group = { size: fams.length, tex: null };
    const xTex = (l) => {
        if (general && F === 'sin' && l === 'ru') {
            let Ak = simpOr(div(A, kn));
            let sgn = '(-1)^{n}';
            if (approxOf(Ak) < 0) {
                Ak = simpOr(neg(Ak));
                sgn = '(-1)^{n+1}';
            }
            return `${v} = ${sgn}${tex(Ak, l)}${signedTex(plusTex([shift, periodN(simpOr(div(PI, num(k.abs()))))], l))}`;
        }
        if (general && F === 'cos') {
            const Ak = simpOr(div(A, num(k.abs())));
            return `${v} = \\pm ${tex(Ak, l)}${signedTex(plusTex([shift, periodN(fams[0].period)], l))}`;
        }
        return fams.map((f) => familyTex(f, v, l)).join(l === 'ru' ? ';\\quad ' : ',\\quad ');
    };
    group.tex = byLang(xTex);
    for (const f of fams) f.group = group;
    const uTex = (l) => {
        const us = tex(u, l);
        if (general && F === 'sin' && l === 'ru') return `${us} = (-1)^{n}${tex(A, l)} + \\pi n`;
        if (general && F === 'cos') return `${us} = \\pm ${tex(A, l)} + 2\\pi n`;
        return uf.map(([b, P]) => `${us} = ${plusTex([simpOr(b), periodN(simpOr(P))], l)}`).join(l === 'ru' ? ';\\quad ' : ',\\quad ');
    };
    const texLines = byLang((l) => (isX ? xTex(l) : `${uTex(l)} \\;\\Rightarrow\\; ${xTex(l)}`) + ZZ(l));
    return { families: fams, steps: [S(title, { tex: texLines, text: rule })] };
}

/** Coefficients of a polynomial in one placeholder: Map degree → constant node, or null. */
function coeffsIn(P, name, v, allowOthers = false) {
    let ct;
    try {
        ct = collectTerms(P, name);
    } catch {
        return null;
    }
    if (!ct) return null;
    for (const [d, c] of ct) {
        if (!Number.isInteger(d) || d < 0 || d > 8) return null;
        if (containsVar(c, v) || (!allowOthers && freeVars(c).some((x) => x.startsWith('__')))) return null;
    }
    return ct;
}

/** Map "i,j" → coefficient for a polynomial in two placeholders. */
function coeffs2(P, a, b, v) {
    const ca = coeffsIn(expd(P) ?? P, a, v, true);
    if (!ca) return null;
    const out = new Map();
    for (const [i, c] of ca) {
        const cb = coeffsIn(c, b, v);
        if (!cb) return null;
        for (const [j, cc] of cb) if (!isConstNode(cc)) return null;
        for (const [j, cc] of cb) out.set(`${i},${j}`, cc);
    }
    return out;
}

/** Polynomial with constant node coefficients (Map degree → node) → roots {roots, steps} or null. */
function rootsOfNodePoly(ct, name) {
    const deg = Math.max(...ct.keys());
    const qs = [];
    let allQ = true;
    for (let d = 0; d <= deg; d++) {
        const q = numValue(ct.get(d) ?? N0);
        if (!q) allQ = false;
        qs.push(q);
    }
    if (allQ) {
        const P = new Poly(qs);
        const r = solveAnyPoly(P, { v: name, domain: 'real' });
        return { roots: r.roots, steps: r.steps, poly: P };
    }
    if (deg === 1) {
        const r = simpOr(div(neg(ct.get(0) ?? N0), ct.get(1)));
        return { roots: [mkRoot(r)], steps: [] };
    }
    if (deg === 2) {
        const r = nodeQuadRoots(ct.get(2), ct.get(1) ?? N0, ct.get(0) ?? N0, { v: name, domain: 'real' });
        return { roots: r.roots, steps: r.steps };
    }
    return null;
}

function polyNodeFrom(ct, name) {
    const terms = [...ct.entries()].sort((a, b) => b[0] - a[0]).map(([d, c]) => simpOr(mul(c, d === 0 ? N1 : pow(sym(name), num(d)))));
    return simpOr(sumNode(terms));
}

/** A polynomial in t = F(u): solve for t, keep |t| ≤ 1 for sin/cos, then the basic equations. */
function trigPolyOne(P, F, u, ctx, extraText) {
    const v = ctx.v;
    const ct = coeffsIn(expd(P) ?? P, PH[F], v);
    if (!ct || !ct.size) return null;
    const deg = Math.max(...ct.keys());
    if (deg < 1) return null;
    const steps = [];
    let families = [];
    if (deg === 1) {
        const a = simpOr(div(neg(ct.get(0) ?? N0), ct.get(1)));
        const b = basicTrig(F, u, a, ctx);
        if (!b) return null;
        if (extraText) steps.push(S(extraText.title, { tex: byLang((l) => `${tex(fn(F, u), l)} = ${tex(a, l)}`), text: extraText.text }));
        steps.push(...b.steps);
        return { families: b.families, steps };
    }
    const tName = 't';
    const polyT = polyNodeFrom(ct, tName);
    const Fu = (l) => tex(fn(F, u), l);
    steps.push(S(byLang((l) => (l === 'ru' ? `Замена $t = ${Fu(l)}$` : `Substitute $t = ${Fu(l)}$`)), {
        tex: byLang((l) => `${tex(polyT, l)} = 0`),
        text: extraText ? extraText.text : (F === 'sin' || F === 'cos' ? T('Уравнение стало алгебраическим относительно $t$; помним, что $-1 \\le t \\le 1$.', 'The equation is now algebraic in $t$; remember that $-1 \\le t \\le 1$.') : T('Уравнение стало алгебраическим относительно $t$.', 'The equation is now algebraic in $t$.')),
    }));
    const rr = rootsOfNodePoly(ct, tName);
    if (!rr) return null;
    steps.push(S(byLang((l) => (l === 'ru' ? `Решаем $${tex(polyT, l)} = 0$` : `Solve $${tex(polyT, l)} = 0$`)), { tex: byLang((l) => rootsTex(rr.roots, 't', l)), sub: rr.steps }));
    for (const t of rr.roots) {
        if ((F === 'sin' || F === 'cos') && Math.abs(t.approx) > 1 + 1e-12) {
            steps.push(S(byLang((l) => `$t = ${tex(t.node, l)}$`), { text: T(`Не подходит: $|${F === 'sin' ? '\\sin' : '\\cos'} x| \\le 1$.`, `Rejected: $|${F === 'sin' ? '\\sin' : '\\cos'} x| \\le 1$.`) }));
            continue;
        }
        const b = basicTrig(F, u, t.node, ctx);
        if (!b) return null;
        families.push(...b.families);
        steps.push(...b.steps);
    }
    return { families, steps };
}

export function trigCore(E, ctx) {
    return trigCore0(E, ctx) ?? trigFraction(E, ctx);
}

/**
 * A fraction with trigonometric functions in a denominator that is not a plain power (sin x/(1 − cos x) = 0):
 * the numerator is zero and the denominator is not — solve the numerator, the ОДЗ check of the families then
 * drops the points where the denominator vanishes (x = πn → x = π + 2πn).
 */
function trigFraction(E, ctx) {
    const v = ctx.v;
    if (ctx.trigFrac) return null;
    let nd;
    try {
        nd = numDen(E);
    } catch {
        return null;
    }
    if (!nd || !containsVar(nd.den, v) || !containsVar(nd.num, v)) return null;
    if (splitCoeff(nd.num).coef.isNeg()) nd = { num: simpOr(neg(nd.num)), den: nd.den };
    const r = trigCore(nd.num, { ...ctx, trigFrac: true });
    if (!r) return null;
    const steps = [S(T('Дробь равна нулю, когда числитель равен нулю, а знаменатель — нет', 'A fraction is zero when its numerator is zero and its denominator is not'), {
        tex: byLang((l) => `${tex(nd.num, l)} = 0,\\qquad ${tex(nd.den, l)} \\ne 0`),
        text: T('Решаем уравнение «числитель = 0», а корни, при которых знаменатель обращается в ноль, отбросим по ОДЗ.', 'Solve "numerator = 0"; the roots where the denominator vanishes are dropped by the domain.'),
    })];
    return { families: r.families, steps: [...steps, ...r.steps] };
}

function trigCore0(E, ctx) {
    const v = ctx.v;
    const tn = outermost(E, (n) => n.type === 'fn' && TRIG_FN.includes(n.name) && containsVar(n, v));
    if (!tn.length) return null;
    let rest = E;
    tn.forEach((t, i) => {
        rest = replaceNode(rest, t, sym(`__p${i}`));
    });
    if (containsVar(rest, v)) return null;
    const args = new Map();
    for (const t of tn) args.set(nodeKey(t.args[0]), t.args[0]);
    if (args.size > 1) return trigMultiArg(E, tn, [...args.values()], ctx);
    const u = tn[0].args[0];
    if (!linArg(u, v)) return null;
    const names0 = [...new Set(tn.map((t) => t.name))].sort();
    let P = E;
    for (const name of names0) P = replaceNode(P, fn(name, u), sym(PH[name]));
    const pre = [];
    const nameSet = new Set(names0);
    const Uf = (f) => (l) => tex(fn(f, u), l);
    // tg and ctg next to sin and cos: tg = sin/cos, ctg = cos/sin
    if ((nameSet.has('sin') || nameSet.has('cos')) && (nameSet.has('tan') || nameSet.has('cot'))) {
        P = replaceNode(P, sym(PH.tan), div(sym(PH.sin), sym(PH.cos)));
        P = replaceNode(P, sym(PH.cot), div(sym(PH.cos), sym(PH.sin)));
        nameSet.delete('tan');
        nameSet.delete('cot');
        nameSet.add('sin');
        nameSet.add('cos');
        pre.push(S(T('Выражаем тангенс и котангенс через синус и косинус', 'Write the tangent and cotangent through sine and cosine'), {
            text: T('$\\operatorname{tg} t = \\frac{\\sin t}{\\cos t}$, $\\operatorname{ctg} t = \\frac{\\cos t}{\\sin t}$.', '$\\tan t = \\frac{\\sin t}{\\cos t}$, $\\cot t = \\frac{\\cos t}{\\sin t}$.'),
        }));
    }
    // trig functions in denominators: multiply by their powers (not zero by the ОДЗ)
    for (const name of [...nameSet]) {
        let ct;
        try {
            ct = collectTerms(expd(P) ?? P, PH[name]);
        } catch {
            ct = null;
        }
        if (!ct) return null;
        const mn = Math.min(0, ...ct.keys());
        if (mn < 0) {
            const k = -mn;
            P = expd(mul(P, pow(sym(PH[name]), num(k))));
            if (!P) return null;
            pre.push(S(T(`Умножаем обе части на $${Uf(name)('ru')}${k > 1 ? `^{${k}}` : ''}$`, `Multiply both sides by $${Uf(name)('en')}${k > 1 ? `^{${k}}` : ''}$`), {
                tex: byLang((l) => `${tex(simpOr(replaceNode(replaceNode(replaceNode(replaceNode(P, sym(PH.sin), fn('sin', u)), sym(PH.cos), fn('cos', u)), sym(PH.tan), fn('tan', u)), sym(PH.cot), fn('cot', u))), l)} = 0`),
                text: T('Он стоит в знаменателе, поэтому по ОДЗ не равен нулю — равносильность не нарушается.', 'It stands in a denominator, so by the domain it is not zero and the equation stays equivalent.'),
            }));
        }
    }
    const names = [...nameSet].sort();
    const res = trigSingle(P, names, u, ctx);
    return res && { families: res.families, steps: [...pre, ...res.steps] };
}

function trigSingle(P, names, u, ctx) {
    const v = ctx.v;
    const done = (r, extra = []) => r && { families: r.families, steps: [...extra, ...r.steps] };
    if (names.length === 1) return done(trigPolyOne(P, names[0], u, ctx));
    const key = names.join(',');
    const Ut = (f) => (l) => tex(fn(f, u), l);
    if (key === 'cos,sin') {
        const bv = coeffs2(P, '__s', '__c', v);
        if (!bv) return null;
        return sinCosCore(bv, u, ctx, 0);
    }
    if (key === 'cot,tan') {
        const bv = coeffs2(P, '__t', '__k', v);
        if (!bv) return null;
        const ij = [...bv.keys()].map((k) => k.split(',').map(Number));
        const mj = Math.max(...ij.map(([, j]) => j));
        const ct = new Map();
        for (const [i, j] of ij) {
            const d = i - j + mj;
            ct.set(d, simpOr(add(ct.get(d) ?? N0, bv.get(`${i},${j}`))));
        }
        for (const [d, c] of [...ct]) if (isZeroNode(c)) ct.delete(d);
        if (!ct.size) return null;
        const polyT = polyNodeFrom(ct, PH.tan);
        const pre = S(T(`Заменяем $\\operatorname{ctg} = \\frac{1}{\\operatorname{tg}}$ и умножаем на $\\operatorname{tg}${mj > 1 ? `^${mj}` : ''}$`, `Replace $\\cot = \\frac{1}{\\tan}$ and multiply by $\\tan${mj > 1 ? `^${mj}` : ''}$`), {
            tex: byLang((l) => `${tex(simpOr(replaceNode(polyT, sym(PH.tan), fn('tan', u))), l)} = 0`),
            text: T('Раз котангенс определён, $\\operatorname{tg} \\ne 0$ — умножать можно, но корень $\\operatorname{tg} = 0$ придётся отбросить.', 'Since the cotangent is defined, $\\tan \\ne 0$: the multiplication is fine, but a root $\\tan = 0$ must be dropped.'),
        });
        const r = trigPolyOne(polyT, 'tan', u, ctx);
        if (!r) return null;
        r.families = r.families.filter((f) => Math.abs(Math.tan(f.b * linArg(u, v).k.toNumber() + approxOf(linArg(u, v).s))) > 1e-9);
        return done(r, [pre]);
    }
    return null;
}

function bvNode(bv, u) {
    const terms = [...bv.entries()].map(([k, c]) => {
        const [i, j] = k.split(',').map(Number);
        return simpOr(mul(c, pow(fn('sin', u), num(i)), pow(fn('cos', u), num(j))));
    });
    return simpOr(sumNode(terms));
}

/** A polynomial in sin u and cos u given as Map "i,j" → coefficient. */
function sinCosCore(bv, u, ctx, depth) {
    const v = ctx.v;
    if (depth > 3) return null;
    for (const [k, c] of [...bv]) if (isZeroNode(simpOr(c))) bv.delete(k);
    if (!bv.size) return null;
    const Ut = (f) => (l) => tex(fn(f, u), l);
    const done = (r, extra = []) => r && { families: r.families, steps: [...extra, ...r.steps] };
    const ij0 = [...bv.keys()].map((k) => k.split(',').map(Number));
    for (const [F, idx] of [['sin', 1], ['cos', 0]]) {
        if (!ij0.every((p) => p[idx] === 0)) continue;
        const node = simpOr(sumNode([...bv.entries()].map(([k, c]) => mul(c, pow(sym(PH[F]), num(Number(k.split(',')[1 - idx])))))));
        return trigPolyOne(node, F, u, ctx);
    }
    const a = Math.min(...ij0.map((p) => p[0]));
    const b = Math.min(...ij0.map((p) => p[1]));
    if (a > 0 || b > 0) {
        const red = new Map();
        for (const [k, c] of bv) {
            const [i, j] = k.split(',').map(Number);
            red.set(`${i - a},${j - b}`, c);
        }
        const fac = simpOr(mul(pow(fn('sin', u), num(a)), pow(fn('cos', u), num(b))));
        const redNode = bvNode(red, u);
        const steps = [S(T('Выносим общий множитель за скобки', 'Take the common factor out of the brackets'), {
            tex: byLang((l) => `${tex(fac, l)}\\left(${tex(redNode, l)}\\right) = 0`),
            text: T('Произведение равно нулю, когда один из множителей равен нулю.', 'A product is zero when one of the factors is zero.'),
        })];
        const families = [];
        if (a > 0) {
            const r = basicTrig('sin', u, N0, ctx);
            if (!r) return null;
            families.push(...r.families);
            steps.push(...r.steps);
        }
        if (b > 0) {
            const r = basicTrig('cos', u, N0, ctx);
            if (!r) return null;
            families.push(...r.families);
            steps.push(...r.steps);
        }
        if ([...red.keys()].some((k) => k !== '0,0')) {
            const r = sinCosCore(red, u, ctx, depth + 1);
            if (!r) return null;
            families.push(...r.families);
            steps.push(...r.steps);
        }
        return { families, steps };
    }
    const ij = [...bv.keys()].map((k) => k.split(',').map(Number));
    const nonConst = ij.filter(([i, j]) => i + j > 0);
    // only even powers of one function: use sin² + cos² = 1
    for (const [F, G, idx] of [['cos', 'sin', 0], ['sin', 'cos', 1]]) {
        if (!ij.every((p) => p[idx] % 2 === 0)) continue;
        const other = PH[F];
        const terms = [...bv.entries()].map(([k, c]) => {
            const [i, j] = k.split(',').map(Number);
            const g = idx === 0 ? i : j;
            const f = idx === 0 ? j : i;
            return mul(c, pow(add(N1, neg(pow(sym(other), num(2)))), num(g / 2)), pow(sym(other), num(f)));
        });
        const P2 = expd(sumNode(terms));
        if (!P2) return null;
        const r = trigPolyOne(P2, F, u, ctx);
        const pre = S(T(`Заменяем $${Ut(G)('ru')}^2$ на $1 - ${Ut(F)('ru')}^2$`, `Replace $${Ut(G)('en')}^2$ with $1 - ${Ut(F)('en')}^2$`), {
            tex: byLang((l) => `${tex(simpOr(replaceNode(P2, sym(other), fn(F, u))), l)} = 0`),
            text: T('Основное тригонометрическое тождество: $\\sin^2 t + \\cos^2 t = 1$. Теперь в уравнении одна функция.', 'The Pythagorean identity $\\sin^2 t + \\cos^2 t = 1$ leaves one function in the equation.'),
        });
        return done(r, [pre]);
    }
    const degs = new Set(nonConst.map(([i, j]) => i + j));
    const c0 = bv.get('0,0');
    if (degs.size === 1 && (!c0 || [...degs][0] === 2)) {
        const d = [...degs][0];
        const h = new Map();
        for (const [i, j] of nonConst) h.set(i, bv.get(`${i},${j}`));
        const pre = [];
        if (c0) {
            h.set(2, simpOr(add(h.get(2) ?? N0, c0)));
            h.set(0, simpOr(add(h.get(0) ?? N0, c0)));
            pre.push(S(T('Записываем число как $a(\\sin^2 + \\cos^2)$', 'Write the number as $a(\\sin^2 + \\cos^2)$'), {
                tex: byLang((l) => `${tex(simpOr(sumNode([...h.entries()].filter(([, c]) => !isZeroNode(c)).map(([i, c]) => mul(c, pow(fn('sin', u), num(i)), pow(fn('cos', u), num(d - i)))))), l)} = 0`),
                text: T('Так все слагаемые получают одинаковую степень — уравнение становится однородным.', 'Now every term has the same degree: the equation becomes homogeneous.'),
            }));
        }
        for (const [i, c] of [...h]) if (isZeroNode(simpOr(c))) h.delete(i);
        const maxI = Math.max(...h.keys());
        const m = d - maxI; // cos^m is a common factor
        let families = [];
        const steps = [...pre];
        if (m > 0) {
            steps.push(S(T(`Выносим $\\cos${m > 1 ? `^${m}` : ''}$ за скобки`, `Take $\\cos${m > 1 ? `^${m}` : ''}$ out of the brackets`), {
                text: T(`Одна из возможностей: $${Ut('cos')('ru')} = 0$.`, `One possibility: $${Ut('cos')('en')} = 0$.`),
            }));
            const b = basicTrig('cos', u, N0, ctx);
            if (!b) return null;
            families.push(...b.families);
            steps.push(...b.steps);
        }
        const dd = maxI;
        if (dd > 0) {
            const ct = new Map();
            for (const [i, c] of h) ct.set(i, c);
            const polyT = polyNodeFrom(ct, PH.tan);
            steps.push(S(T(`Однородное уравнение: делим на $\\cos${dd > 1 ? `^${dd}` : ''} ${tex(u).length > 1 ? `(${tex(u)})` : tex(u)}$`, `A homogeneous equation: divide by $\\cos${dd > 1 ? `^${dd}` : ''} ${tex(u, 'en').length > 1 ? `(${tex(u, 'en')})` : tex(u, 'en')}$`), {
                tex: byLang((l) => `${tex(simpOr(replaceNode(polyT, sym(PH.tan), fn('tan', u))), l)} = 0`),
                text: T(`Делить можно: если $${Ut('cos')('ru')} = 0$, то $${Ut('sin')('ru')} = \\pm 1$, и уравнение даёт $${tex(h.get(dd))} = 0$ — неверно.`, `This is allowed: if $${Ut('cos')('en')} = 0$ then $${Ut('sin')('en')} = \\pm 1$ and the equation gives $${tex(h.get(dd), 'en')} = 0$, which is false.`),
            }));
            const r = trigPolyOne(polyT, 'tan', u, ctx);
            if (!r) return null;
            families.push(...r.families);
            steps.push(...r.steps);
        }
        return { families, steps };
    }
    // a sin u + b cos u = c: the auxiliary angle
    if (ij.every(([i, j]) => i + j <= 1) && bv.has('1,0') && bv.has('0,1')) {
        const a = bv.get('1,0');
        const b = bv.get('0,1');
        const cRight = simpOr(neg(c0 ?? N0));
        const R = simpOr(pow(add(pow(a, num(2)), pow(b, num(2))), num(Q.HALF)));
        const cosPhi = simpOr(div(a, R));
        let phi = simpOr(fn('acos', cosPhi));
        if (approxOf(b) < 0) phi = simpOr(neg(phi));
        const u2 = simpOr(add(u, phi));
        const rhs2 = simpOr(div(cRight, R));
        const pre = S(T('Метод вспомогательного угла', 'The auxiliary angle method'), {
            tex: byLang((l) => `${tex(simpOr(add(mul(a, fn('sin', u)), mul(b, fn('cos', u)))), l)} = ${tex(R, l)}\\sin\\left(${tex(u2, l)}\\right)`),
            text: T(`$a\\sin t + b\\cos t = R\\sin(t + \\varphi)$, где $R = \\sqrt{a^2 + b^2} = ${tex(R)}$, $\\cos\\varphi = \\frac{a}{R}$, $\\sin\\varphi = \\frac{b}{R}$; здесь $\\varphi = ${tex(phi)}$.`,
                `$a\\sin t + b\\cos t = R\\sin(t + \\varphi)$ with $R = \\sqrt{a^2 + b^2} = ${tex(R, 'en')}$, $\\cos\\varphi = \\frac{a}{R}$, $\\sin\\varphi = \\frac{b}{R}$; here $\\varphi = ${tex(phi, 'en')}$.`),
        });
        const r = basicTrig('sin', u2, rhs2, ctx);
        return done(r, [pre]);
    }
    return null;
}

/** c·F(u) with a rational c → {c, F, u}. */
function trigTerm(t, v) {
    const fs = t.type === 'mul' ? t.args : [t];
    const withV = fs.filter((f) => containsVar(f, v));
    if (withV.length !== 1 || withV[0].type !== 'fn' || !TRIG_FN.includes(withV[0].name)) return null;
    const c = numValue(simpOr(fs.length === 1 ? N1 : mul(fs.filter((f) => f !== withV[0]))));
    return c && { c, F: withV[0].name, u: withV[0].args[0] };
}

/** sin a ± sin b, cos a ± cos b = 0 → a product of two factors. */
function sumToProduct(E, ctx) {
    const v = ctx.v;
    if (E.type !== 'add' || E.args.length !== 2) return null;
    const [A, B] = E.args.map((t) => trigTerm(t, v));
    if (!A || !B || A.F !== B.F || (A.F !== 'sin' && A.F !== 'cos') || !A.c.abs().eq(B.c.abs())) return null;
    const plus = A.c.eq(B.c);
    const half = (x) => {
        let s = simpOr(div(x, num(2)));
        const la = linArg(s, v);
        if (la && la.k.isNeg()) s = simpOr(neg(s));
        return s;
    };
    const sum = half(add(A.u, B.u));
    const dif = half(add(A.u, neg(B.u)));
    if (!linArg(sum, v) || !linArg(dif, v)) return null;
    const [G1, G2] = A.F === 'sin' ? (plus ? ['sin', 'cos'] : ['cos', 'sin']) : plus ? ['cos', 'cos'] : ['sin', 'sin'];
    const name = A.F === 'sin' ? (plus ? T('Сумма синусов', 'A sum of sines') : T('Разность синусов', 'A difference of sines')) : plus ? T('Сумма косинусов', 'A sum of cosines') : T('Разность косинусов', 'A difference of cosines');
    const lhsT = (l) => `${tex(fn(A.F, A.u), l)} ${plus ? '+' : '-'} ${tex(fn(B.F, B.u), l)}`;
    const prodT = (l) => `${A.F === 'cos' && !plus ? '-' : ''}2${tex(fn(G1, sum), l)}${tex(fn(G2, dif), l)}`;
    const steps = [S(T(`${name.ru}: переходим к произведению`, `${name.en}: turn it into a product`), {
        tex: byLang((l) => `${lhsT(l)} = ${prodT(l)} = 0`),
        text: T('Произведение равно нулю, когда один из множителей равен нулю.', 'A product is zero when one of the factors is zero.'),
    })];
    const families = [];
    for (const [G, w] of [[G1, sum], [G2, dif]]) {
        const b = basicTrig(G, w, N0, ctx);
        if (!b) return null;
        families.push(...b.families);
        steps.push(...b.steps);
    }
    return { families, steps };
}

/**
 * F(A) = ±G(B) with different arguments: tg 3x = tg x ⇔ 3x = x + πn; sin A = cos B ⇔ A = π/2 − B + 2πn or
 * A = π/2 + B + 2πn; tg A = ctg B ⇔ A = π/2 − B + πn. (sin/sin and cos/cos go through sumToProduct.)
 * Points where a side is undefined are dropped later by the ОДЗ check of the families.
 */
function equalTrig(E, ctx) {
    const v = ctx.v;
    if (E.type !== 'add' || E.args.length !== 2) return null;
    let [P, R] = E.args.map((t) => trigTerm(t, v));
    if (!P || !R) return null;
    const sgn = P.c.eq(R.c.neg()) ? 1 : P.c.eq(R.c) ? -1 : 0;
    if (!sgn) return null;
    const key = `${P.F},${R.F}`;
    const half = mul(num(Q.HALF), PI);
    const twoPi = mul(num(2), PI);
    // X = c + σ·Y + period·n, X and Y being the arguments A and B (or B and A)
    const A = P.u;
    const B = R.u;
    let rels;
    let rule;
    const pm = sgn > 0 ? '' : '-';
    if (key === 'tan,tan' || key === 'cot,cot') {
        rels = [{ X: A, Y: B, c: N0, s: sgn, P: PI }];
        const f = key === 'tan,tan' ? 'tg' : 'ctg';
        rule = byLang((l) => {
            const F = l === 'ru' ? `\\operatorname{${f}}` : key === 'tan,tan' ? '\\tan' : '\\cot';
            return l === 'ru'
                ? `$${F} a = ${F} b \\Leftrightarrow a = b + \\pi n$ (там, где обе части определены — это проверим по ОДЗ).${sgn < 0 ? ` Здесь $-${F} b = ${F}(-b)$.` : ''}`
                : `$${F} a = ${F} b \\Leftrightarrow a = b + \\pi n$ (where both sides are defined, which the domain check takes care of).${sgn < 0 ? ` Here $-${F} b = ${F}(-b)$.` : ''}`;
        });
    } else if (key === 'tan,cot' || key === 'cot,tan') {
        const [X, Y] = key === 'tan,cot' ? [A, B] : [B, A];
        rels = [{ X, Y, c: half, s: -sgn, P: PI }];
        rule = T('$\\operatorname{ctg} b = \\operatorname{tg}\\left(\\frac{\\pi}{2} - b\\right)$, а $\\operatorname{tg} a = \\operatorname{tg} c \\Leftrightarrow a = c + \\pi n$.', '$\\cot b = \\tan\\left(\\frac{\\pi}{2} - b\\right)$, and $\\tan a = \\tan c \\Leftrightarrow a = c + \\pi n$.');
    } else if (key === 'sin,cos' || key === 'cos,sin') {
        const [X, Y] = key === 'sin,cos' ? [A, B] : [B, A];
        rels = sgn > 0
            ? [{ X, Y, c: half, s: -1, P: twoPi }, { X, Y, c: half, s: 1, P: twoPi }]
            : [{ X, Y, c: neg(half), s: 1, P: twoPi }, { X, Y, c: mul(num(new Q(3n, 2n)), PI), s: -1, P: twoPi }];
        rule = sgn > 0
            ? T('$\\cos b = \\sin\\left(\\frac{\\pi}{2} - b\\right)$, а $\\sin a = \\sin c \\Leftrightarrow a = c + 2\\pi n$ или $a = \\pi - c + 2\\pi n$.', '$\\cos b = \\sin\\left(\\frac{\\pi}{2} - b\\right)$, and $\\sin a = \\sin c \\Leftrightarrow a = c + 2\\pi n$ or $a = \\pi - c + 2\\pi n$.')
            : T('$-\\cos b = \\sin\\left(b - \\frac{\\pi}{2}\\right)$, а $\\sin a = \\sin c \\Leftrightarrow a = c + 2\\pi n$ или $a = \\pi - c + 2\\pi n$.', '$-\\cos b = \\sin\\left(b - \\frac{\\pi}{2}\\right)$, and $\\sin a = \\sin c \\Leftrightarrow a = c + 2\\pi n$ or $a = \\pi - c + 2\\pi n$.');
    } else return null;
    const families = [];
    const lines = [];
    for (const r of rels) {
        const lx = linArg(r.X, v);
        const ly = linArg(r.Y, v);
        if (!lx || !ly) return null;
        const K = lx.k.sub(ly.k.mul(r.s));
        if (K.isZero()) return null;
        // (kX − σkY)·x = c − sX + σ·sY + P·n
        const base = simpOr(div(add(r.c, neg(lx.s), mul(num(r.s), ly.s)), num(K)));
        families.push(mkFamily(base, div(r.P, num(K.abs()))));
        const t = simpOr(add(r.c, mul(num(r.s), r.Y)));
        lines.push((l) => `${tex(r.X, l)} = ${plusTex([...(t.type === 'add' ? t.args : [t]), periodN(simpOr(r.P))], l)}`);
    }
    const eqT = (l) => `${tex(fn(P.F, A), l)} = ${pm}${tex(fn(R.F, B), l)}`;
    const steps = [
        S(byLang((l) => (l === 'ru' ? `Приравниваем аргументы: $${eqT(l)}$` : `Compare the arguments: $${eqT(l)}$`)), {
            tex: byLang((l) => lines.map((f) => f(l)).join(`${orTex(l)} `) + ZZ(l)),
            text: rule,
        }),
        S(T(`Выражаем $${v}$`, `Solve for $${v}$`), { tex: byLang((l) => families.map((f) => familyTex(f, v, l)).join(l === 'ru' ? ';\\quad ' : ',\\quad ') + ZZ(l)) }),
    ];
    return { families, steps };
}

function trigMultiArg(E, tn, args, ctx) {
    const sp = sumToProduct(E, ctx);
    if (sp) return sp;
    // the textbook double-angle route first (sin 2x = cos x), then comparing the arguments (sin 3x = cos x)
    return doubleAngle(E, tn, args, ctx) ?? equalTrig(E, ctx);
}

function doubleAngle(E, tn, args, ctx) {
    const v = ctx.v;
    if (ctx.trigDepth) return null;
    const las = args.map((u) => ({ u, la: linArg(u, v) }));
    if (las.some((x) => !x.la)) return null;
    las.sort((a, b) => a.la.k.abs().cmp(b.la.k.abs()));
    const u0 = las[0];
    for (const x of las.slice(1)) {
        if (!x.la.k.eq(u0.la.k.mul(2)) || exactZero(add(x.la.s, mul(num(-2), u0.la.s))) !== true) return null;
    }
    const k0 = nodeKey(u0.u);
    const at0 = tn.filter((t) => nodeKey(t.args[0]) === k0).map((t) => t.name);
    const onlySin = at0.length > 0 && at0.every((n) => n === 'sin');
    const onlyCos = at0.length > 0 && at0.every((n) => n === 'cos');
    const u = u0.u;
    const S_ = fn('sin', u);
    const C_ = fn('cos', u);
    const reps = [];
    let E2 = E;
    for (const t of tn) {
        if (nodeKey(t.args[0]) === k0) continue;
        let r;
        if (t.name === 'sin') r = mul(num(2), S_, C_);
        else if (t.name === 'cos') r = onlyCos ? add(mul(num(2), pow(C_, num(2))), num(-1)) : onlySin ? add(N1, mul(num(-2), pow(S_, num(2)))) : add(pow(C_, num(2)), neg(pow(S_, num(2))));
        else return null;
        reps.push([t, r]);
        E2 = replaceNode(E2, t, r);
    }
    const E3 = expd(E2);
    if (!E3) return null;
    const pre = S(T('Формулы двойного угла', 'Double-angle formulas'), {
        tex: byLang((l) => reps.map(([t, r]) => `${tex(t, l)} = ${tex(r, l)}`).join(';\\quad ') + `\\;\\Rightarrow\\; ${tex(E3, l)} = 0`),
        text: T('Переходим к одному аргументу.', 'Now there is a single argument.'),
    });
    const r = trigCore(E3, { ...ctx, trigDepth: 1 });
    return r && { families: r.families, steps: [pre, ...r.steps] };
}
