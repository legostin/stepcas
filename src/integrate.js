// integrate — antiderivatives with steps: a cascade of methods, each one explaining why it applies;
// definite integrals (Newton–Leibniz, improper integrals as limits, a numeric value marked ≈ otherwise)
// and the area between two curves.
//
// Cascade (on the canonical form of simplify.js): constant → table → linearity → linear substitution
// f(kx + b) → rational functions (division, partial fractions over Q, completing the square) → expand →
// trigonometric forms (odd powers, power reduction, t = tg x, product to sum) → u-substitution
// g(h(x))·h′(x) → quadratics under a root → rationalising substitution t = ⁿ√(ax + b) → integration by
// parts (LIATE, repeated, cyclic eᵃˣ·sin bx) → universal substitution t = tg(x/2).
// Every candidate antiderivative is checked by differentiating it back and comparing with the integrand
// at sample points of its domain; an answer that fails the check is never shown.

import { Q, MathError, bigLcm } from './rational.js';
import { num, sym, add, mul, div, neg, pow, fn, isConst, containsVar, freeVars, nodeKey, substitute, mapNode, toNode, nodeChildren, nodeSize, nodeSome } from './ast.js';
import { parse } from './parse.js';
import { simplify, canonContext, splitCoeff } from './simplify.js';
import { expand } from './expand.js';
import { Poly } from './poly.js';
import { evaluate, compile } from './evaluate.js';
import { step } from './steps.js';
import { rng } from './random.js';
import { numIntegrate, numFindRoots } from './numeric.js';
import { quickDerivative, niceForm, prettyForm, calcTex, ratFunctionOf } from './diff.js';
import { limit } from './limit.js';

const N0 = num(0);
const N1 = num(1);
const NM1 = num(-1);
const N2 = num(2);
const HALF = num(Q.HALF);
const PI = sym('pi');
const E_ = sym('e');

const isNum = (n) => n.type === 'num';
const isZero = (n) => isNum(n) && n.value.isZero();
const isOne = (n) => isNum(n) && n.value.isOne();
const T_ = (ru, en) => ({ ru, en });
const q = (a, b = 1n) => new Q(BigInt(a), BigInt(b));

// ---------------------------------------------------------------- small helpers

function asNode(x) {
    if (x && typeof x === 'object' && typeof x.type === 'string') return x;
    if (typeof x === 'string') return parse(x);
    return toNode(x);
}

function simp(node) {
    let s = simplify(node);
    for (let i = 0; i < 3; i++) {
        const t = simplify(s);
        if (nodeKey(t) === nodeKey(s)) break;
        s = t;
    }
    return s;
}

function trySimp(node) {
    try {
        return simp(node);
    } catch {
        return null;
    }
}

function bt(f) {
    const ru = f('ru');
    const en = f('en');
    return ru === en ? ru : { ru, en };
}

const tall = (s) => /\\frac|\\sqrt|\\left|\\dfrac|\^\{/.test(s);
const paren = (s) => (tall(s) ? `\\left(${s}\\right)` : `(${s})`);

function negLeading(n) {
    if (isNum(n)) return n.value.isNeg();
    if (n.type === 'neg') return true;
    if (n.type === 'mul') return n.args.length > 0 && negLeading(n.args[0]);
    return false;
}

const isVar = (n, v) => n.type === 'sym' && n.name === v && !isConst(n);

/** TeX of ∫ f dv. */
function iTex(f, v, L) {
    if (isOne(f)) return `\\int d${v}`;
    const s = calcTex(f, L);
    return `\\int ${f.type === 'add' || negLeading(f) ? paren(s) : s}\\,d${v}`;
}

/** TeX of a node for the right-hand side of a step. */
const tx = (n, L) => calcTex(n, L);

/** A multiplier in front of something: 3, -\frac{1}{2}, (a + 1). */
function coefTex(c, L) {
    if (isOne(c)) return '';
    if (isNum(c) && c.value.eq(-1)) return '-';
    const s = calcTex(c, L);
    return c.type === 'add' ? paren(s) : s;
}

/** "k dx" for a differential: dx, −dx, 3\\,dx, (2x + 1)\\,dx. */
function dTex(k, v, L) {
    if (isOne(k)) return `d${v}`;
    if (isNum(k) && k.value.eq(-1)) return `-d${v}`;
    const s = calcTex(k, L);
    return `${k.type === 'add' ? paren(s) : s}\\,d${v}`;
}

function freshVar(f, v) {
    const used = new Set([...freeVars(f), v]);
    for (const t of ['t', 'u', 'w', 's', 'z', 'p', 'r']) if (!used.has(t)) return t;
    return 't_1';
}

/** Linear in v with coefficients free of v: {k, b} (nodes, k ≠ 0), else null. */
function linearParts(L, v) {
    if (!containsVar(L, v)) return null;
    let k;
    try {
        k = simp(quickDerivative(L, v));
    } catch {
        return null;
    }
    if (containsVar(k, v) || isZero(k)) return null;
    const b = trySimp(add(L, mul(NM1, k, sym(v))));
    if (!b || containsVar(b, v)) return null;
    return { k, b };
}

// ---------------------------------------------------------------- positivity (ln|u| or ln u)

function surelyPositive(u, v) {
    if (isNum(u)) return u.value.isPos();
    if (isConst(u)) return u.name === 'pi' || u.name === 'e';
    if (u.type === 'pow') {
        if (isConst(u.base) && u.base.name === 'e') return true;
        if (isNum(u.base) && u.base.value.isPos()) return true;
        if (surelyPositive(u.base, v)) return true;
        return false;
    }
    if (u.type === 'mul') return u.args.every((f) => surelyPositive(f, v));
    if (u.type === 'fn') return u.name === 'cosh' || u.name === 'exp';
    if (u.type === 'add') {
        // Σ nonnegative with a positive constant; or a quadratic with no real roots
        let pos = false;
        let ok = true;
        for (const t of u.args) {
            if (isNum(t)) {
                if (t.value.isPos()) pos = true;
                else ok = false;
            } else if (!nonNegative(t)) ok = false;
        }
        if (ok && pos) return true;
        const P = Poly.fromNode(u, v);
        if (P && P.degree === 2 && P.lead.isPos() && P.discriminant().isNeg()) return true;
        return false;
    }
    return false;
}

function nonNegative(t) {
    const { coef, rest } = splitCoeff(t);
    if (coef.isNeg() || rest === null) return !coef.isNeg();
    const fs = rest.type === 'mul' ? rest.args : [rest];
    return fs.every((f) => {
        if (f.type === 'pow' && isNum(f.exp) && f.exp.value.isInt() && f.exp.value.n % 2n === 0n) return true;
        if (f.type === 'pow' && isNum(f.exp) && f.exp.value.d % 2n === 0n) return true; // even roots, where defined
        if (f.type === 'pow' && isConst(f.base) && f.base.name === 'e') return true;
        if (f.type === 'fn' && (f.name === 'abs' || f.name === 'cosh')) return true;
        if (isNum(f) || (isConst(f) && f.name !== 'i')) return true;
        return false;
    });
}

function lnAbs(u, v) {
    return surelyPositive(u, v) ? fn('ln', u) : fn('ln', fn('abs', u));
}

// ---------------------------------------------------------------- the check: F′ = f on the domain

const RANGES = [[0.2, 1.8], [-1.8, -0.2], [2, 6], [-6, -2], [0.05, 0.95], [-0.95, -0.05], [6, 20], [-20, -6], [20, 200], [-200, -20]];

/**
 * Is F an antiderivative of f? true / false / null (too few usable points). Points where f is finite but F
 * is not count as a failure (ln x for 1/x is wrong for x < 0).
 */
function checkAnti(F, f, v, opts = {}) {
    let dF;
    try {
        dF = quickDerivative(F, v);
    } catch {
        return null;
    }
    // exact check first: F′ − f expands to 0 (then only the domain matters; big coefficients such as
    // those of ∫x²⁰eˣ lose too much precision in floating point to compare numerically)
    let exact = false;
    if (nodeSize(dF) + nodeSize(f) < 600) {
        try {
            const d = simp(expand(add(dF, neg(f))));
            exact = isZero(d);
        } catch {
            exact = false;
        }
    }
    const r = rng(opts.seed ?? 4242);
    const others = [...new Set([...freeVars(F), ...freeVars(f)])].filter((w) => w !== v);
    let usable = 0;
    let bad = 0;
    for (let k = 0; k < 40; k++) {
        const env = {};
        for (const w of others) env[w] = r.real(0.6, 1.9);
        const [lo, hi] = RANGES[k % RANGES.length];
        env[v] = r.real(lo, hi);
        let fv;
        let dv;
        let Fv;
        try {
            fv = evaluate(f, env);
            if (!Number.isFinite(fv) || Math.abs(fv) > 1e10) continue;
            dv = evaluate(dF, env);
            Fv = evaluate(F, env);
        } catch {
            return null;
        }
        if (!Number.isFinite(Fv) || !Number.isFinite(dv)) {
            // f is defined here but the answer is not: allowed only at isolated points
            const env2 = { ...env, [v]: env[v] * (1 + 1e-6) + 1e-7 };
            let F2;
            try {
                F2 = evaluate(F, env2);
            } catch {
                return null;
            }
            if (!Number.isFinite(F2)) bad++;
            if (bad >= 2) return false;
            continue;
        }
        usable++;
        if (!exact && Math.abs(dv - fv) > 1e-6 * Math.max(1, Math.abs(fv), Math.abs(dv))) return false;
        if (usable >= 14) break;
    }
    if (exact) return true;
    return usable >= 3 ? true : null;
}

// ---------------------------------------------------------------- the recursive integrator

/**
 * I(f, ctx) → {F, step, method} | null for a canonical integrand f (ctx.v is the variable).
 * Each method returns a candidate; a candidate that fails checkAnti is dropped and the next method tried.
 */
function I(f, ctx) {
    const b = ctx.budget;
    if (++b.calls > b.max || ctx.depth > 14) return null;
    const key = ctx.v + '|' + nodeKey(f);
    if (b.memo.has(key)) return b.memo.get(key);
    b.memo.set(key, null); // in progress: a cycle ends here
    let res = null;
    for (const m of METHODS) {
        let r = null;
        try {
            r = m(f, { ...ctx, depth: ctx.depth + 1 });
        } catch (e) {
            if (!(e instanceof MathError)) throw e;
            r = null;
        }
        if (!r) continue;
        let F;
        try {
            F = simp(r.F);
        } catch {
            continue;
        }
        const ok = checkAnti(F, f, ctx.v);
        if (ok === false) continue;
        if (ok === null && ctx.depth === 0 && !r.trust) continue;
        res = { ...r, F };
        break;
    }
    b.memo.set(key, res);
    return res;
}

function sub(ctx, extra = {}) {
    return { ...ctx, ...extra };
}

// ---- constant and table

function mConst(f, ctx) {
    const { v } = ctx;
    if (containsVar(f, v)) return null;
    const F = mul(f, sym(v));
    return {
        F,
        method: 'constant',
        step: step({
            title: T_('Интеграл от постоянной', 'Integral of a constant'),
            tex: bt((L) => `${iTex(f, v, L)} = ${tx(simp(F), L)}`),
            text: T_(`Подынтегральная функция не зависит от ${v}: ∫c d${v} = c·${v} + C.`, `The integrand does not depend on ${v}: ∫c d${v} = c·${v} + C.`),
            rule: 'const',
        }),
    };
}

function quadIs(P, c0, c1, c2) {
    return P && P.degree === 2 && P.coeff(0).eq(c0) && P.coeff(1).eq(c1) && P.coeff(2).eq(c2);
}

function tableOf(f, v) {
    const X = sym(v);
    if (isVar(f, v)) return { F: div(pow(X, N2), N2), law: T_(`∫${v} d${v} = ${v}²/2 + C`, `∫${v} d${v} = ${v}²/2 + C`) };
    if (f.type === 'pow' && isVar(f.base, v) && !containsVar(f.exp, v)) {
        const e = f.exp;
        if (isNum(e) && e.value.eq(-1)) return { F: lnAbs(X, v), law: T_(`∫d${v}/${v} = ln|${v}| + C`, `∫d${v}/${v} = ln|${v}| + C`) };
        const e1 = simp(add(e, N1));
        return { F: div(pow(X, e1), e1), law: T_(`∫${v}ⁿ d${v} = ${v}ⁿ⁺¹/(n + 1) + C (n ≠ −1)`, `∫${v}ⁿ d${v} = ${v}ⁿ⁺¹/(n + 1) + C (n ≠ −1)`), note: !isNum(e) };
    }
    if (f.type === 'pow' && !containsVar(f.base, v) && isVar(f.exp, v)) {
        if (isConst(f.base) && f.base.name === 'e') return { F: f, law: T_(`∫e^${v} d${v} = e^${v} + C`, `∫e^${v} d${v} = e^${v} + C`) };
        return { F: div(f, fn('ln', f.base)), law: T_(`∫a^${v} d${v} = a^${v}/ln a + C`, `∫a^${v} d${v} = a^${v}/ln a + C`) };
    }
    if (f.type === 'fn' && f.args.length === 1 && isVar(f.args[0], v)) {
        const T = {
            sin: [neg(fn('cos', X)), '∫sin x dx = −cos x + C'],
            cos: [fn('sin', X), '∫cos x dx = sin x + C'],
            tan: [neg(lnAbs(fn('cos', X), v)), ['∫tg x dx = −ln|cos x| + C', '∫tan x dx = −ln|cos x| + C']],
            cot: [lnAbs(fn('sin', X), v), ['∫ctg x dx = ln|sin x| + C', '∫cot x dx = ln|sin x| + C']],
            sinh: [fn('cosh', X), ['∫sh x dx = ch x + C', '∫sinh x dx = cosh x + C']],
            cosh: [fn('sinh', X), ['∫ch x dx = sh x + C', '∫cosh x dx = sinh x + C']],
            tanh: [fn('ln', fn('cosh', X)), ['∫th x dx = ln ch x + C', '∫tanh x dx = ln cosh x + C']],
            coth: [lnAbs(fn('sinh', X), v), ['∫cth x dx = ln|sh x| + C', '∫coth x dx = ln|sinh x| + C']],
            abs: [div(mul(X, fn('abs', X)), N2), '∫|x| dx = x|x|/2 + C'],
            sign: [fn('abs', X), '∫sgn x dx = |x| + C'],
            sec: [lnAbs(add(fn('sec', X), fn('tan', X)), v), ['∫sec x dx = ln|sec x + tg x| + C', '∫sec x dx = ln|sec x + tan x| + C']],
            csc: [lnAbs(fn('tan', div(X, N2)), v), ['∫cosec x dx = ln|tg(x/2)| + C', '∫csc x dx = ln|tan(x/2)| + C']],
        }[f.name];
        if (!T) return null;
        const [ru, en] = Array.isArray(T[1]) ? T[1] : [T[1], T[1]];
        return { F: T[0], law: T_(ru.replace(/x/g, v), en.replace(/x/g, v)) };
    }
    if (f.type === 'pow' && isNum(f.exp) && f.base.type === 'fn' && f.base.args.length === 1 && isVar(f.base.args[0], v)) {
        const e = f.exp.value;
        const nm = f.base.name;
        const hit = (name, k) => nm === name && e.eq(k);
        if (hit('cos', -2) || hit('sec', 2)) return { F: fn('tan', X), law: T_('∫dx/cos² x = tg x + C', '∫dx/cos² x = tan x + C') };
        if (hit('sin', -2) || hit('csc', 2)) return { F: neg(fn('cot', X)), law: T_('∫dx/sin² x = −ctg x + C', '∫dx/sin² x = −cot x + C') };
        if (hit('cosh', -2)) return { F: fn('tanh', X), law: T_('∫dx/ch² x = th x + C', '∫dx/cosh² x = tanh x + C') };
        if (hit('sinh', -2)) return { F: neg(fn('coth', X)), law: T_('∫dx/sh² x = −cth x + C', '∫dx/sinh² x = −coth x + C') };
        if (hit('cos', -1)) return { F: lnAbs(fn('tan', add(div(X, N2), div(PI, num(4)))), v), law: T_('∫dx/cos x = ln|tg(x/2 + π/4)| + C', '∫dx/cos x = ln|tan(x/2 + π/4)| + C') };
        if (hit('sin', -1)) return { F: lnAbs(fn('tan', div(X, N2)), v), law: T_('∫dx/sin x = ln|tg(x/2)| + C', '∫dx/sin x = ln|tan(x/2)| + C') };
        return null;
    }
    if (f.type === 'pow' && isNum(f.exp) && f.base.type === 'add') {
        const P = Poly.fromNode(f.base, v);
        const e = f.exp.value;
        if (e.eq(-1) && quadIs(P, 1, 0, 1)) return { F: fn('atan', X), law: T_('∫dx/(1 + x²) = arctg x + C', '∫dx/(1 + x²) = arctan x + C') };
        if (e.eq(q(-1, 2)) && quadIs(P, 1, 0, -1)) return { F: fn('asin', X), law: T_('∫dx/√(1 − x²) = arcsin x + C', '∫dx/√(1 − x²) = arcsin x + C') };
        if (e.eq(q(-1, 2)) && quadIs(P, 1, 0, 1)) return { F: fn('ln', add(X, fn('sqrt', add(pow(X, N2), N1)))), law: T_('∫dx/√(x² + 1) = ln(x + √(x² + 1)) + C', '∫dx/√(x² + 1) = ln(x + √(x² + 1)) + C') };
        if (e.eq(q(-1, 2)) && quadIs(P, -1, 0, 1)) return { F: lnAbs(add(X, fn('sqrt', add(pow(X, N2), NM1))), v), law: T_('∫dx/√(x² − 1) = ln|x + √(x² − 1)| + C', '∫dx/√(x² − 1) = ln|x + √(x² − 1)| + C') };
    }
    return null;
}

function mTable(f, ctx) {
    const { v } = ctx;
    const t = tableOf(f, v);
    if (!t) return null;
    const F = t.F;
    return {
        F,
        method: 'table',
        step: step({
            title: T_('Табличный интеграл', 'Table integral'),
            tex: bt((L) => `${iTex(f, v, L)} = ${tx(trySimp(F) ?? F, L)}`),
            text: t.note
                ? T_(`Из таблицы: ${t.law.ru} (при показателе, не равном −1).`, `From the table: ${t.law.en} (for an exponent other than −1).`)
                : T_(`Из таблицы интегралов: ${t.law.ru}.`, `From the table of integrals: ${t.law.en}.`),
            rule: 'table',
        }),
    };
}

// ---- linearity

function mLinearity(f, ctx) {
    const { v } = ctx;
    if (f.type === 'mul') {
        const consts = f.args.filter((a) => !containsVar(a, v));
        if (!consts.length) return null;
        const rest = f.args.filter((a) => containsVar(a, v));
        const c = simp(mul(consts));
        const g = simp(rest.length === 1 ? rest[0] : mul(rest));
        const r = I(g, ctx);
        if (!r) return null;
        const F = mul(c, r.F);
        return {
            F,
            method: r.method,
            step: step({
                title: T_('Постоянный множитель', 'Constant factor'),
                tex: bt((L) => `${iTex(f, v, L)} = ${coefTex(c, L)}${iTex(g, v, L)} = ${tx(simp(F), L)}`),
                text: T_('Постоянный множитель выносим за знак интеграла: ∫c·f dx = c·∫f dx.', 'A constant factor comes out of the integral: ∫c·f dx = c·∫f dx.'),
                rule: 'const-factor',
                sub: [r.step],
            }),
        };
    }
    if (f.type === 'add') {
        const parts = [];
        for (const t of f.args) {
            const r = I(t, ctx);
            if (!r) return null;
            parts.push({ t, r });
        }
        const F = add(parts.map((p) => p.r.F));
        const methods = [...new Set(parts.map((p) => p.r.method))];
        return {
            F,
            method: methods.length === 1 ? methods[0] : 'linearity',
            step: step({
                title: T_('Интеграл суммы', 'Integral of a sum'),
                tex: bt((L) => `${iTex(f, v, L)} = ${parts.map((p, i) => {
                    if (negLeading(p.t)) return (i === 0 ? '-' : ' - ') + iTex(simp(neg(p.t)), v, L);
                    const s = iTex(p.t, v, L);
                    return i === 0 ? s : ' + ' + s;
                }).join('')} = ${tx(simp(F), L)}`),
                text: T_('Интеграл суммы равен сумме интегралов: берём каждое слагаемое отдельно, постоянные выносим.', 'The integral of a sum is the sum of the integrals: take each term separately, constants come out.'),
                rule: 'sum',
                sub: parts.map((p) => p.r.step),
            }),
        };
    }
    return null;
}

// ---- linear substitution f(kx + b)

function linearCandidates(f, v) {
    const out = new Map();
    const visit = (n) => {
        if (!containsVar(n, v)) return;
        const kids = n.type === 'fn' ? n.args : n.type === 'pow' ? [n.base, n.exp] : [];
        for (const c of kids) {
            if (containsVar(c, v) && !isVar(c, v) && linearParts(c, v)) out.set(nodeKey(c), c);
        }
        for (const c of nodeChildren(n)) visit(c);
    };
    visit(f);
    return [...out.values()];
}

/** Pre-order transform: fnc(node) → replacement (not descended into) or undefined to go deeper. */
function mapPre(n, fnc) {
    const r = fnc(n);
    if (r !== undefined) return r;
    const kids = nodeChildren(n);
    if (!kids.length) return n;
    const nk = kids.map((c) => mapPre(c, fnc));
    if (nk.every((c, i) => c === kids[i])) return n;
    switch (n.type) {
        case 'add':
            return add(nk);
        case 'mul':
            return mul(nk);
        case 'div':
            return div(nk[0], nk[1]);
        case 'neg':
            return neg(nk[0]);
        case 'pow':
            return pow(nk[0], nk[1]);
        case 'fn':
            return fn(n.name, ...nk);
        default:
            return n;
    }
}

function replaceNode(f, target, by) {
    const key = nodeKey(target);
    return mapPre(f, (m) => (nodeKey(m) === key ? by : undefined));
}

function mLinearSub(f, ctx) {
    const { v } = ctx;
    for (const Lx of linearCandidates(f, v)) {
        const t = freshVar(f, v);
        const T = sym(t);
        const g0 = replaceNode(f, Lx, T);
        if (containsVar(g0, v)) continue;
        const g = trySimp(g0);
        if (!g) continue;
        const { k } = linearParts(Lx, v);
        const r = I(g, sub(ctx, { v: t }));
        if (!r) continue;
        const F = mul(div(N1, k), substitute(r.F, { [t]: Lx }));
        return {
            F,
            method: r.method === 'table' ? 'linear-substitution' : r.method,
            step: step({
                title: T_('Линейная замена', 'Linear substitution'),
                tex: bt((L) => `${iTex(f, v, L)} = \\left[${t} = ${tx(Lx, L)},\\ d${t} = ${dTex(k, v, L)}\\right] = ${coefTex(simp(div(N1, k)), L)}${iTex(g, t, L)} = ${tx(simp(F), L)}`),
                text: T_(`Под функцией стоит линейное выражение ${plainish(Lx, 'ru')}. Если ∫f(t)dt = F(t) + C, то ∫f(kx + b)dx = F(kx + b)/k + C: это замена t = kx + b, при которой dt = k·dx.`,
                    `The function is applied to a linear expression ${plainish(Lx, 'en')}. If ∫f(t)dt = F(t) + C, then ∫f(kx + b)dx = F(kx + b)/k + C: the substitution t = kx + b, dt = k·dx.`),
                rule: 'linear-substitution',
                sub: [r.step],
            }),
        };
    }
    return null;
}

function plainish(n, L) {
    return toTextSafe(prettyForm(n), L);
}

function toTextSafe(n, L) {
    try {
        let s = calcTex(n, L);
        s = s.replace(/\\left|\\right/g, '').replace(/\\operatorname\{(\w+)\}/g, '$1').replace(/\\cdot/g, '·').replace(/\\,/g, ' ');
        s = s.replace(/\\frac\{([^{}]*)\}\{([^{}]*)\}/g, '($1)/($2)').replace(/\\sqrt\{([^{}]*)\}/g, '√($1)').replace(/\^\{(-?\d+)\}/g, (m, d) => supDigits(d)).replace(/\\([a-z]+)/g, '$1');
        return s.replace(/[{}]/g, '').replace(/\s+/g, ' ').trim();
    } catch {
        return '';
    }
}

const SUP = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹', '-': '⁻' };
const supDigits = (d) => [...d].map((c) => SUP[c]).join('');

// ---- expand

function hasProductOfSums(f) {
    if (f.type === 'pow' && f.base.type === 'add' && isNum(f.exp) && f.exp.value.isInt() && f.exp.value.gt(1)) return true;
    if (f.type === 'mul') return f.args.some((a) => a.type === 'add' || (a.type === 'pow' && a.base.type === 'add' && isNum(a.exp) && a.exp.value.isInt() && a.exp.value.isPos()));
    return false;
}

function mExpand(f, ctx) {
    const { v } = ctx;
    if (!hasProductOfSums(f)) return null;
    let X;
    try {
        X = simp(expand(f));
    } catch {
        return null;
    }
    if (X.type !== 'add' || X.args.length > 60 || nodeKey(X) === nodeKey(f)) return null;
    const r = I(X, ctx);
    if (!r) return null;
    return {
        F: r.F,
        method: r.method,
        step: step({
            title: T_('Раскрываем скобки', 'Expand'),
            tex: bt((L) => `${iTex(f, v, L)} = ${iTex(X, v, L)}`),
            text: T_('После раскрытия скобок получается сумма простых слагаемых, каждое из которых интегрируется по таблице.', 'Multiplying out gives a sum of simple terms, each of which is a table integral.'),
            rule: 'expand',
            sub: [r.step],
        }),
    };
}

// ---- f = c·h′·hᵏ: the inner function's derivative is a factor (∫h′/h = ln|h|, ∫h′hᵏ = hᵏ⁺¹/(k + 1))

function mDerivPattern(f, ctx) {
    const { v } = ctx;
    const { rest } = splitCoeff(f);
    if (!rest) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    for (const x of fs) {
        const h = x.type === 'pow' && isNum(x.exp) ? x.base : x.type === 'fn' ? null : null;
        if (!h || !containsVar(h, v) || isVar(h, v) || linearParts(h, v)) continue;
        const k = x.exp.value;
        let dh;
        try {
            dh = simp(quickDerivative(h, v));
        } catch {
            continue;
        }
        if (isZero(dh)) continue;
        const c = trySimp(mul(f, pow(h, num(k.neg())), pow(dh, NM1)));
        if (!c || containsVar(c, v)) continue;
        const F = k.eq(-1) ? mul(c, lnAbs(h, v)) : mul(c, div(pow(h, num(k.add(Q.ONE))), qn(k.add(Q.ONE))));
        const law = k.eq(-1)
            ? T_(`В числителе стоит (с точностью до множителя) производная знаменателя: ∫h′/h dx = ln|h| + C, где h = ${plainish(h, 'ru')}.`, `The numerator is (up to a factor) the derivative of the denominator: ∫h′/h dx = ln|h| + C with h = ${plainish(h, 'en')}.`)
            : T_(`Множителем стоит (с точностью до постоянной) производная выражения h = ${plainish(h, 'ru')}: ∫hᵏ·h′ dx = hᵏ⁺¹/(k + 1) + C — это замена t = h.`, `The derivative of h = ${plainish(h, 'en')} is (up to a constant) a factor: ∫hᵏ·h′ dx = hᵏ⁺¹/(k + 1) + C, i.e. the substitution t = h.`);
        return {
            F,
            method: 'substitution',
            step: step({
                title: k.eq(-1) ? T_('Производная знаменателя в числителе', 'The derivative of the denominator on top') : T_('Производная внутренней функции — множитель', 'The inner derivative is a factor'),
                tex: bt((L) => `${iTex(f, v, L)} = \\left[t = ${tx(h, L)},\\ dt = ${dTex(dh, v, L)}\\right] = ${tx(trySimp(F) ?? F, L)}`),
                text: law,
                rule: 'substitution',
            }),
        };
    }
    return null;
}

// ---- rational functions

function solveQ(A, b) {
    const n = A.length;
    const M = A.map((row, i) => [...row, b[i]]);
    for (let col = 0; col < n; col++) {
        let p = col;
        while (p < n && M[p][col].isZero()) p++;
        if (p === n) return null;
        [M[col], M[p]] = [M[p], M[col]];
        const inv = M[col][col].inv();
        for (let j = col; j <= n; j++) M[col][j] = M[col][j].mul(inv);
        for (let i = 0; i < n; i++) {
            if (i === col || M[i][col].isZero()) continue;
            const k = M[i][col];
            for (let j = col; j <= n; j++) M[i][j] = M[i][j].sub(k.mul(M[col][j]));
        }
    }
    return M.map((row) => row[n]);
}

const qn = (x) => num(x);

/** ∫ A/(ax + b)^k dx */
function intLinearPiece(A, lin, k, v) {
    const a = lin.coeff(1);
    const base = lin.toNode(v);
    if (k === 1) return mul(qn(A.div(a)), lnAbs(base, v));
    return mul(qn(A.neg().div(a.mul(k - 1))), pow(base, num(1 - k)));
}

/** ∫ dt/(t² + m2)^k (m2 > 0 rational, t a node) by the reduction formula. */
function intJ(k, tNode, m2) {
    const m = pow(qn(m2), HALF);
    if (k === 1) return mul(div(N1, m), fn('atan', div(tNode, m)));
    const kk = k - 1;
    const first = div(tNode, mul(qn(m2.mul(2 * kk)), pow(add(pow(tNode, N2), qn(m2)), num(kk))));
    const coef = qn(q(2 * k - 3).div(m2.mul(2 * kk)));
    return add(first, mul(coef, intJ(k - 1, tNode, m2)));
}

/** ∫ (Bx + C)/(ax² + bx + c)^k dx for a quadratic without rational roots. */
function intQuadPiece(B, Cc, quad, k, v) {
    const X = sym(v);
    const [c, b, a] = [quad.coeff(0), quad.coeff(1), quad.coeff(2)];
    const qNode = quad.toNode(v);
    const M = B.div(a.mul(2));
    const Nn = Cc.sub(B.mul(b).div(a.mul(2)));
    const disc = b.mul(b).sub(a.mul(c).mul(4));
    const parts = [];
    const lin2 = add(mul(qn(a.mul(2)), X), qn(b)); // 2ax + b
    if (k === 1) {
        if (!M.isZero()) parts.push(mul(qn(M), lnAbs(qNode, v)));
        if (!Nn.isZero()) {
            if (disc.isNeg()) {
                const s = pow(qn(disc.neg()), HALF);
                parts.push(mul(qn(Nn.mul(2)), div(N1, s), fn('atan', div(lin2, s))));
            } else {
                const s = pow(qn(disc), HALF);
                parts.push(mul(qn(Nn), div(N1, s), lnAbs(div(add(lin2, neg(s)), add(lin2, s)), v)));
            }
        }
        return add(parts);
    }
    if (!disc.isNeg()) return null;
    if (!M.isZero()) parts.push(mul(qn(M.div(1 - k)), pow(qNode, num(1 - k))));
    if (!Nn.isZero()) {
        const tNode = add(X, qn(b.div(a.mul(2))));
        const m2 = disc.neg().div(a.mul(a).mul(4));
        parts.push(mul(qn(Nn.mul(a.inv().pow(BigInt(k)))), intJ(k, tNode, m2)));
    }
    return add(parts);
}

/** A partial fraction for display: (2 − x)/(3(x² − x + 1)) rather than (2/3 − x/3)/(x² − x + 1), sign in front. */
function fracPiece(numP, denNode, v) {
    let P = numP;
    let sign = false;
    if (P.lead.isNeg() && P.c.every((c) => !c.isPos())) {
        sign = true;
        P = P.neg();
    }
    let l = 1n;
    for (const c of P.c) l = bigLcm(l, c.d);
    const top = P.scale(new Q(l)).toNode(v);
    const bottom = l === 1n ? denNode : mul(num(l), denNode);
    const d = div(top, bottom);
    return sign ? neg(d) : d;
}

function mRational(f, ctx) {
    const { v } = ctx;
    const r = ratFunctionOf(f, v);
    if (!r) return null;
    if (r.den.degree < 1) {
        // a polynomial in disguise, (x² − 1)/(x − 1) − x: integrate its plain form
        const P0 = canonicalRational(f, v);
        if (!P0 || nodeKey(P0) === nodeKey(f)) return null;
        const rp = I(P0, ctx);
        if (!rp) return null;
        return { ...rp, step: step({
            title: T_('Упрощаем дробь', 'Simplify the fraction'),
            tex: bt((L) => `${tx(f, L)} = ${tx(P0, L)}`),
            text: T_('Дробь сокращается, под интегралом остаётся многочлен.', 'The fraction cancels, leaving a polynomial under the integral.'),
            rule: 'simplify',
            sub: [rp.step],
        }) };
    }
    const P = r.num;
    const D = r.den;
    const { q: polyPart, r: rem } = P.divmod(D);
    const { constant, factors } = D.factor();
    if (factors.some((x) => x.poly.degree > 2)) return null;
    const X = sym(v);
    // partial fractions: unknowns per (factor, power)
    const terms = [];
    for (const { poly, mult } of factors) for (let k = 1; k <= mult; k++) terms.push({ poly, k });
    const N = D.degree;
    const cols = [];
    for (const t of terms) {
        const base = D.divmod(t.poly.pow(t.k)).q;
        if (t.poly.degree === 1) cols.push({ t, kind: 'A', p: base });
        else {
            cols.push({ t, kind: 'B', p: base.mul(new Poly([Q.ZERO, Q.ONE])) });
            cols.push({ t, kind: 'C', p: base });
        }
    }
    if (cols.length !== N) return null;
    const A = [];
    const bvec = [];
    for (let i = 0; i < N; i++) {
        A.push(cols.map((c) => c.p.coeff(i)));
        bvec.push(rem.coeff(i));
    }
    const sol = rem.isZero() ? cols.map(() => Q.ZERO) : solveQ(A, bvec);
    if (!sol) return null;
    const pieces = [];
    let ci = 0;
    for (const t of terms) {
        if (t.poly.degree === 1) {
            pieces.push({ t, A: sol[ci++] });
        } else {
            pieces.push({ t, B: sol[ci++], C: sol[ci++] });
        }
    }
    // integrate
    const Fparts = [];
    const subs = [];
    if (!polyPart.isZero()) {
        const pp = polyPart.toNode(v);
        const rp = I(simp(pp), ctx);
        if (!rp) return null;
        Fparts.push(rp.F);
        subs.push(rp.step);
    }
    const pieceNodes = [];
    for (const pc of pieces) {
        const denNode = pc.t.k === 1 ? pc.t.poly.toNode(v) : pow(pc.t.poly.toNode(v), num(pc.t.k));
        let node;
        let Fp;
        if (pc.t.poly.degree === 1) {
            if (pc.A.isZero()) continue;
            node = fracPiece(new Poly([pc.A]), denNode, v);
            Fp = intLinearPiece(pc.A, pc.t.poly, pc.t.k, v);
        } else {
            if (pc.B.isZero() && pc.C.isZero()) continue;
            node = fracPiece(new Poly([pc.C, pc.B]), denNode, v);
            Fp = intQuadPiece(pc.B, pc.C, pc.t.poly, pc.t.k, v);
            if (!Fp) return null;
        }
        pieceNodes.push(node);
        Fparts.push(Fp);
        subs.push(pieceStep(node, Fp, pc, v));
    }
    const F = add(Fparts.length ? Fparts : [N0]);
    // steps
    const steps = [];
    const fNode = div(P.toNode(v), D.toNode(v));
    if (!polyPart.isZero()) {
        steps.push(step({
            title: T_('Выделяем целую часть', 'Divide the polynomials'),
            tex: bt((L) => `${tx(fNode, L)} = ${tx(polyPart.toNode(v), L)}${rem.isZero() ? '' : (() => { const r = tx(fracPiece(rem, D.toNode(v), v), L); return r.startsWith('-') ? ' - ' + r.slice(1) : ' + ' + r; })()}`),
            text: T_('Степень числителя не меньше степени знаменателя, поэтому сначала делим многочлены уголком: дробь = целая часть + правильная дробь.', 'The numerator has at least the degree of the denominator, so first divide the polynomials: fraction = polynomial part + proper fraction.'),
            rule: 'division',
        }));
    }
    const factoredD = factorNode(constant, factors, v);
    const simpleDen = factors.length === 1 && factors[0].mult === 1;
    if (!rem.isZero() && !simpleDen) {
        steps.push(step({
            title: T_('Раскладываем знаменатель', 'Factor the denominator'),
            tex: bt((L) => `${tx(D.toNode(v), L)} = ${tx(factoredD, L)}`),
            text: T_('Находим корни знаменателя и раскладываем его на линейные множители и квадратные трёхчлены без действительных корней.', 'Find the roots of the denominator and split it into linear factors and quadratics without real roots.'),
            rule: 'factor',
        }));
        steps.push(step({
            title: T_('Простейшие дроби', 'Partial fractions'),
            tex: bt((L) => `${tx(fracPiece(rem, D.toNode(v), v), L)} = ${pieceNodes.map((n, i) => {
                const s = tx(n, L);
                return i === 0 ? s : (s.startsWith('-') ? ' - ' + s.slice(1) : ' + ' + s);
            }).join('')}`),
            text: T_('Раскладываем правильную дробь в сумму простейших: каждому множителю (x − a)ᵏ соответствуют дроби A/(x − a), …, A/(x − a)ᵏ, а квадратному трёхчлену — (Bx + C)/(…). Коэффициенты находим, приводя к общему знаменателю и приравнивая коэффициенты числителей (метод неопределённых коэффициентов).',
                'Split the proper fraction into partial fractions: a factor (x − a)ᵏ gives A/(x − a), …, A/(x − a)ᵏ, and a quadratic gives (Bx + C)/(…). The coefficients come from bringing everything to the common denominator and matching the numerators (undetermined coefficients).'),
            rule: 'partial-fractions',
        }));
    }
    if (steps.length === 0 && subs.length === 1) {
        // a single simple fraction: its own step says everything
        return { F, method: 'rational', step: { ...subs[0], title: T_('Рациональная дробь', 'Rational function'), rule: 'rational' } };
    }
    steps.push(step({
        title: T_('Интегрируем каждую дробь', 'Integrate each fraction'),
        tex: bt((L) => `${iTex(f, v, L)} = ${tx(simp(F), L)}`),
        rule: 'sum',
        sub: subs,
    }));
    return {
        F,
        method: 'rational',
        step: step({
            title: T_('Рациональная дробь', 'Rational function'),
            tex: bt((L) => `${iTex(f, v, L)} = ${tx(simp(F), L)}`),
            text: T_('Подынтегральная функция — отношение многочленов. Такие интегралы всегда берутся: выделяем целую часть и раскладываем остаток на простейшие дроби.', 'The integrand is a ratio of polynomials. Such integrals can always be done: take out the polynomial part and split the rest into partial fractions.'),
            rule: 'rational',
            sub: steps,
        }),
    };
}

function factorNode(constant, factors, v) {
    const fs = [];
    if (!constant.isOne()) fs.push(num(constant));
    for (const { poly, mult } of factors) fs.push(mult === 1 ? poly.toNode(v) : pow(poly.toNode(v), num(mult)));
    return fs.length === 1 ? fs[0] : mul(fs);
}

function pieceStep(node, Fp, pc, v) {
    let text;
    if (pc.t.poly.degree === 1) {
        text = pc.t.k === 1
            ? T_('∫A/(ax + b) dx = (A/a)·ln|ax + b| + C.', '∫A/(ax + b) dx = (A/a)·ln|ax + b| + C.')
            : T_('∫A/(ax + b)ᵏ dx = −A/(a(k − 1)(ax + b)ᵏ⁻¹) + C.', '∫A/(ax + b)ᵏ dx = −A/(a(k − 1)(ax + b)ᵏ⁻¹) + C.');
    } else {
        text = pc.t.k === 1
            ? T_('Выделяем в числителе производную знаменателя: (Bx + C) = (B/2a)(2ax + b) + (C − Bb/2a). Первая часть даёт логарифм, вторая после выделения полного квадрата в знаменателе — арктангенс (или логарифм, если у трёхчлена есть действительные корни).',
                'Split off the derivative of the denominator in the numerator: (Bx + C) = (B/2a)(2ax + b) + (C − Bb/2a). The first part gives a logarithm, the second, after completing the square, an arctangent (or a logarithm if the quadratic has real roots).')
            : T_('Выделяем производную знаменателя в числителе и полный квадрат в знаменателе; оставшийся интеграл ∫dt/(t² + m²)ᵏ понижаем формулой приведения.',
                'Split off the derivative of the denominator and complete the square; the remaining ∫dt/(t² + m²)ᵏ is reduced step by step.');
    }
    let middle = null;
    if (pc.t.poly.degree === 2 && pc.t.k === 1) {
        // (Bx + C)/(ax² + bx + c) = (B/2a)·(2ax + b)/(…) + (C − Bb/2a)/(a(x + b/2a)² + …)
        const [c, b, a] = [pc.t.poly.coeff(0), pc.t.poly.coeff(1), pc.t.poly.coeff(2)];
        const M = pc.B.div(a.mul(2));
        const Nn = pc.C.sub(pc.B.mul(b).div(a.mul(2)));
        const X = sym(v);
        const qNode = pc.t.poly.toNode(v);
        const lin2 = new Poly([b, a.mul(2)]).toNode(v);
        const h = b.div(a.mul(2));
        const sq = pow(h.isZero() ? X : add(X, qn(h)), N2);
        const kk = c.sub(b.mul(b).div(a.mul(4)));
        const square = kk.isZero() ? (a.isOne() ? sq : mul(qn(a), sq)) : add(a.isOne() ? sq : mul(qn(a), sq), qn(kk));
        const coef = (q0, L, first) => {
            if (q0.isOne()) return first ? '' : ' + ';
            if (q0.eq(-1)) return first ? '-' : ' - ';
            const t = qn(q0.abs()).value.toTex(L);
            return (q0.isNeg() ? (first ? '-' : ' - ') : first ? '' : ' + ') + t;
        };
        middle = (L) => {
            let out = '';
            if (!M.isZero()) out += `${coef(M, L, true)}\\int \\frac{${tx(lin2, L)}}{${tx(qNode, L)}}\\,d${v}`;
            if (!Nn.isZero()) out += `${coef(Nn, L, !out)}\\int \\frac{d${v}}{${tx(square, L)}}`;
            return out;
        };
    }
    return step({
        title: T_('Простейшая дробь', 'Partial fraction'),
        tex: bt((L) => `${iTex(node, v, L)} = ${middle ? middle(L) + ' = ' : ''}${tx(trySimp(Fp) ?? Fp, L)}`),
        text,
        rule: 'partial-fraction',
    });
}

// ---- trigonometric forms

const TRIG_REWRITE = { tan: (u) => div(fn('sin', u), fn('cos', u)), cot: (u) => div(fn('cos', u), fn('sin', u)), sec: (u) => div(N1, fn('cos', u)), csc: (u) => div(N1, fn('sin', u)) };

function toSinCos(f) {
    let changed = false;
    const g = mapNode(f, (m) => {
        if (m.type === 'fn' && TRIG_REWRITE[m.name]) {
            changed = true;
            return TRIG_REWRITE[m.name](m.args[0]);
        }
        return undefined;
    });
    return changed ? trySimp(g) : f;
}

/** c·sin^m(L)·cos^n(L) with integers m, n and L linear → {c, L, m, n}, else null. */
function sinCosShape(f, v) {
    const { coef, rest } = splitCoeff(f);
    if (rest === null) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    let L = null;
    let m = 0;
    let n = 0;
    const consts = [];
    for (const x of fs) {
        if (!containsVar(x, v)) {
            consts.push(x);
            continue;
        }
        const b = x.type === 'pow' ? x.base : x;
        const e = x.type === 'pow' ? x.exp : N1;
        if (b.type !== 'fn' || (b.name !== 'sin' && b.name !== 'cos') || !isNum(e) || !e.value.isInt()) return null;
        const arg = b.args[0];
        if (L && nodeKey(L) !== nodeKey(arg)) return null;
        L = arg;
        if (b.name === 'sin') m += Number(e.value.n);
        else n += Number(e.value.n);
    }
    if (!L) return null;
    const lp = linearParts(L, v);
    if (!lp) return null;
    return { c: consts.length ? mul([num(coef), ...consts]) : num(coef), L, m, n, k: lp.k };
}

/** A rational function of v in lowest terms as a node (a polynomial when the denominator is a number), else null. */
function canonicalRational(node, v) {
    const r = ratFunctionOf(node, v);
    if (!r) return null;
    if (r.den.degree < 1) return trySimp(r.num.scale(r.den.coeff(0).inv()).toNode(v));
    return trySimp(div(r.num.toNode(v), r.den.toNode(v)));
}

function substResult(f, ctx, { t, uNode, g, title, text, rule, dtTex }) {
    const { v } = ctx;
    const g0 = trySimp(g);
    if (!g0) return null;
    // after t = tg(x/2) and the like the fraction comes out nested: −2/(((t²−1)/(t²+1) − 1)(t²+1)) is just 1
    const gs = canonicalRational(g0, t) ?? g0;
    const r = I(gs, sub(ctx, { v: t }));
    if (!r) return null;
    const F = substitute(r.F, { [t]: uNode });
    return {
        F,
        method: rule,
        step: step({
            title,
            tex: bt((L) => `${iTex(f, v, L)} = \\left[${t} = ${tx(uNode, L)},\\ ${dtTex(L)}\\right] = ${iTex(gs, t, L)} = ${tx(trySimp(r.F) ?? r.F, L)} = ${tx(trySimp(F) ?? F, L)}`),
            text,
            rule,
            sub: [r.step],
        }),
    };
}

function mTrig(f, ctx) {
    const { v } = ctx;
    const g = toSinCos(f);
    if (!g) return null;
    const sh = sinCosShape(g, v);
    if (sh && (sh.m !== 0 || sh.n !== 0)) {
        const { c, L, m, n, k } = sh;
        const t = freshVar(f, v);
        const T = sym(t);
        const oneMinus = add(N1, neg(pow(T, N2)));
        const kInv = div(N1, k);
        const mOdd = m % 2 !== 0;
        const nOdd = n % 2 !== 0;
        const cosOK = mOdd && m >= 1;
        const sinOK = nOdd && n >= 1;
        const useSin = sinOK && cosOK ? n <= m : sinOK ? true : cosOK ? false : nOdd;
        if (m % 2 !== 0 && !useSin) {
            // t = cos L, dt = −k sin L dx
            const gt = mul(neg(c), kInv, pow(oneMinus, num((m - 1) / 2)), pow(T, num(n)));
            return substResult(f, ctx, {
                t, uNode: fn('cos', L), g: expandSafe(gt), rule: 'trig-substitution',
                title: T_(`Замена ${t} = ${plainish(fn('cos', L), 'ru')}`, `Substitution ${t} = ${plainish(fn('cos', L), 'en')}`),
                dtTex: (Lg) => `d${t} = -${coefTex(k, Lg)}\\sin ${Lg === 'ru' ? '' : ''}${paren(tx(L, Lg)).replace(/^\((.*)\)$/, L.type === 'sym' ? '$1' : '($1)')}\\,d${v}`,
                text: T_('Синус стоит в нечётной степени: один синус отделяем к dx, остальные чётные степени выражаем через косинус (sin² = 1 − cos²) и заменяем t = cos, dt = −sin·dx.',
                    'The sine has an odd power: keep one sine with dx, write the remaining even powers through the cosine (sin² = 1 − cos²) and substitute t = cos, dt = −sin·dx.'),
            });
        }
        if (useSin) {
            const gt = mul(c, kInv, pow(T, num(m)), pow(oneMinus, num((n - 1) / 2)));
            return substResult(f, ctx, {
                t, uNode: fn('sin', L), g: expandSafe(gt), rule: 'trig-substitution',
                title: T_(`Замена ${t} = ${plainish(fn('sin', L), 'ru')}`, `Substitution ${t} = ${plainish(fn('sin', L), 'en')}`),
                dtTex: (Lg) => `d${t} = ${coefTex(k, Lg)}\\cos${L.type === 'sym' ? ' ' + tx(L, Lg) : paren(tx(L, Lg))}\\,d${v}`,
                text: T_('Косинус стоит в нечётной степени: один косинус отделяем к dx, остальные чётные степени выражаем через синус (cos² = 1 − sin²) и заменяем t = sin, dt = cos·dx.',
                    'The cosine has an odd power: keep one cosine with dx, write the remaining even powers through the sine (cos² = 1 − sin²) and substitute t = sin, dt = cos·dx.'),
            });
        }
        if (m + n <= 0) {
            // t = tg L: sin^m cos^n = t^m (1 + t²)^{−(m+n)/2}, dx = dt/(k(1 + t²))
            const gt = mul(c, kInv, pow(T, num(m)), pow(add(N1, pow(T, N2)), num(-(m + n) / 2 - 1)));
            return substResult(f, ctx, {
                t, uNode: fn('tan', L), g: gt, rule: 'trig-substitution',
                title: T_(`Замена ${t} = ${plainish(fn('tan', L), 'ru')}`, `Substitution ${t} = ${plainish(fn('tan', L), 'en')}`),
                dtTex: (Lg) => `d${t} = \\frac{${coefTex(k, Lg) ? coefTex(k, Lg) + '\\,' : ''}d${v}}{\\cos^{2}${L.type === 'sym' ? ' ' + tx(L, Lg) : paren(tx(L, Lg))}}`,
                text: T_('Степени синуса и косинуса чётные, а их сумма не положительна: делим на cos² и заменяем t = tg, dt = dx/cos², 1/cos² = 1 + t².',
                    'The powers of sine and cosine are even and add up to a non-positive number: divide by cos² and substitute t = tan, dt = dx/cos², 1/cos² = 1 + t².'),
            });
        }
        // both even, m + n > 0
        const S2 = pow(fn('sin', L), N2);
        const C2 = pow(fn('cos', L), N2);
        let rewritten;
        let text;
        if (m >= 0 && n >= 0) {
            const L2 = mul(N2, L);
            const s2 = div(add(N1, neg(fn('cos', L2))), N2);
            const c2 = div(add(N1, fn('cos', L2)), N2);
            rewritten = mul(c, pow(s2, num(m / 2)), pow(c2, num(n / 2)));
            text = T_('Степени чётные: понижаем их формулами двойного угла sin²u = (1 − cos 2u)/2, cos²u = (1 + cos 2u)/2 и раскрываем скобки.', 'Even powers: lower them with the double-angle formulas sin²u = (1 − cos 2u)/2, cos²u = (1 + cos 2u)/2 and expand.');
        } else if (n < 0) {
            rewritten = mul(c, pow(add(N1, neg(C2)), num(m / 2)), pow(fn('cos', L), num(n)));
            text = T_('Выражаем синус через косинус: sin² = 1 − cos², и раскрываем скобки.', 'Write the sine through the cosine, sin² = 1 − cos², and expand.');
        } else {
            rewritten = mul(c, pow(fn('sin', L), num(m)), pow(add(N1, neg(S2)), num(n / 2)));
            text = T_('Выражаем косинус через синус: cos² = 1 − sin², и раскрываем скобки.', 'Write the cosine through the sine, cos² = 1 − sin², and expand.');
        }
        const X = expandSafe(rewritten);
        if (!X || nodeKey(X) === nodeKey(f)) return null;
        const r = I(X, ctx);
        if (!r) return null;
        return {
            F: r.F,
            method: 'trig-power',
            step: step({ title: T_('Понижаем степень', 'Lower the powers'), tex: bt((Lg) => `${iTex(f, v, Lg)} = ${iTex(X, v, Lg)}`), text, rule: 'trig-power', sub: [r.step] }),
        };
    }
    // product to sum: sin a·cos b, sin a·sin b, cos a·cos b with different linear arguments
    const ps = productToSum(g, v);
    if (ps) {
        const r = I(ps.X, ctx);
        if (!r) return null;
        return {
            F: r.F,
            method: 'trig-product',
            step: step({
                title: T_('Произведение в сумму', 'Product to sum'),
                tex: bt((Lg) => `${iTex(f, v, Lg)} = ${iTex(ps.X, v, Lg)}`),
                text: T_('Произведение синусов и косинусов разных аргументов превращаем в сумму: sin a·cos b = (sin(a + b) + sin(a − b))/2, sin a·sin b = (cos(a − b) − cos(a + b))/2, cos a·cos b = (cos(a − b) + cos(a + b))/2.',
                    'Turn the product of sines and cosines of different arguments into a sum: sin a·cos b = (sin(a + b) + sin(a − b))/2, sin a·sin b = (cos(a − b) − cos(a + b))/2, cos a·cos b = (cos(a − b) + cos(a + b))/2.'),
                rule: 'trig-product',
                sub: [r.step],
            }),
        };
    }
    return null;
}

/** Other factors next to sin²u, cos³u …: lower the trig powers (double angle, triple angle) and expand. */
function mTrigLower(f, ctx) {
    const { v } = ctx;
    if (f.type !== 'mul') return null;
    let changed = false;
    const out = f.args.map((x) => {
        if (x.type !== 'pow' || !isNum(x.exp) || !x.exp.value.isInt() || x.base.type !== 'fn' || !['sin', 'cos'].includes(x.base.name)) return x;
        const k = Number(x.exp.value.n);
        const u = x.base.args[0];
        if (!linearParts(u, v)) return x;
        const u2 = mul(N2, u);
        const u3 = mul(num(3), u);
        let r = null;
        if (k === 2) r = x.base.name === 'sin' ? div(add(N1, neg(fn('cos', u2))), N2) : div(add(N1, fn('cos', u2)), N2);
        else if (k === 3) r = x.base.name === 'sin' ? div(add(mul(num(3), fn('sin', u)), neg(fn('sin', u3))), num(4)) : div(add(mul(num(3), fn('cos', u)), fn('cos', u3)), num(4));
        else if (k === 4) {
            const c2 = x.base.name === 'sin' ? neg(fn('cos', u2)) : fn('cos', u2);
            r = div(add(num(3), mul(num(4), c2), fn('cos', mul(num(4), u))), num(8));
        }
        if (!r) return x;
        changed = true;
        return r;
    });
    if (!changed) return null;
    if (!f.args.some((x) => containsVar(x, v) && !(x.type === 'pow' && x.base.type === 'fn' && ['sin', 'cos'].includes(x.base.name)))) return null;
    const X = expandSafe(mul(out));
    if (!X || X.type !== 'add') return null;
    const r = I(X, ctx);
    if (!r) return null;
    return {
        F: r.F,
        method: r.method,
        step: step({
            title: T_('Понижаем степень', 'Lower the powers'),
            tex: bt((L) => `${iTex(f, v, L)} = ${iTex(X, v, L)}`),
            text: T_('Степень синуса или косинуса понижаем формулами sin²u = (1 − cos 2u)/2, cos²u = (1 + cos 2u)/2 (и sin³u = (3 sin u − sin 3u)/4) и раскрываем скобки: получается сумма знакомых интегралов.',
                'Lower the power of the sine or cosine with sin²u = (1 − cos 2u)/2, cos²u = (1 + cos 2u)/2 (and sin³u = (3 sin u − sin 3u)/4) and expand: a sum of familiar integrals remains.'),
            rule: 'trig-power',
            sub: [r.step],
        }),
    };
}

function expandSafe(n) {
    try {
        return simp(expand(n));
    } catch {
        return trySimp(n);
    }
}

function productToSum(f, v) {
    const { coef, rest } = splitCoeff(f);
    if (!rest || rest.type !== 'mul') return null;
    const trig = [];
    const others = [];
    for (const x of rest.args) {
        if (x.type === 'fn' && (x.name === 'sin' || x.name === 'cos') && linearParts(x.args[0], v)) trig.push(x);
        else if (!containsVar(x, v)) others.push(x);
        else return null;
    }
    if (trig.length !== 2 || nodeKey(trig[0].args[0]) === nodeKey(trig[1].args[0])) return null;
    let [p1, p2] = trig;
    if (p1.name === 'cos' && p2.name === 'sin') [p1, p2] = [p2, p1];
    const a = p1.args[0];
    const b = p2.args[0];
    const sum = add(a, b);
    const dif = add(a, neg(b));
    let X;
    if (p1.name === 'sin' && p2.name === 'cos') X = div(add(fn('sin', sum), fn('sin', dif)), N2);
    else if (p1.name === 'sin') X = div(add(fn('cos', dif), neg(fn('cos', sum))), N2);
    else X = div(add(fn('cos', dif), fn('cos', sum)), N2);
    const all = expandSafe(mul([num(coef), ...others, X]));
    return all ? { X: all } : null;
}

// ---- u-substitution g(h(x))·h′(x)

function subCandidates(f, v) {
    const out = new Map();
    const visit = (n) => {
        if (!containsVar(n, v)) return;
        if (n !== f && !isVar(n, v)) out.set(nodeKey(n), n);
        if (n.type === 'pow' && containsVar(n.base, v) && !isVar(n.base, v)) out.set(nodeKey(n.base), n.base);
        // x/(x⁴ + 1): the helpful t = x² is not written anywhere, only its square x⁴
        if (n.type === 'pow' && isVar(n.base, v) && isNum(n.exp) && n.exp.value.isInt()) {
            const k = Number(n.exp.value.n);
            for (let d = 2; d <= k / 2 && k <= 24; d++) {
                if (k % d) continue;
                const u = pow(sym(v), num(d));
                out.set(nodeKey(u), u);
            }
        }
        for (const c of nodeChildren(n)) visit(c);
    };
    visit(f);
    return [...out.values()].filter((u) => !linearParts(u, v));
}

function replaceU(r, u, t, v) {
    const key = nodeKey(u);
    const T = sym(t);
    const expBase = u.type === 'pow' && !containsVar(u.base, v) ? u.base : null;
    const powW = u.type === 'pow' && isNum(u.exp) ? u.base : null;
    const powP = powW ? u.exp.value : null;
    const rootLike = powP && !powP.isInt();
    let g = mapPre(r, (m) => {
        if (nodeKey(m) === key) return T;
        if (expBase && m.type === 'pow' && nodeKey(m.base) === nodeKey(expBase) && containsVar(m.exp, v)) {
            const ratio = trySimp(div(m.exp, u.exp));
            if (ratio && isNum(ratio)) return pow(T, ratio);
        }
        if (powW && m.type === 'pow' && nodeKey(m.base) === nodeKey(powW) && isNum(m.exp)) {
            const e = m.exp.value.div(powP);
            if (rootLike || e.isInt()) return pow(T, num(e));
        }
        if (powW && rootLike && nodeKey(m) === nodeKey(powW)) return pow(T, num(powP.inv()));
        return undefined;
    });
    g = trySimp(g);
    if (!g) return null;
    if (containsVar(g, v) && u.type === 'fn' && u.name === 'ln' && isVar(u.args[0], v)
        && nodeSome(r, (m) => m.type === 'fn' && m.name !== 'ln' && nodeSome(m.args[0], (k) => nodeKey(k) === key))) {
        // cos(ln x): with t = ln x the leftover x is eᵗ (x·ln x is left to parts)
        g = trySimp(substitute(g, { [v]: pow(E_, T) }));
        return g && !containsVar(g, v) ? g : null;
    }
    if (containsVar(g, v)) {
        // u = a·v^k + b: v^m → ((t − b)/a)^(m/k) when k | m
        const P = Poly.fromNode(u, v);
        if (!P || P.degree < 2) return null;
        const nz = P.c.map((c, i) => (c.isZero() ? -1 : i)).filter((i) => i >= 0);
        if (nz.length > 2 || (nz.length === 2 && nz[0] !== 0)) return null;
        const kdeg = P.degree;
        const a = P.lead;
        const b = P.coeff(0);
        const back = div(add(T, qn(b.neg())), qn(a));
        g = mapNode(g, (m) => {
            if (m.type === 'pow' && isVar(m.base, v) && isNum(m.exp) && m.exp.value.isInt() && m.exp.value.n % BigInt(kdeg) === 0n) return pow(back, num(m.exp.value.div(kdeg)));
            return undefined;
        });
        g = trySimp(g);
        if (!g || containsVar(g, v)) return null;
    }
    return g;
}

function mUSub(f, ctx) {
    const { v } = ctx;
    if (f.type === 'add') return null;
    const t = freshVar(f, v);
    const cands = [];
    for (const u of subCandidates(f, v)) {
        let du;
        try {
            du = simp(quickDerivative(u, v));
        } catch {
            continue;
        }
        if (isZero(du)) continue;
        const r = trySimp(mul(f, pow(du, NM1)));
        if (!r) continue;
        const g = replaceU(r, u, t, v);
        if (!g || containsVar(g, v)) continue;
        if (nodeKey(substitute(g, { [t]: sym(v) })) === nodeKey(f)) continue;
        cands.push({ u, du, g, size: nodeSize(g) });
    }
    // prefer a substitution that leaves an integral in t (t = x² for x·e^(x²)), then the simplest one
    const isConstG = (c) => !containsVar(c.g, t);
    cands.sort((a, b) => isConstG(a) - isConstG(b) || a.size - b.size || nodeSize(b.u) - nodeSize(a.u));
    for (const c of cands.slice(0, 5)) {
        const res = substResult(f, ctx, {
            t, uNode: c.u, g: c.g, rule: 'substitution',
            title: T_('Замена переменной', 'Substitution'),
            dtTex: (L) => `d${t} = ${isOne(c.du) ? '' : c.du.type === 'add' ? paren(tx(c.du, L)) : tx(c.du, L) + '\\,'}d${v}`,
            text: T_(`Замечаем, что производная выражения ${plainish(c.u, 'ru')} (с точностью до постоянного множителя) уже стоит множителем под интегралом. Делаем замену ${t} = ${plainish(c.u, 'ru')}: интеграл превращается в более простой.`,
                `The derivative of ${plainish(c.u, 'en')} is (up to a constant factor) already a factor of the integrand. Substitute ${t} = ${plainish(c.u, 'en')}: the integral becomes simpler.`),
        });
        if (res) return res;
    }
    return null;
}

// ---- square roots of quadratics

function quadRootShape(f, v) {
    const { coef, rest } = splitCoeff(f);
    if (!rest) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    let rad = null;
    const others = [];
    for (const x of fs) {
        if (x.type === 'pow' && isNum(x.exp) && (x.exp.value.eq(Q.HALF) || x.exp.value.eq(q(-1, 2))) && containsVar(x.base, v)) {
            if (rad) return null;
            rad = x;
        } else others.push(x);
    }
    if (!rad) return null;
    const Qp = Poly.fromNode(rad.base, v);
    if (!Qp || Qp.degree !== 2) return null;
    const lin = others.length ? Poly.fromNode(mul(others), v) : new Poly([Q.ONE]);
    if (!lin || lin.degree > 1) return null;
    return { coef, Qp, e: rad.exp.value, B: lin.coeff(1).mul(coef), C: lin.coeff(0).mul(coef), radBase: rad.base };
}

function mQuadRoot(f, ctx) {
    const { v } = ctx;
    const sh = quadRootShape(f, v);
    if (!sh) return null;
    const { Qp, e, B, C, radBase } = sh;
    const X = sym(v);
    const [c, b, a] = [Qp.coeff(0), Qp.coeff(1), Qp.coeff(2)];
    const D = b.mul(b).sub(a.mul(c).mul(4));
    const sqrtQ = pow(radBase, HALF);
    const lin2 = add(mul(qn(a.mul(2)), X), qn(b));
    const M = B.div(a.mul(2));
    const Nn = C.sub(B.mul(b).div(a.mul(2)));
    const parts = [];
    let text;
    const tShift = add(X, qn(b.div(a.mul(2))));
    if (e.isNeg()) {
        // ∫(Bx + C)/√Q = (B/a)√Q + N∫dx/√Q
        if (!M.isZero()) parts.push(mul(qn(B.div(a)), sqrtQ));
        if (!Nn.isZero()) {
            if (a.isPos()) parts.push(mul(qn(Nn), div(N1, pow(qn(a), HALF)), lnAbs(add(X, qn(b.div(a.mul(2))), div(sqrtQ, pow(qn(a), HALF))), v)));
            else {
                if (!D.isPos()) return null;
                parts.push(mul(qn(Nn), div(N1, pow(qn(a.neg()), HALF)), fn('asin', div(add(mul(qn(a.mul(-2)), X), qn(b.neg())), pow(qn(D), HALF)))));
            }
        }
        text = a.isPos()
            ? T_('Под корнем квадратный трёхчлен с положительным старшим коэффициентом. Выделяем полный квадрат и пользуемся «длинным логарифмом»: ∫dt/√(t² + k) = ln|t + √(t² + k)| + C. Если в числителе есть x, сначала отделяем производную подкоренного выражения.',
                'A quadratic with a positive leading coefficient under the root. Complete the square and use ∫dt/√(t² + k) = ln|t + √(t² + k)| + C. If x is in the numerator, first split off the derivative of the radicand.')
            : T_('Под корнем квадратный трёхчлен с отрицательным старшим коэффициентом. Выделяем полный квадрат: получается ∫dt/√(m² − t²) = arcsin(t/m) + C. Если в числителе есть x, сначала отделяем производную подкоренного выражения.',
                'A quadratic with a negative leading coefficient under the root. Completing the square gives ∫dt/√(m² − t²) = arcsin(t/m) + C. If x is in the numerator, first split off the derivative of the radicand.');
    } else {
        // ∫(Bx + C)√Q = (B/(3a)) Q^{3/2} + N∫√Q
        if (!M.isZero()) parts.push(mul(qn(B.div(a.mul(3))), pow(radBase, num(q(3, 2)))));
        if (!Nn.isZero()) {
            // ∫√Q dx with Q = a(t² + K), t = x + b/2a, K = (4ac − b²)/(4a²):
            //   a > 0: (t/2)√Q + (√a·K/2)·ln|t + √Q/√a|;   a < 0 (Q = |a|(m² − t²)): (t/2)√Q + (√|a|·m²/2)·arcsin(t/m)
            const K = D.neg().div(a.mul(a).mul(4));
            const sa = pow(qn(a.abs()), HALF);
            const half = mul(div(tShift, N2), sqrtQ);
            if (a.isPos()) {
                parts.push(mul(qn(Nn), add(half, mul(qn(K.div(2)), sa, lnAbs(add(tShift, div(sqrtQ, sa)), v)))));
            } else {
                const m2 = K.neg();
                if (!m2.isPos()) return null;
                parts.push(mul(qn(Nn), add(half, mul(qn(m2.div(2)), sa, fn('asin', div(tShift, pow(qn(m2), HALF)))))));
            }
        }
        text = T_('Корень из квадратного трёхчлена: выделяем полный квадрат и пользуемся формулами ∫√(m² − t²)dt = (t/2)√(m² − t²) + (m²/2)arcsin(t/m) + C и ∫√(t² + k)dt = (t/2)√(t² + k) + (k/2)ln|t + √(t² + k)| + C.',
            'The root of a quadratic: complete the square and use ∫√(m² − t²)dt = (t/2)√(m² − t²) + (m²/2)arcsin(t/m) + C and ∫√(t² + k)dt = (t/2)√(t² + k) + (k/2)ln|t + √(t² + k)| + C.');
    }
    if (!parts.length) return null;
    const F = add(parts);
    const complete = completeSquareTex(a, b, c, v);
    return {
        F,
        method: 'quadratic-root',
        step: step({
            title: T_('Квадратный трёхчлен под корнем', 'A quadratic under the root'),
            tex: bt((L) => `${complete ? complete(L) + ',\\quad ' : ''}${iTex(f, v, L)} = ${tx(trySimp(F) ?? F, L)}`),
            text,
            rule: 'quadratic-root',
        }),
    };
}

function completeSquareTex(a, b, c, v) {
    if (b.isZero()) return null;
    const X = sym(v);
    const h = b.div(a.mul(2));
    const k = c.sub(b.mul(b).div(a.mul(4)));
    const sq = pow(add(X, qn(h)), N2);
    const node = add(a.isOne() ? sq : mul(qn(a), sq), qn(k));
    const orig = new Poly([c, b, a]).toNode(v);
    return (L) => `${tx(orig, L)} = ${toTex2(node, L)}`;
}

function toTex2(n, L) {
    // keep (x + h)² unsimplified
    return calcTex(n, L);
}

// ---- ∫Pₙ(x)/√Q dx = Rₙ₋₁(x)·√Q + λ∫dx/√Q (undetermined coefficients)

/** ∫dx/√Q for a quadratic Q = ax² + bx + c (the «long logarithm» or arcsin), or null. */
function invSqrtQuad(Qp, v, radBase) {
    const X = sym(v);
    const [c, b, a] = [Qp.coeff(0), Qp.coeff(1), Qp.coeff(2)];
    const sqrtQ = pow(radBase, HALF);
    if (a.isPos()) return mul(div(N1, pow(qn(a), HALF)), lnAbs(add(X, qn(b.div(a.mul(2))), div(sqrtQ, pow(qn(a), HALF))), v));
    const D = b.mul(b).sub(a.mul(c).mul(4));
    if (!D.isPos()) return null;
    return mul(div(N1, pow(qn(a.neg()), HALF)), fn('asin', div(add(mul(qn(a.mul(-2)), X), qn(b.neg())), pow(qn(D), HALF))));
}

function mRadicalPoly(f, ctx) {
    const { v } = ctx;
    const { coef, rest } = splitCoeff(f);
    if (!rest) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    let rad = null;
    const others = [];
    for (const x of fs) {
        if (x.type === 'pow' && isNum(x.exp) && (x.exp.value.eq(Q.HALF) || x.exp.value.eq(q(-1, 2))) && containsVar(x.base, v)) {
            if (rad) return null;
            rad = x;
        } else others.push(x);
    }
    if (!rad) return null;
    const Qp = Poly.fromNode(rad.base, v);
    if (!Qp || Qp.degree !== 2) return null;
    let P = Poly.fromNode(mul([num(coef), ...others]), v);
    if (!P) return null;
    if (rad.exp.value.isPos()) P = P.mul(Qp);
    const n = P.degree;
    if (n < 2 || n > 12) return null;
    // P = R′·Q + R·Q′/2 + λ, R of degree n − 1
    const dQ = Qp.derivative();
    const cols = [];
    for (let j = 0; j < n; j++) {
        const xj = Poly.monomial(Q.ONE, j);
        cols.push(xj.derivative().mul(Qp).add(xj.mul(dQ).scale(Q.HALF)));
    }
    cols.push(new Poly([Q.ONE]));
    const Am = [];
    const bv = [];
    for (let i = 0; i <= n; i++) {
        Am.push(cols.map((c) => c.coeff(i)));
        bv.push(P.coeff(i));
    }
    const sol = solveQ(Am, bv);
    if (!sol) return null;
    const R = new Poly(sol.slice(0, n));
    const lam = sol[n];
    const J = lam.isZero() ? null : invSqrtQuad(Qp, v, rad.base);
    if (!lam.isZero() && !J) return null;
    const sqrtQ = pow(rad.base, HALF);
    const F = add([mul(R.toNode(v), sqrtQ), ...(J ? [mul(qn(lam), J)] : [])]);
    return {
        F,
        method: 'radical-polynomial',
        step: step({
            title: T_('Метод неопределённых коэффициентов', 'Undetermined coefficients'),
            tex: bt((L) => `${iTex(f, v, L)} = \\left(${tx(R.toNode(v), L)}\\right)\\sqrt{${tx(rad.base, L)}}${lam.isZero() ? '' : ` ${lam.isNeg() ? '-' : '+'} ${lam.abs().isOne() ? '' : qn(lam.abs()).value.toTex(L)}\\int \\frac{d${v}}{\\sqrt{${tx(rad.base, L)}}}`} = ${tx(trySimp(F) ?? F, L)}`),
            text: T_(`Многочлен, делённый на корень из квадратного трёхчлена: ∫Pₙ(x)/√Q dx = Rₙ₋₁(x)·√Q + λ∫dx/√Q. Коэффициенты многочлена R степени ${n - 1} и число λ находим, продифференцировав обе части и приравняв коэффициенты при одинаковых степенях x.`,
                `A polynomial over the root of a quadratic: ∫Pₙ(x)/√Q dx = Rₙ₋₁(x)·√Q + λ∫dx/√Q. The coefficients of R (degree ${n - 1}) and λ come from differentiating both sides and matching the coefficients of equal powers of x.`),
            rule: 'radical-polynomial',
        }),
    };
}

// ---- rationalising substitution t = ⁿ√(ax + b)

function mRationalizing(f, ctx) {
    const { v } = ctx;
    let base = null;
    let den = 1n;
    let ok = true;
    const visit = (n) => {
        if (n.type === 'pow' && isNum(n.exp) && !n.exp.value.isInt() && containsVar(n.base, v)) {
            if (base && nodeKey(base) !== nodeKey(n.base)) ok = false;
            base = n.base;
            den = bigLcm(den, n.exp.value.d);
        }
        for (const c of nodeChildren(n)) visit(c);
    };
    visit(f);
    if (!ok || !base || den < 2n || den > 12n) return null;
    const lp = linearParts(base, v);
    if (!lp || !isNum(lp.k) || !isNum(lp.b)) return null;
    const m = Number(den);
    const t = freshVar(f, v);
    const T = sym(t);
    const xOfT = div(add(pow(T, num(m)), neg(lp.b)), lp.k);
    let g = trySimp(mul(substitute(f, { [v]: xOfT }), div(mul(num(m), pow(T, num(m - 1))), lp.k)));
    if (!g) return null;
    g = trySimp(mapNode(g, (x) => (x.type === 'fn' && x.name === 'abs' && isVar(x.args[0], t) ? T : undefined)));
    if (!g || !ratFunctionOf(g, t)) return null;
    const uNode = pow(base, num(q(1, m)));
    return substResult(f, ctx, {
        t, uNode, g, rule: 'rationalizing',
        title: T_('Замена, убирающая корень', 'A substitution that removes the root'),
        dtTex: (L) => `${v} = ${tx(trySimp(xOfT) ?? xOfT, L)},\\ d${v} = ${tx(simp(div(mul(num(m), pow(T, num(m - 1))), lp.k)), L)}\\,d${t}`,
        text: T_(`Все корни — из одного и того же линейного выражения ${plainish(base, 'ru')}. Заменяем t = ${m === 2 ? '√' : `${m}-й корень из `}(${plainish(base, 'ru')}): корни исчезают, остаётся рациональная дробь от t.`,
            `All roots are of the same linear expression ${plainish(base, 'en')}. Substitute t = ${m === 2 ? '√' : `the ${m}-th root of `}(${plainish(base, 'en')}): the roots disappear and a rational function of t is left.`),
    });
}

// ---- integration by parts

function partsKind(x, v) {
    const b = x.type === 'pow' && isNum(x.exp) && x.exp.value.isInt() && x.exp.value.isPos() ? x.base : x;
    if (b.type === 'fn' && (b.name === 'ln' || b.name === 'lg' || b.name === 'log')) return 'L';
    if (b.type === 'fn' && ['asin', 'acos', 'atan', 'acot', 'asinh', 'acosh', 'atanh'].includes(b.name)) return 'I';
    if (isVar(b, v)) return 'A';
    if (x.type === 'pow' && isVar(x.base, v) && isNum(x.exp)) return 'A';
    if (b.type === 'add' && Poly.fromNode(b, v)) return 'A';
    if (b.type === 'fn' && ['sin', 'cos', 'sinh', 'cosh'].includes(b.name)) return 'T';
    if (x.type === 'pow' && !containsVar(x.base, v)) return 'E';
    return '?';
}

function trigPowerPartner(x, v) {
    if (!(x.type === 'pow' && isNum(x.exp) && x.exp.value.isInt() && x.base.type === 'fn' && linearParts(x.base.args[0], v))) return false;
    if (['sin', 'cos'].includes(x.base.name)) return true;
    // x·tg²x: ∫tg²x dx = tg x − x, and its integral is elementary again; an odd power would leave ∫ln|cos x|
    return ['tan', 'cot'].includes(x.base.name) && x.exp.value.isPos() && x.exp.value.n % 2n === 0n;
}

const LIATE_WHY = {
    L: T_('логарифм при дифференцировании превращается в дробь', 'a logarithm turns into a fraction when differentiated'),
    I: T_('обратная тригонометрическая функция при дифференцировании становится алгебраической', 'an inverse trigonometric function becomes algebraic when differentiated'),
    A: T_('многочлен при дифференцировании понижает степень', 'a polynomial loses a degree when differentiated'),
};

function mParts(f, ctx) {
    const { v } = ctx;
    if ((ctx.parts ?? 0) >= 6) return null;
    const { coef, rest } = splitCoeff(f);
    if (!rest) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    const kinds = fs.map((x) => (containsVar(x, v) ? partsKind(x, v) : 'c'));
    let pick = -1;
    for (const want of ['L', 'I', 'A']) {
        const idx = kinds.indexOf(want);
        if (idx < 0) continue;
        if (want === 'A' && kinds.filter((k) => k !== 'c' && k !== 'A').length === 0) break; // a bare polynomial needs no parts
        if (want === 'A') {
            // a polynomial is u only next to eˣ, sin, cos, sh, ch or 1/cos², 1/sin² (not next to roots etc.)
            const partnerOk = fs.every((x, i) => kinds[i] === 'c' || kinds[i] === 'A' || kinds[i] === 'E' || kinds[i] === 'T' || trigPowerPartner(x, v));
            if (!partnerOk) break;
        }
        pick = idx;
        break;
    }
    if (pick < 0) return null;
    const u = fs[pick];
    if (kinds[pick] === 'A' && !Poly.fromNode(u, v)) {
        const P = Poly.fromNode(u.type === 'pow' ? u.base : u, v);
        if (!P) return null;
    }
    if (kinds[pick] === 'A' && !(Poly.fromNode(u, v)?.degree >= 1)) return null;
    const dvNode = simp(mul([num(coef), ...fs.filter((_, i) => i !== pick)]));
    const c2 = sub(ctx, { parts: (ctx.parts ?? 0) + 1 });
    const rv = I(dvNode, c2);
    if (!rv) return null;
    // v enters the second integral, so tidy it first: arctg(tg x) → x keeps ∫v du elementary-looking
    let V = rv.F;
    try {
        const Vc = cleanAnti(V, v);
        if (checkAnti(Vc, dvNode, v) !== false) V = Vc;
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
    }
    let du;
    try {
        du = simp(quickDerivative(u, v));
    } catch {
        return null;
    }
    const inner = trySimp(mul(V, du));
    if (!inner) return null;
    const rj = isZero(inner) ? { F: N0, step: null } : I(inner, c2);
    if (!rj) return null;
    const F = add(mul(u, V), neg(rj.F));
    const why = LIATE_WHY[kinds[pick]];
    const dvT = (L) => (isOne(dvNode) ? `d${v}` : `${tx(dvNode, L)}\\,d${v}`);
    const Vs = trySimp(V) ?? V;
    return {
        F,
        method: 'parts',
        step: step({
            title: T_('Интегрирование по частям', 'Integration by parts'),
            tex: bt((L) => `\\left[u = ${tx(u, L)},\\ dv = ${dvT(L)};\\ du = ${isOne(du) ? '' : tx(du, L) + '\\,'}d${v},\\ v = ${tx(Vs, L)}\\right],\\quad ${iTex(f, v, L)} = ${tx(simp(mul(u, Vs)), L)} - ${iTex(inner, v, L)} = ${tx(trySimp(F) ?? F, L)}`),
            text: T_(`Формула ∫u dv = uv − ∫v du. За u берём ${plainish(u, 'ru')}: ${why ? why.ru : 'так интеграл упрощается'}. Остальное — dv, его первообразная v = ${plainish(Vs, 'ru')}.`,
                `The formula ∫u dv = uv − ∫v du. Take u = ${plainish(u, 'en')}: ${why ? why.en : 'this makes the integral simpler'}. The rest is dv, with antiderivative v = ${plainish(Vs, 'en')}.`),
            rule: 'parts',
            sub: [rv.step, rj.step].filter(Boolean),
        }),
    };
}

// ---- P(x)·e^{kx+b}, P(x)·sin/cos(kx+b) of any degree: integration by parts n times (the tabular way)

function mPolyTimes(f, ctx) {
    const { v } = ctx;
    const { coef, rest } = splitCoeff(f);
    if (!rest || rest.type !== 'mul') return null;
    const polys = [];
    let other = null;
    for (const x of rest.args) {
        if (!containsVar(x, v)) polys.push(x);
        else if (!other && ((x.type === 'pow' && !containsVar(x.base, v) && linearParts(x.exp, v)) || (x.type === 'fn' && (x.name === 'sin' || x.name === 'cos') && linearParts(x.args[0], v)))) other = x;
        else polys.push(x);
    }
    if (!other) return null;
    const P = Poly.fromNode(mul([num(coef), ...polys]), v);
    if (!P || P.degree < 3 || P.degree > 40) return null;
    const X = sym(v);
    const derivs = [P];
    for (let i = 0; i < P.degree; i++) derivs.push(derivs[i].derivative());
    let F;
    if (other.type === 'pow') {
        // ∫P e^u = e^u·Σ (−1)ᵏ P⁽ᵏ⁾/aᵏ⁺¹, a = u′ (for a^u: a = u′·ln a)
        const a = simp(mul(linearParts(other.exp, v).k, fn('ln', other.base)));
        const terms = derivs.map((d, k) => mul(num(k % 2 ? -1 : 1), d.toNode(v), pow(a, num(-(k + 1)))));
        F = mul(other, add(terms));
    } else {
        // ∫P cos u = sin u·Σ(−1)ᵏP⁽²ᵏ⁾/a²ᵏ⁺¹ + cos u·Σ(−1)ᵏP⁽²ᵏ⁺¹⁾/a²ᵏ⁺²; ∫P sin u = −cos u·Σ… + sin u·Σ…
        const u = other.args[0];
        const a = linearParts(u, v).k;
        const even = [];
        const odd = [];
        derivs.forEach((d, k) => {
            const sgn = Math.floor(k / 2) % 2 ? -1 : 1;
            (k % 2 ? odd : even).push(mul(num(sgn), d.toNode(v), pow(a, num(-(k + 1)))));
        });
        const E0 = add(even.length ? even : [N0]);
        const O1 = add(odd.length ? odd : [N0]);
        F = other.name === 'cos' ? add(mul(fn('sin', u), E0), mul(fn('cos', u), O1)) : add(mul(neg(fn('cos', u)), E0), mul(fn('sin', u), O1));
    }
    void X;
    return {
        F,
        method: 'parts',
        step: step({
            title: T_(`По частям ${P.degree} раз`, `By parts ${P.degree} times`),
            tex: bt((L) => `${iTex(f, v, L)} = ${tx(trySimp(F) ?? F, L)}`),
            text: T_(`Интегрируем по частям ${P.degree} раз подряд, каждый раз беря за u многочлен: его степень падает на единицу, пока не останется число. Удобно вести таблицу: производные многочлена со знаками +, −, +, … умножаются на последовательные первообразные второго множителя.`,
                `Integrate by parts ${P.degree} times, each time with the polynomial as u: its degree drops by one until a number is left. It is convenient to keep a table: the derivatives of the polynomial with signs +, −, +, … times the successive antiderivatives of the other factor.`),
            rule: 'parts-tabular',
        }),
    };
}

// ---- trigonometric substitution for √(α − βx²) and √(α + βx²) with other powers of x

function trigOfArc(name, k, arc, u) {
    // sin(k·arcsin u), cos(k·arcsin u), … as algebraic expressions of u (recurrences on k)
    const s1 = arc === 'asin' ? u : arc === 'atan' ? div(u, fn('sqrt', add(N1, pow(u, N2)))) : null;
    const c1 = arc === 'asin' ? fn('sqrt', add(N1, neg(pow(u, N2)))) : arc === 'atan' ? div(N1, fn('sqrt', add(N1, pow(u, N2)))) : null;
    if (!s1) return null;
    let s = s1;
    let c = c1;
    for (let i = 1; i < k; i++) {
        const ns = add(mul(s, c1), mul(c, s1));
        const nc = add(mul(c, c1), neg(mul(s, s1)));
        s = ns;
        c = nc;
    }
    if (name === 'sin') return s;
    if (name === 'cos') return c;
    if (name === 'tan') return div(s, c);
    if (name === 'cot') return div(c, s);
    if (name === 'sec') return div(N1, c);
    if (name === 'csc') return div(N1, s);
    return null;
}

function unArc(G, v) {
    // sin(k·arcsin(u)) etc. → algebraic; k a positive integer
    return mapNode(G, (m) => {
        if (m.type !== 'fn' || !['sin', 'cos', 'tan', 'cot', 'sec', 'csc'].includes(m.name)) return undefined;
        let a = m.args[0];
        let k = 1;
        if (a.type === 'mul' && a.args.length === 2 && isNum(a.args[0]) && a.args[0].value.isInt() && a.args[0].value.isPos()) {
            k = Number(a.args[0].value.n);
            a = a.args[1];
        }
        if (a.type !== 'fn' || (a.name !== 'asin' && a.name !== 'atan') || k > 12) return undefined;
        return trigOfArc(m.name, k, a.name, a.args[0]);
    });
}

function mTrigSub(f, ctx) {
    const { v } = ctx;
    // find √(α ∓ βx²)ʳ (r odd multiple of 1/2) with the same quadratic everywhere
    let Q = null;
    let ok = true;
    const visit = (n) => {
        if (n.type === 'pow' && isNum(n.exp) && n.exp.value.d === 2n && containsVar(n.base, v)) {
            const P = Poly.fromNode(n.base, v);
            if (!P || P.degree !== 2 || !P.coeff(1).isZero()) ok = false;
            else if (Q && !Q.equals(P)) ok = false;
            else Q = P;
        }
        for (const c of nodeChildren(n)) visit(c);
    };
    visit(f);
    if (!ok || !Q) return null;
    const al = Q.coeff(0);
    const be = Q.coeff(2);
    if (!al.isPos()) return null;
    const kind = be.isNeg() ? 'sin' : 'tan';
    const A = pow(qn(al.div(be.abs())), HALF); // x = A·sin t or A·tan t
    const t = freshVar(f, v);
    const T = sym(t);
    const sa = pow(qn(al), HALF);
    // (α − βx²)^r = (√α·cos t)^(2r),  (α + βx²)^r = (√α/cos t)^(2r)
    const radical = kind === 'sin' ? mul(sa, fn('cos', T)) : div(sa, fn('cos', T));
    const baseKey = nodeKey(Q.toNode(v));
    let g = mapNode(f, (m) => {
        if (m.type === 'pow' && isNum(m.exp) && m.exp.value.d === 2n) {
            const P = Poly.fromNode(m.base, v);
            if (P && nodeKey(P.toNode(v)) === baseKey) return pow(radical, num(m.exp.value.mul(2)));
        }
        return undefined;
    });
    const xOfT = mul(A, fn(kind, T));
    const dx = kind === 'sin' ? mul(A, fn('cos', T)) : div(A, pow(fn('cos', T), N2));
    g = trySimp(mul(substitute(g, { [v]: xOfT }), dx));
    if (!g || containsVar(g, v)) return null;
    const r = I(g, sub(ctx, { v: t }));
    if (!r) return null;
    const arc = kind === 'sin' ? fn('asin', div(sym(v), A)) : fn('atan', div(sym(v), A));
    const Ft = mapNode(r.F, (m) => (m.type === 'fn' && m.name === 'atan' && m.args[0].type === 'fn' && m.args[0].name === 'tan' ? m.args[0].args[0] : undefined));
    const back = trySimp(unArc(substitute(Ft, { [t]: arc }), v));
    if (!back) return null;
    return {
        F: back,
        method: 'trig-root-substitution',
        step: step({
            title: kind === 'sin' ? T_(`Подстановка ${v} = a·sin ${t}`, `Substitution ${v} = a·sin ${t}`) : T_(`Подстановка ${v} = a·tg ${t}`, `Substitution ${v} = a·tan ${t}`),
            tex: bt((L) => `${iTex(f, v, L)} = \\left[${v} = ${tx(simp(xOfT), L)},\\ d${v} = ${tx(simp(dx), L)}\\,d${t}\\right] = ${iTex(g, t, L)} = ${tx(trySimp(r.F) ?? r.F, L)} = ${tx(back, L)}`),
            text: kind === 'sin'
                ? T_(`Под корнем a² − ${v}²: подстановка ${v} = a·sin ${t} (${t} ∈ [−π/2; π/2]) превращает корень в a·cos ${t}, и остаётся тригонометрический интеграл. В конце возвращаемся: ${t} = arcsin(${v}/a), cos ${t} = √(a² − ${v}²)/a.`,
                    `a² − ${v}² under the root: the substitution ${v} = a·sin ${t} (${t} ∈ [−π/2, π/2]) turns the root into a·cos ${t}, leaving a trigonometric integral. At the end go back: ${t} = arcsin(${v}/a), cos ${t} = √(a² − ${v}²)/a.`)
                : T_(`Под корнем a² + ${v}²: подстановка ${v} = a·tg ${t} (${t} ∈ (−π/2; π/2)) превращает корень в a/cos ${t}. В конце возвращаемся: ${t} = arctg(${v}/a).`,
                    `a² + ${v}² under the root: the substitution ${v} = a·tan ${t} (${t} ∈ (−π/2, π/2)) turns the root into a/cos ${t}. At the end go back: ${t} = arctan(${v}/a).`),
            rule: 'trig-root-substitution',
            sub: [r.step],
        }),
    };
}

// cyclic: e^{A}·sin G, e^{A}·cos G with A, G linear
function mCyclic(f, ctx) {
    const { v } = ctx;
    const { coef, rest } = splitCoeff(f);
    if (!rest || rest.type !== 'mul') return null;
    let ex = null;
    let tr = null;
    const consts = [];
    for (const x of rest.args) {
        if (!containsVar(x, v)) consts.push(x);
        else if (x.type === 'pow' && !containsVar(x.base, v) && linearParts(x.exp, v) && !ex) ex = x;
        else if (x.type === 'fn' && (x.name === 'sin' || x.name === 'cos') && linearParts(x.args[0], v) && !tr) tr = x;
        else return null;
    }
    if (!ex || !tr) return null;
    const alpha = simp(mul(linearParts(ex.exp, v).k, fn('ln', ex.base)));
    const beta = linearParts(tr.args[0], v).k;
    const G = tr.args[0];
    const den = add(pow(alpha, N2), pow(beta, N2));
    const body = tr.name === 'sin'
        ? add(mul(alpha, fn('sin', G)), neg(mul(beta, fn('cos', G))))
        : add(mul(alpha, fn('cos', G)), mul(beta, fn('sin', G)));
    const c = mul([num(coef), ...consts]);
    const F = mul(c, ex, body, pow(den, NM1));
    const J = tr.name === 'sin' ? 'cos' : 'sin';
    return {
        F,
        method: 'parts-cyclic',
        step: step({
            title: T_('По частям дважды (циклический интеграл)', 'By parts twice (a cyclic integral)'),
            tex: bt((L) => `I = ${iTex(f, v, L)} = ${tx(trySimp(F) ?? F, L)}`),
            text: T_(`Интегрируем по частям два раза подряд (оба раза u — тригонометрическая функция): после первого раза появляется интеграл с ${J}, после второго снова исходный интеграл I с другим коэффициентом. Получается уравнение I = (…) − k·I, из которого и находим I.`,
                `Integrate by parts twice (both times u is the trigonometric function): the first time gives an integral with ${J}, the second brings back the original integral I with another coefficient. This gives an equation I = (…) − k·I, which we solve for I.`),
            rule: 'parts-cyclic',
        }),
    };
}

// ---- universal substitution t = tg(x/2)

function mWeierstrass(f, ctx) {
    const { v } = ctx;
    const g = toSinCos(f);
    if (!g) return null;
    const S = sym('S__');
    const Cc = sym('C__');
    const X = sym(v);
    const h = mapNode(g, (m) => {
        if (m.type === 'fn' && m.name === 'sin' && isVar(m.args[0], v)) return S;
        if (m.type === 'fn' && m.name === 'cos' && isVar(m.args[0], v)) return Cc;
        return undefined;
    });
    if (containsVar(h, v) || (!containsVar(h, 'S__') && !containsVar(h, 'C__'))) return null;
    const t = freshVar(f, v);
    const T = sym(t);
    const den = add(N1, pow(T, N2));
    const gt = trySimp(mul(substitute(h, { S__: div(mul(N2, T), den), C__: div(add(N1, neg(pow(T, N2))), den) }), div(N2, den)));
    if (!gt || !ratFunctionOf(gt, t)) return null;
    void X;
    return substResult(f, ctx, {
        t, uNode: fn('tan', div(sym(v), N2)), g: gt, rule: 'universal-substitution',
        title: T_('Универсальная подстановка', 'Universal substitution'),
        dtTex: (L) => `\\sin ${v} = \\frac{2${t}}{1 + ${t}^{2}},\\ \\cos ${v} = \\frac{1 - ${t}^{2}}{1 + ${t}^{2}},\\ d${v} = \\frac{2\\,d${t}}{1 + ${t}^{2}}`,
        text: T_('Подынтегральная функция рационально выражается через sin x и cos x. Универсальная подстановка t = tg(x/2) превращает её в рациональную дробь от t (ответ верен на каждом промежутке, где tg(x/2) определён).',
            'The integrand is a rational function of sin x and cos x. The universal substitution t = tan(x/2) turns it into a rational function of t (the answer holds on each interval where tan(x/2) is defined).'),
    });
}

const METHODS = [mConst, mTable, mLinearity, mLinearSub, mDerivPattern, mRational, mCyclic, mTrig, mExpand, mUSub, mQuadRoot, mRadicalPoly, mRationalizing, mPolyTimes, mParts, mTrigLower, mTrigSub, mWeierstrass];

// ---------------------------------------------------------------- non-elementary integrals

function nonElementaryHint(f, v) {
    const g = trySimp(f) ?? f;
    const { rest } = splitCoeff(g);
    if (!rest) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    const vfs = fs.filter((x) => containsVar(x, v));
    const key = (x) => nodeKey(x);
    const X = sym(v);
    const quadExp = (x) => x.type === 'pow' && isConst(x.base) && x.base.name === 'e' && (() => {
        const P = Poly.fromNode(x.exp, v);
        return P && P.degree === 2;
    })();
    if (vfs.length === 1 && quadExp(vfs[0])) {
        // e^(−x²) goes with erf, e^(+x²) with the imaginary error function erfi
        if (Poly.fromNode(vfs[0].exp, v).lead.isPos()) {
            return T_('Этот интеграл не выражается через элементарные функции (так доказал Лиувилль). Через специальную функцию, мнимую функцию ошибок: ∫e^(x²)dx = (√π/2)·erfi x + C.',
                'This integral has no elementary antiderivative (Liouville). With a special function, the imaginary error function: ∫e^(x²)dx = (√π/2)·erfi x + C.');
        }
        return T_('Этот интеграл не выражается через элементарные функции (так доказал Лиувилль). Через специальную функцию ошибок: ∫e^(−x²)dx = (√π/2)·erf x + C.',
            'This integral has no elementary antiderivative (Liouville). With the error function: ∫e^(−x²)dx = (√π/2)·erf x + C.');
    }
    const names = vfs.map((x) => (x.type === 'fn' ? x.name : x.type === 'pow' && x.base.type === 'fn' ? x.base.name + '^' + key(x.exp) : key(x)));
    const xm1 = key(pow(X, NM1));
    if (vfs.length === 2 && vfs.some((x) => key(x) === xm1)) {
        const other = vfs.find((x) => key(x) !== xm1);
        if (other.type === 'fn' && other.name === 'sin' && isVar(other.args[0], v)) return T_('∫(sin x / x)dx не берётся в элементарных функциях; это интегральный синус Si x.', '∫(sin x / x)dx has no elementary antiderivative; it is the sine integral Si x.');
        if (other.type === 'fn' && other.name === 'cos' && isVar(other.args[0], v)) return T_('∫(cos x / x)dx не берётся в элементарных функциях; это интегральный косинус Ci x.', '∫(cos x / x)dx has no elementary antiderivative; it is the cosine integral Ci x.');
        if (other.type === 'pow' && isConst(other.base) && other.base.name === 'e' && isVar(other.exp, v)) return T_('∫(eˣ / x)dx не берётся в элементарных функциях; это интегральная экспонента Ei x.', '∫(eˣ / x)dx has no elementary antiderivative; it is the exponential integral Ei x.');
    }
    if (vfs.length === 1 && vfs[0].type === 'pow' && isNum(vfs[0].exp) && vfs[0].exp.value.eq(-1) && vfs[0].base.type === 'fn' && vfs[0].base.name === 'ln') {
        return T_('∫dx/ln x не берётся в элементарных функциях; это интегральный логарифм li x.', '∫dx/ln x has no elementary antiderivative; it is the logarithmic integral li x.');
    }
    if (vfs.length === 1 && vfs[0].type === 'fn' && (vfs[0].name === 'sin' || vfs[0].name === 'cos')) {
        const P = Poly.fromNode(vfs[0].args[0], v);
        if (P && P.degree === 2) return T_('Интегралы Френеля ∫sin(x²)dx и ∫cos(x²)dx не выражаются через элементарные функции.', 'The Fresnel integrals ∫sin(x²)dx and ∫cos(x²)dx have no elementary antiderivative.');
    }
    if (vfs.length === 1 && vfs[0].type === 'pow' && isVar(vfs[0].base, v) && isVar(vfs[0].exp, v)) return T_('∫xˣdx не выражается через элементарные функции.', '∫xˣdx has no elementary antiderivative.');
    void names;
    return null;
}

// ---------------------------------------------------------------- cleaning the answer

function cleanAnti(F, v) {
    let G = simp(F);
    // atan(tan u) = u up to a piecewise constant — fine for an antiderivative
    G = simp(mapNode(G, (m) => (m.type === 'fn' && m.name === 'atan' && m.args[0].type === 'fn' && m.args[0].name === 'tan' ? m.args[0].args[0] : undefined)));
    // ln|u| with u > 0 everywhere (after a substitution t = eˣ, …) is just ln u
    G = simp(mapNode(G, (m) => (m.type === 'fn' && m.name === 'ln' && m.args[0].type === 'fn' && m.args[0].name === 'abs' && surelyPositive(m.args[0].args[0], v) ? fn('ln', m.args[0].args[0]) : undefined)));
    if (G.type === 'add') {
        const kept = G.args.filter((t) => containsVar(t, v));
        if (kept.length && kept.length < G.args.length) G = simp(add(kept));
    }
    return niceForm(G, v, { fnFractions: false });
}

// ---------------------------------------------------------------- public API

function checkExpr(node) {
    if (node.type === 'rel' || node.type === 'chain' || node.type === 'list') {
        throw new MathError({ ru: 'Нужна формула функции, а не уравнение или список', en: 'A formula is needed, not an equation or a list' }, null, null, 'not-expr');
    }
}

function answerStep(title, tex) {
    const s = step({ title, tex, rule: 'answer' });
    s.final = true;
    return s;
}

/**
 * Indefinite integral. → {result: node | null, method, steps, verified, reason?: {ru, en}, tex}.
 * result is an antiderivative (the printed tex adds + C); verified means F′ = f was checked numerically on
 * the domain. When nothing works (or the only candidate fails the check), result is null and reason says
 * so honestly (with a hint for known non-elementary integrals).
 */
export function integrate(node, v = 'x', opts = {}) {
    node = asNode(node);
    checkExpr(node);
    let f;
    try {
        f = simp(node);
    } catch (e) {
        if (e instanceof MathError) throw e;
        throw new MathError({ ru: 'Не удалось разобрать выражение', en: 'Could not process the expression' }, null, null, 'internal');
    }
    const ctx = { v, depth: 0, budget: { calls: 0, max: opts.budget ?? 600, memo: new Map() } };
    const start = step({
        title: T_('Что интегрируем', 'What we integrate'),
        tex: bt((L) => iTex(node, v, L)),
        text: freeVars(node).filter((w) => w !== v).length
            ? T_(`Интегрируем по ${v}; остальные буквы считаем постоянными.`, `We integrate with respect to ${v}; the other letters are constants.`)
            : T_('Ищем первообразную: функцию, производная которой равна подынтегральной.', 'We look for an antiderivative: a function whose derivative is the integrand.'),
        rule: 'start',
    });
    const r = I(f, ctx);
    const fail = (reason) => ({
        result: null,
        method: null,
        steps: opts.steps ? [start, step({ title: T_('Не получилось', 'Not found'), text: reason, rule: 'fail' })] : [],
        verified: false,
        reason,
        tex: null,
    });
    if (!r) {
        const hint = nonElementaryHint(f, v);
        return fail(hint ?? T_('Не удалось найти первообразную: такой интеграл движок пока не берёт (возможно, он и не выражается через элементарные функции). Определённый интеграл можно посчитать численно.',
            'Could not find an antiderivative: the engine cannot do this integral yet (it may have no elementary antiderivative at all). A definite integral can still be computed numerically.'));
    }
    let F = cleanAnti(r.F, v);
    let verified = checkAnti(F, f, v) === true;
    if (!verified) {
        const raw = simp(r.F);
        if (checkAnti(raw, f, v) === true) {
            F = prettyForm(raw);
            verified = true;
        }
    }
    if (!verified && checkAnti(F, f, v) === false) {
        return fail(T_('Найденная функция не прошла проверку дифференцированием, поэтому ответа не показываем.', 'The candidate failed the check by differentiation, so no answer is shown.'));
    }
    const tex = bt((L) => `${iTex(node, v, L)} = ${tx(F, L)} + C`);
    const steps = [];
    if (opts.steps) {
        steps.push(start);
        steps.push(r.step);
        const rawTex = (L) => tx(simp(r.F), L);
        if (rawTex('ru') !== tx(F, 'ru')) {
            const raw = simp(r.F);
            const dropped = raw.type === 'add' && raw.args.some((t) => !containsVar(t, v));
            const atanTan = nodeSome(raw, (m) => m.type === 'fn' && m.name === 'atan' && m.args[0].type === 'fn' && m.args[0].name === 'tan');
            let text = dropped
                ? T_('Приводим ответ к аккуратному виду; слагаемые-константы уходят в произвольную постоянную C.', 'Tidy up the answer; constant terms go into the arbitrary constant C.')
                : T_('Приводим ответ к аккуратному виду.', 'Tidy up the answer.');
            if (atanTan) {
                text = T_(`${text.ru} arctg(tg u) отличается от u на постоянную (πk на каждом промежутке), её тоже забирает C.`, `${text.en} arctan(tan u) differs from u by a constant (πk on each interval), which C also absorbs.`);
            }
            steps.push(step({
                title: T_('Упрощаем', 'Simplify'),
                tex: bt((L) => `${rawTex(L)} = ${tx(F, L)}${dropped ? ' + \\mathrm{const}' : ''}`),
                text,
                rule: 'simplify',
            }));
        }
        steps.push(step({
            title: T_('Проверка', 'Check'),
            tex: bt((L) => `\\left(${tx(F, L)}\\right)' = ${tx(f, L)}`),
            text: verified
                ? T_('Дифференцируем ответ и сравниваем с подынтегральной функцией в нескольких точках — совпадает.', 'Differentiate the answer and compare with the integrand at several points: they agree.')
                : T_('Проверить ответ численно не удалось: область определения слишком узкая для выборочных точек.', 'The numeric check could not be done: the domain is too narrow for the sample points.'),
            rule: 'check',
        }));
        steps.push(answerStep(T_('Ответ', 'Answer'), tex));
    }
    return { result: F, method: r.method, steps, verified, tex };
}

// ---------------------------------------------------------------- definite integrals

function boundNode(x) {
    if (x === Infinity) return sym('inf');
    if (x === -Infinity) return neg(sym('inf'));
    return asNode(x);
}

function boundValue(n) {
    const s = trySimp(n) ?? n;
    if (isConst(s) && s.name === 'inf') return { node: s, x: Infinity };
    if (s.type === 'mul' && s.args.length === 2 && isNum(s.args[0]) && s.args[0].value.isNeg() && isConst(s.args[1]) && s.args[1].name === 'inf') return { node: s, x: -Infinity };
    const x = evaluate(s);
    if (!Number.isFinite(x)) throw new MathError({ ru: 'Пределы интегрирования — числа или ±∞', en: 'The limits of integration must be numbers or ±∞' }, null, null, 'range');
    return { node: s, x };
}

const boundTex = (b, L) => (b.x === Infinity ? '+\\infty' : b.x === -Infinity ? '-\\infty' : tx(b.node, L));

/** Candidate singular points of g on [lo, hi]: zeros of denominators and of log arguments, poles of tg/ctg/sec/cosec. */
function singularCandidates(g, v, lo, hi) {
    const bases = [];
    const walk = (n) => {
        if (n.type === 'pow' && isNum(n.exp) && n.exp.value.isNeg() && containsVar(n.base, v)) bases.push(n.base);
        if (n.type === 'fn' && (n.name === 'ln' || n.name === 'lg') && containsVar(n.args[0], v)) bases.push(n.args[0]);
        if (n.type === 'fn' && n.name === 'log' && containsVar(n.args[1], v)) bases.push(n.args[1]);
        if (n.type === 'fn' && (n.name === 'tan' || n.name === 'sec') && containsVar(n.args[0], v)) bases.push(fn('cos', n.args[0]));
        if (n.type === 'fn' && (n.name === 'cot' || n.name === 'csc') && containsVar(n.args[0], v)) bases.push(fn('sin', n.args[0]));
        if (n.type === 'fn' && n.name === 'abs' && containsVar(n.args[0], v)) bases.push(n.args[0]);
        nodeChildren(n).forEach(walk);
    };
    walk(g);
    const wl = Number.isFinite(lo) ? lo : -1000;
    const wh = Number.isFinite(hi) ? hi : 1000;
    const pts = [];
    for (const B of bases) {
        const P = Poly.fromNode(B, v);
        if (P && P.degree >= 1) {
            for (const { root } of P.rationalRoots()) {
                const x = root.toNumber();
                if (x >= wl && x <= wh) pts.push({ x, node: num(root) });
            }
        }
        let bc;
        try {
            bc = compile(B, [v]);
        } catch {
            continue;
        }
        try {
            for (const r of numFindRoots(bc, wl, wh, { samples: 2000 })) {
                if (r.kind === 'interval') continue;
                pts.push({ x: r.x, node: null });
            }
        } catch {
            // no roots found numerically
        }
    }
    return mergePoints(pts);
}

function mergePoints(list) {
    const sorted = [...list].sort((a, b) => a.x - b.x);
    const out = [];
    for (const p of sorted) {
        const last = out[out.length - 1];
        if (last && Math.abs(last.x - p.x) <= 1e-7 * Math.max(1, Math.abs(p.x))) {
            if (!last.node && p.node) out[out.length - 1] = p;
            continue;
        }
        out.push(p);
    }
    return out;
}

/** Points of [l, h] where F jumps although f stays bounded (a numeric scan refined by bisection). */
function jumpsOf(Fc, fc, l, h) {
    const N = 2000;
    const out = [];
    let prev = null;
    for (let i = 0; i <= N; i++) {
        const x = l + ((h - l) * (i + 0.37)) / (N + 1);
        const y = Fc(x);
        if (prev && Number.isFinite(y) && Number.isFinite(prev.y)) {
            const slope = Math.max(Math.abs(fc(x)), Math.abs(fc(prev.x)), Math.abs(fc((x + prev.x) / 2)), 1);
            if (Math.abs(y - prev.y) > 50 * slope * (x - prev.x) + 1e-6) {
                let a = prev.x;
                let b = x;
                const ya = prev.y;
                for (let k = 0; k < 80; k++) {
                    const m = (a + b) / 2;
                    const ym = Fc(m);
                    if (Number.isFinite(ym) && Math.abs(ym - ya) < Math.abs(Fc(b) - ym)) a = m;
                    else b = m;
                }
                out.push({ x: (a + b) / 2, node: null });
            }
        }
        prev = { x, y };
    }
    return out;
}

/** Snap a numeric point to a nice exact node (integers, simple fractions, multiples of π/12). */
function exactPoint(x) {
    for (const d of [1, 2, 3, 4, 5, 6, 8, 10, 12]) {
        const n = Math.round(x * d);
        if (Math.abs(n / d - x) < 1e-9 * Math.max(1, Math.abs(x))) return num(new Q(BigInt(n), BigInt(d)));
    }
    const k = Math.round((x / Math.PI) * 12);
    if (Math.abs((k / 12) * Math.PI - x) < 1e-9) return simp(mul(num(new Q(BigInt(k), 12n)), PI));
    return null;
}

/** Value of F at an end of a piece: exact substitution (unless forced), else a one-sided limit. */
function endValue(F, v, b, side, force) {
    if (Number.isFinite(b.x) && !force) {
        try {
            const s = simp(substitute(F, { [v]: b.node }));
            const x = evaluate(s);
            if (Number.isFinite(x)) return { kind: 'fin', node: s, x, how: 'subst' };
        } catch {
            // fall through to the limit
        }
    }
    const L = limit(F, v, b.node, { side });
    if (L.value === 'inf' || L.value === '-inf') return { kind: L.value, how: 'limit', lim: L };
    if (L.value && typeof L.value === 'object') {
        const x = evaluate(L.value);
        if (Number.isFinite(x)) return { kind: 'fin', node: L.value, x, how: 'limit', lim: L };
    }
    return { kind: 'unknown', how: 'limit', lim: L };
}

function numericValue(fc, lo, hi) {
    try {
        const r = numIntegrate(fc, lo, hi, { info: true });
        return Number.isFinite(r.value) ? r : null;
    } catch {
        return null;
    }
}

/** The numeric value with a convergence verdict ({value, ok, divergent, reason}), or null. */
function checkedValue(fc, lo, hi) {
    try {
        return numIntegrate(fc, lo, hi, { info: true, check: true });
    } catch {
        return null;
    }
}

/** For an improper integral computed numerically: do the partial integrals settle as the cut-off moves out? */
function improperSettles(fc, lo, hi) {
    const val = (a, b) => numericValue(fc, a, b)?.value ?? NaN;
    const seq = [];
    if (!Number.isFinite(hi) || !Number.isFinite(lo)) {
        for (const R of [1e2, 1e4, 1e6]) seq.push(val(Number.isFinite(lo) ? lo : -R, Number.isFinite(hi) ? hi : R));
    } else {
        const w = hi - lo;
        const l0 = !Number.isFinite(fc(lo)) || poleAt(fc, lo);
        const h0 = !Number.isFinite(fc(hi)) || poleAt(fc, hi);
        for (const e of [1e-2, 1e-4, 1e-6]) seq.push(val(l0 ? lo + e * w : lo, h0 ? hi - e * w : hi));
    }
    if (!seq.every(Number.isFinite)) return false;
    const d1 = Math.abs(seq[1] - seq[0]);
    const d2 = Math.abs(seq[2] - seq[1]);
    return d2 <= 1e-3 * Math.max(1, Math.abs(seq[2])) && d2 <= d1;
}

const poleAt = (fc, x) => {
    const d = 1e-8 * Math.max(1, Math.abs(x));
    const yl = fc(x - d);
    const yr = fc(x + d);
    return !Number.isFinite(yl) || !Number.isFinite(yr) || Math.abs(yl) > 1e6 || Math.abs(yr) > 1e6;
};

/**
 * ∫ₐᵇ f dv. a, b: numbers, strings or nodes (inf / -inf allowed). opts: {steps}.
 * → {value: node | 'inf' | '-inf' | null, numeric: number | null, exact: boolean, approx: boolean,
 *    converges: boolean | null, improper: boolean, antiderivative: node | null, method, steps, tex}.
 * Exact values come from Newton–Leibniz: the interval is split at the points where f blows up or the
 * antiderivative jumps, and every end of a piece that is infinite or singular is a one-sided limit of F
 * (an infinite limit means the integral diverges). The exact value is cross-checked numerically.
 * Otherwise a numeric value, marked ≈.
 */
// F(b′) − F(a′) against the quadrature on finite pieces [a′; b′] inside an improper interval (ends pulled in from
// infinity and away from poles): does the antiderivative really match f there?
function truncatedAgrees(F, fc, v, lo, hi, interior) {
    let Fc;
    try { Fc = compile(F, [v]); } catch { return false; }
    const ends = [lo, ...interior.filter((p) => p.pole), hi];
    for (let i = 0; i + 1 < ends.length; i++) {
        const a0 = ends[i].x, b0 = ends[i + 1].x;
        const tries = [];
        for (const far of [1e2, 1e4]) {
            const a = Number.isFinite(a0) ? a0 + (poleAt(fc, a0) ? 1e-3 * Math.max(1, Math.abs(a0)) : 0) : (Number.isFinite(b0) ? b0 : 0) - far;
            const b = Number.isFinite(b0) ? b0 - (poleAt(fc, b0) ? 1e-3 * Math.max(1, Math.abs(b0)) : 0) : (Number.isFinite(a0) ? a0 : 0) + far;
            if (!(b > a)) continue;
            let q;
            try { q = numIntegrate(fc, a, b, { tol: 1e-12 }); } catch { q = NaN; }
            const e = Fc(b) - Fc(a);
            if (!Number.isFinite(q) || !Number.isFinite(e)) return false;
            tries.push(Math.abs(q - e) <= 1e-7 * Math.max(1, Math.abs(e)));
        }
        if (!tries.length || !tries.every(Boolean)) return false;
    }
    return true;
}

export function integrateDefinite(node, v = 'x', a = 0, b = 1, opts = {}) {
    node = asNode(node);
    checkExpr(node);
    const f = simp(node);
    const A = boundValue(boundNode(a));
    const B = boundValue(boundNode(b));
    const steps = [];
    const wantSteps = !!opts.steps;
    const head = (L) => `\\int_{${boundTex(A, L)}}^{${boundTex(B, L)}} ${f.type === 'add' ? paren(tx(node, L)) : tx(node, L)}\\,d${v}`;
    if (wantSteps) {
        steps.push(step({
            title: T_('Что считаем', 'What we compute'),
            tex: bt(head),
            text: T_('Находим первообразную F и пользуемся формулой Ньютона — Лейбница: ∫ₐᵇ f dx = F(b) − F(a). Если предел бесконечен или функция на отрезке не ограничена, интеграл несобственный — вместо значений F берём пределы.',
                'Find an antiderivative F and use the Newton–Leibniz formula: ∫ₐᵇ f dx = F(b) − F(a). If a limit is infinite or the function is unbounded on the interval, the integral is improper and F is replaced by limits.'),
            rule: 'start',
        }));
    }
    const out = (o) => ({ value: null, numeric: null, exact: false, approx: false, converges: null, improper: false, antiderivative: null, method: null, steps, tex: null, ...o });
    if (A.x === B.x) {
        return out({ value: N0, numeric: 0, exact: true, converges: true, method: 'equal-limits', tex: bt((L) => `${head(L)} = 0`) });
    }
    const flip = A.x > B.x;
    const lo = flip ? B : A;
    const hi = flip ? A : B;
    const others = freeVars(f).filter((w) => w !== v);
    if (others.length) throw new MathError({ ru: `Для определённого интеграла нужны числовые значения букв: ${others.join(', ')}`, en: `A definite integral needs numeric values for: ${others.join(', ')}` }, null, null, 'unbound');
    const fc = compile(f, [v]);
    // domain: f must be defined almost everywhere on the interval
    const pa = Number.isFinite(lo.x) ? lo.x : Math.min(-1, hi.x - 1000);
    const pb = Number.isFinite(hi.x) ? hi.x : Math.max(1, lo.x + 1000);
    let nan = 0;
    for (let i = 1; i < 200; i++) if (Number.isNaN(fc(pa + ((pb - pa) * i) / 200))) nan++;
    if (nan > 4) {
        return out({
            method: 'undefined',
            steps: wantSteps ? [step({ title: T_('Функция не определена', 'The function is not defined'), text: T_('Подынтегральная функция не определена на части отрезка интегрирования, поэтому такой интеграл (в действительных числах) не имеет смысла.', 'The integrand is undefined on part of the interval, so this integral makes no sense over the reals.'), rule: 'fail' })] : [],
        });
    }
    const inside = (x) => x > lo.x + 1e-9 * Math.max(1, Math.abs(lo.x)) && x < hi.x - 1e-9 * Math.max(1, Math.abs(hi.x));
    const fPoles = singularCandidates(f, v, lo.x, hi.x).filter((p) => inside(p.x) && poleAt(fc, p.x));
    let improper = !Number.isFinite(lo.x) || !Number.isFinite(hi.x) || !Number.isFinite(fc(lo.x)) || !Number.isFinite(fc(hi.x)) || poleAt(fc, lo.x) || poleAt(fc, hi.x) || fPoles.length > 0;
    const anti = integrate(node, v, { steps: wantSteps });
    let exactNode = null;
    let diverges = null;
    let unknown = false;
    let interior = fPoles;
    let parts = [];
    if (anti.result) {
        const F = anti.result;
        const Fs = trySimp(F) ?? F;
        let Fc = null;
        try {
            Fc = compile(Fs, [v]);
        } catch {
            Fc = null;
        }
        let cand = [...fPoles, ...singularCandidates(Fs, v, lo.x, hi.x).filter((p) => inside(p.x))];
        if (Fc) {
            const l = Number.isFinite(lo.x) ? lo.x : Math.min(hi.x, 0) - 100;
            const h = Number.isFinite(hi.x) ? hi.x : Math.max(lo.x, 0) + 100;
            cand.push(...jumpsOf(Fc, fc, l, h).filter((p) => inside(p.x)));
        }
        cand = mergePoints(cand);
        // keep the points where F is not continuous (or f blows up); a point needs an exact position
        interior = [];
        for (const p of cand) {
            const d = 1e-7 * Math.max(1, Math.abs(p.x));
            const yl = Fc ? Fc(p.x - d) : NaN;
            const yr = Fc ? Fc(p.x + d) : NaN;
            const smooth = Number.isFinite(yl) && Number.isFinite(yr) && Math.abs(yl - yr) < 1e-5 * Math.max(1, Math.abs(yl)) && !poleAt(fc, p.x);
            if (smooth) continue;
            const nodeX = p.node ?? exactPoint(p.x);
            if (!nodeX) {
                unknown = true;
                break;
            }
            interior.push({ x: p.x, node: nodeX, pole: poleAt(fc, p.x) });
        }
        if (!unknown) {
            const pts = [lo, ...interior, hi];
            for (let i = 0; i + 1 < pts.length; i++) {
                const p = pts[i];
                const r = pts[i + 1];
                const forceTop = i + 1 < pts.length - 1 || !Number.isFinite(fc(r.x)) || poleAt(fc, r.x);
                const forceBot = i > 0 || !Number.isFinite(fc(p.x)) || poleAt(fc, p.x);
                const top = endValue(F, v, r, 'left', forceTop);
                const bot = endValue(F, v, p, 'right', forceBot);
                parts.push({ p, r, top, bot });
                if (['inf', '-inf'].includes(top.kind) || ['inf', '-inf'].includes(bot.kind)) diverges = diverges ?? { p, r, top, bot };
                if (top.kind === 'unknown' || bot.kind === 'unknown') unknown = true;
            }
            if (!diverges && !unknown) {
                exactNode = trySimp(add(parts.map((x) => add(x.top.node, neg(x.bot.node)))));
                if (exactNode && flip) exactNode = trySimp(neg(exactNode));
            }
        }
        if (interior.some((p) => p.pole)) improper = true;
        if (wantSteps && (exactNode || diverges)) {
            steps.push(step({
                title: T_('Первообразная', 'Antiderivative'),
                tex: bt((L) => `F(${v}) = ${tx(F, L)}`),
                rule: 'antiderivative',
                sub: anti.steps.filter((s) => s.rule !== 'answer' && s.rule !== 'start'),
            }));
            if (flip) {
                steps.push(step({
                    title: T_('Меняем пределы местами', 'Swap the limits'),
                    tex: bt((L) => `\\int_{${boundTex(A, L)}}^{${boundTex(B, L)}} = -\\int_{${boundTex(B, L)}}^{${boundTex(A, L)}}`),
                    text: T_('Нижний предел больше верхнего: переставляем пределы и меняем знак.', 'The lower limit is larger than the upper one: swap them and change the sign.'),
                    rule: 'swap',
                }));
            }
            if (interior.length) {
                const poles = interior.some((p) => p.pole);
                steps.push(step({
                    title: poles ? T_('Особые точки внутри отрезка', 'Singular points inside the interval') : T_('Разрыв первообразной', 'A jump of the antiderivative'),
                    tex: bt((L) => `${v} = ${interior.map((p) => tx(p.node, L)).join(L === 'ru' ? ';\\ ' : ',\\ ')}`),
                    text: poles
                        ? T_('Внутри отрезка функция обращается в бесконечность. Формулу Ньютона — Лейбница через такую точку применять нельзя: разбиваем интеграл на части и каждую считаем как несобственный интеграл (через пределы).',
                            'The function blows up inside the interval. Newton–Leibniz cannot be applied across such a point: split the integral and treat each part as an improper integral (through limits).')
                        : T_('Найденная первообразная делает скачок внутри отрезка (так бывает после замены t = tg(x/2)). Разбиваем отрезок в этой точке и на каждой части берём пределы первообразной.',
                            'The antiderivative jumps inside the interval (this happens after the substitution t = tan(x/2)). Split the interval there and take limits of the antiderivative on each part.'),
                    rule: 'split',
                }));
            }
            for (const x of parts) {
                const lim = (e, pt, sideSign) => (e.how === 'limit' ? `\\lim_{${v} \\to ${Number.isFinite(pt.x) ? `{${tx(pt.node, 'en')}}^{${sideSign}}` : boundTex(pt, 'en')}} F(${v})` : null);
                const val = (e) => (e.kind === 'fin' ? null : e.kind === 'inf' ? '+\\infty' : e.kind === '-inf' ? '-\\infty' : '?');
                const isLim = x.top.how === 'limit' || x.bot.how === 'limit';
                steps.push(step({
                    title: isLim ? T_('Несобственный интеграл: пределы', 'Improper integral: limits') : T_('Формула Ньютона — Лейбница', 'Newton–Leibniz formula'),
                    tex: bt((L) => {
                        const upper = x.top.kind === 'fin' ? tx(x.top.node, L) : val(x.top);
                        const lower = x.bot.kind === 'fin' ? tx(x.bot.node, L) : val(x.bot);
                        const lu = lim(x.top, x.r, '-') ?? `F\\left(${boundTex(x.r, L)}\\right)`;
                        const ll = lim(x.bot, x.p, '+') ?? `F\\left(${boundTex(x.p, L)}\\right)`;
                        const both = x.top.kind === 'fin' && x.bot.kind === 'fin' ? trySimp(add(x.top.node, neg(x.bot.node))) : null;
                        return `\\int_{${boundTex(x.p, L)}}^{${boundTex(x.r, L)}} f\\,d${v} = ${lu} - ${ll} = ${upper} - ${/^-/.test(lower) ? `\\left(${lower}\\right)` : lower}${both ? ` = ${tx(niceForm(both), L)}` : ''}`;
                    }),
                    text: isLim
                        ? T_('На бесконечном пределе, в точке, где функция не ограничена, или в точке скачка первообразной её значение заменяем односторонним пределом.', 'At an infinite limit, at a point where the function is unbounded, or where the antiderivative jumps, its value is replaced by a one-sided limit.')
                        : T_('Первообразная непрерывна на отрезке, поэтому интеграл равен F(b) − F(a).', 'The antiderivative is continuous on the interval, so the integral equals F(b) − F(a).'),
                    rule: 'newton-leibniz',
                }));
            }
        }
    }
    if (diverges) {
        const signOf = (k) => (k === 'inf' ? 1 : k === '-inf' ? -1 : 0);
        const contributions = parts.map((x) => signOf(x.top.kind) - signOf(x.bot.kind)).filter((c) => c !== 0);
        const same = contributions.length && contributions.every((c) => Math.sign(c) === Math.sign(contributions[0]));
        const val = same ? ((flip ? -1 : 1) * Math.sign(contributions[0]) > 0 ? 'inf' : '-inf') : null;
        const tex = bt((L) => `${head(L)}\\ ${L === 'ru' ? '\\text{расходится}' : '\\text{diverges}'}`);
        if (wantSteps) {
            const s = answerStep(T_('Интеграл расходится', 'The integral diverges'), tex);
            s.text = T_('Предел первообразной бесконечен, значит, несобственный интеграл расходится (площадь под графиком бесконечна).', 'The limit of the antiderivative is infinite, so the improper integral diverges (the area under the graph is infinite).');
            steps.push(s);
        }
        return out({ value: val, converges: false, improper: true, antiderivative: anti.result, method: 'improper', tex });
    }
    // numeric value: for the cross-check, or as the answer
    const cuts = [lo, ...mergePoints([...interior, ...fPoles]).filter((p) => inside(p.x)), hi];
    let numeric = 0;
    let numOk = true;
    let checked = true; // every piece passed the numeric convergence check
    let numDiverges = null; // a piece the check calls divergent
    for (let i = 0; i + 1 < cuts.length; i++) {
        const piece = checkedValue(fc, cuts[i].x, cuts[i + 1].x);
        if (piece?.divergent) numDiverges = numDiverges ?? piece;
        if (!piece?.ok) checked = false;
        const res = piece && Number.isFinite(piece.value) ? piece : numericValue(fc, cuts[i].x, cuts[i + 1].x);
        if (!res) {
            numOk = false;
            break;
        }
        numeric += res.value;
    }
    if (flip) numeric = -numeric;
    if (improper && !exactNode && numDiverges) {
        // no exact verdict (the limit of F does not exist, or there is no F), but the tail visibly does not settle
        const s = numDiverges.value === Infinity ? 1 : numDiverges.value === -Infinity ? -1 : 0;
        const val = s ? ((flip ? -s : s) > 0 ? 'inf' : '-inf') : null;
        const tex = bt((L) => `${head(L)}\ ${L === 'ru' ? '\text{расходится}' : '\text{diverges}'}`);
        if (wantSteps) {
            const st = answerStep(T_('Интеграл расходится', 'The integral diverges'), tex);
            st.text = numDiverges.reason === 'pole'
                ? T_('Функция растёт у особой точки так быстро, что площадь рядом с ней бесконечна: интеграл расходится.', 'The function grows so fast near the singular point that the area there is infinite: the integral diverges.')
                : s ? T_('На бесконечности функция убывает недостаточно быстро: площадь под графиком бесконечна.', 'The function does not decay fast enough at infinity: the area under the graph is infinite.')
                    : T_('Интегралы по всё более длинным отрезкам не стремятся ни к какому числу: волны не затухают, и площадь под графиком то набирается, то убывает. Несобственный интеграл расходится.', 'The integrals over longer and longer intervals do not tend to any number: the waves do not die down, and the area keeps growing and shrinking. The improper integral diverges.');
            steps.push(st);
        }
        return out({ value: val, converges: false, improper: true, antiderivative: anti.result, method: 'improper-numeric', tex });
    }
    if (exactNode) {
        const ex = evaluate(exactNode);
        const tol = improper ? 1e-4 : 1e-6;
        // A slowly decaying tail (1/(x ln²x) on [e; ∞)) fools the quadrature: then check the antiderivative on a long
        // finite piece, where the numbers are reliable, instead of letting a bad number veto a verified answer.
        const agrees = Number.isFinite(ex) && (!numOk || Math.abs(ex - numeric) <= tol * Math.max(1, Math.abs(ex)) || (improper && truncatedAgrees(anti.result, fc, v, lo, hi, interior)));
        if (agrees) {
            const value = niceForm(exactNode);
            const tex = bt((L) => `${head(L)} = ${tx(value, L)}${isNum(trySimp(value) ?? value) && (trySimp(value) ?? value).value.isInt() ? '' : ` \\approx ${fmtNum(ex, L)}`}`);
            if (wantSteps) steps.push(answerStep(T_('Ответ', 'Answer'), tex));
            return out({ value, numeric: ex, exact: true, converges: true, improper, antiderivative: anti.result, method: improper ? 'improper' : interior.length ? 'newton-leibniz-pieces' : 'newton-leibniz', tex });
        }
    }
    const poles = fPoles.length > 0;
    const tailOk = !improper || exactNode || checked || improperSettles(fc, lo.x, hi.x);
    if (!numOk || !Number.isFinite(numeric) || (poles && !exactNode) || !tailOk) {
        if (wantSteps) {
            steps.push(step({
                title: T_('Не получилось', 'Not found'),
                text: poles || !tailOk
                    ? T_('Интеграл несобственный, а точно проверить его сходимость не удалось; численно он не устанавливается (похоже, расходится). Ненадёжное число не приводим.', 'The integral is improper and its convergence could not be checked exactly; numerically it does not settle (it seems to diverge). No unreliable number is given.')
                    : T_('Ни точно, ни численно посчитать этот интеграл не удалось (возможно, он расходится).', 'This integral could not be computed exactly or numerically (it may diverge).'),
                rule: 'fail',
            }));
        }
        return out({ improper, antiderivative: anti.result, method: 'failed' });
    }
    const tex = bt((L) => `${head(L)} \\approx ${fmtNum(numeric, L)}`);
    if (wantSteps) {
        if (!anti.result && anti.reason) steps.push(step({ title: T_('Первообразная', 'Antiderivative'), text: anti.reason, rule: 'antiderivative' }));
        steps.push(step({
            title: T_('Численное интегрирование', 'Numerical integration'),
            text: !anti.result
                ? T_('Первообразную в элементарных функциях найти не удалось, поэтому считаем интеграл численно (адаптивная квадратура Гаусса — Кронрода). Значение приближённое.', 'No elementary antiderivative was found, so the integral is computed numerically (adaptive Gauss–Kronrod quadrature). The value is approximate.')
                : T_('Точное значение подтвердить не удалось, поэтому приводим численное (приближённое).', 'The exact value could not be confirmed, so a numeric (approximate) value is given.'),
            rule: 'numeric',
        }));
        steps.push(answerStep(T_('Ответ (приближённо)', 'Answer (approximate)'), tex));
    }
    return out({ numeric, approx: true, converges: true, improper, antiderivative: anti.result, method: 'numeric', tex });
}

function fmtNum(x, L) {
    let s = x.toFixed(6);
    if (s.includes('.')) s = s.replace(/\.?0+$/, '');
    if (s === '-0') s = '0';
    return L === 'ru' ? s.replace('.', '{,}') : s;
}

/**
 * Area between y = f and y = g for v in [a, b] (∫|f − g|). a, b optional: then the outermost intersection
 * points are used. → {value: node | null, numeric, exact, approx, points: [nodes], pieces, steps, tex}.
 */
export function areaBetween(f, g, v = 'x', a = null, b = null, opts = {}) {
    f = asNode(f);
    g = asNode(g);
    const d = simp(add(f, neg(g)));
    const dc = compile(d, [v]);
    let lo;
    let hi;
    const cross = [];
    const P = Poly.fromNode(d, v);
    const exactRoots = P && P.degree >= 1 ? P.rationalRoots().map((r) => r.root) : null;
    if (a === null || b === null) {
        let roots;
        if (P && exactRoots && exactRoots.length >= 2) roots = exactRoots.map((r) => ({ node: num(r), x: r.toNumber() }));
        else roots = numFindRoots(dc, -50, 50).filter((r) => r.kind !== 'interval').map((r) => ({ node: exactPoint(r.x) ?? num(Q.of(r.x.toFixed(10))), x: r.x }));
        if (roots.length < 2) throw new MathError({ ru: 'Графики пересекаются меньше чем в двух точках — укажите границы', en: 'The graphs meet at fewer than two points: give the bounds' }, null, null, 'no-bounds');
        lo = roots[0];
        hi = roots[roots.length - 1];
    } else {
        lo = boundValue(boundNode(a));
        hi = boundValue(boundNode(b));
        if (lo.x > hi.x) [lo, hi] = [hi, lo];
    }
    for (const r of numFindRoots(dc, lo.x, hi.x)) {
        if (r.kind === 'interval' || r.x <= lo.x + 1e-9 || r.x >= hi.x - 1e-9) continue;
        const ex = exactRoots?.find((z) => Math.abs(z.toNumber() - r.x) < 1e-8);
        cross.push({ node: ex ? num(ex) : exactPoint(r.x) ?? num(Q.of(r.x.toFixed(12))), x: r.x });
    }
    const pts = [lo, ...cross, hi];
    const pieces = [];
    let total = null;
    let numeric = 0;
    let exact = true;
    const steps = [];
    for (let i = 0; i + 1 < pts.length; i++) {
        const p = pts[i];
        const r = pts[i + 1];
        const mid = dc((p.x + r.x) / 2);
        const upper = mid >= 0 ? d : simp(neg(d));
        const res = integrateDefinite(upper, v, p.node, r.node, { steps: false });
        pieces.push({ from: p.node, to: r.node, upper: mid >= 0 ? 'f' : 'g', value: res.value, numeric: res.numeric });
        if (!res.exact) exact = false;
        numeric += res.numeric ?? NaN;
        if (res.exact && total !== null) total = add(total, res.value);
        else if (res.exact && i === 0) total = res.value;
        else total = null;
    }
    const value = exact && total ? niceForm(total) : null;
    const tex = bt((L) => `S = \\int_{${tx(lo.node, L)}}^{${tx(hi.node, L)}} \\left|${tx(prettyForm(d), L)}\\right|\\,d${v} ${value ? '= ' + tx(value, L) : '\\approx ' + fmtNum(numeric, L)}`);
    if (opts.steps) {
        steps.push(step({
            title: T_('Разность функций', 'Difference of the functions'),
            tex: bt((L) => `f(${v}) - g(${v}) = ${tx(prettyForm(d), L)}`),
            text: T_('Площадь между графиками — интеграл от модуля разности: на каждом участке из верхней функции вычитаем нижнюю.', 'The area between the graphs is the integral of the absolute difference: on each piece subtract the lower function from the upper one.'),
            rule: 'difference',
        }));
        if (cross.length || a === null) {
            steps.push(step({
                title: T_('Точки пересечения', 'Intersection points'),
                tex: bt((L) => `${v} = ${pts.map((p) => tx(p.node, L)).join(L === 'ru' ? ';\\ ' : ',\\ ')}`),
                text: T_('Между точками пересечения разность сохраняет знак.', 'Between the intersection points the difference keeps its sign.'),
                rule: 'intersections',
            }));
        }
        for (const pc of pieces) {
            steps.push(step({
                title: T_('Участок', 'Piece'),
                tex: bt((L) => `\\int_{${tx(pc.from, L)}}^{${tx(pc.to, L)}} ${pc.upper === 'f' ? '(f - g)' : '(g - f)'}\\,d${v} = ${pc.value && typeof pc.value === 'object' ? tx(pc.value, L) : '\\approx ' + fmtNum(pc.numeric ?? NaN, L)}`),
                rule: 'piece',
            }));
        }
        steps.push(answerStep(T_('Площадь', 'Area'), tex));
    }
    return { value, numeric, exact: !!value, approx: !value, points: pts.map((p) => p.node), pieces, steps, tex };
}
