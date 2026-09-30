// integral/basic — constants and the table, linearity, a linear substitution f(kx + b), expanding, and the inner
// function's derivative as a factor (∫h′/h, ∫h′hᵏ).

import { containsVar, mul, sym, div, pow, add, isConst, fn, neg, num, nodeKey, nodeChildren, substitute } from '../../core/ast.js';
import { step } from '../../core/steps.js';
import { Poly } from '../../core/poly.js';
import { prettyForm, calcTex, quickDerivative } from '../derivative/index.js';
import { expand } from '../../core/expand.js';
import { splitCoeff } from '../../core/simplify.js';
import { Q } from '../../core/rational.js';
import { N1, N2, NM1, PI, coefTex, dTex, freshVar, iTex, isNum, isVar, isZero, linearParts, lnAbs, negLeading, q, simp, trySimp, tx } from './common.js';
import { I, sub } from './engine.js';
import { qn } from './rational.js';
import { msg, eachLanguage, notation } from '../../i18n/index.js';

// ---- constant and table

export function mConst(f, ctx) {
    const { v } = ctx;
    if (containsVar(f, v)) return null;
    const F = mul(f, sym(v));
    return {
        F,
        method: 'constant',
        step: step({
            title: msg('calculus.integral.basic.integral_of_constant'),
            tex: eachLanguage((L) => `${iTex(f, v, L)} = ${tx(simp(F), L)}`),
            text: msg('calculus.integral.basic.integrand_does_not_depend_on_c', { v }),
            rule: 'const',
        }),
    };
}

function quadIs(P, c0, c1, c2) {
    return P && P.degree === 2 && P.coeff(0).eq(c0) && P.coeff(1).eq(c1) && P.coeff(2).eq(c2);
}

// a law of the table in the reader's notation: {tan} is a function name (tg or tan), x the variable of integration
const lawIn = (tpl, v) => (lng) => tpl.replace(/x/g, v).replace(/\{(\w+)\}/g, (m, f) => notation(lng).fnText?.[f] ?? f);

function tableOf(f, v) {
    const X = sym(v);
    if (isVar(f, v)) return { F: div(pow(X, N2), N2), law: lawIn('∫x dx = x²/2 + C', v) };
    if (f.type === 'pow' && isVar(f.base, v) && !containsVar(f.exp, v)) {
        const e = f.exp;
        if (isNum(e) && e.value.eq(-1)) return { F: lnAbs(X, v), law: lawIn('∫dx/x = ln|x| + C', v) };
        const e1 = simp(add(e, N1));
        return {
            F: div(pow(X, e1), e1),
            law: lawIn('∫xⁿ dx = xⁿ⁺¹/(n + 1) + C (n ≠ −1)', v),
            note: !isNum(e),
        };
    }
    if (f.type === 'pow' && !containsVar(f.base, v) && isVar(f.exp, v)) {
        if (isConst(f.base) && f.base.name === 'e') return { F: f, law: lawIn('∫e^x dx = e^x + C', v) };
        return { F: div(f, fn('ln', f.base)), law: lawIn('∫a^x dx = a^x/ln a + C', v) };
    }
    if (f.type === 'fn' && f.args.length === 1 && isVar(f.args[0], v)) {
        const T = {
            sin: [neg(fn('cos', X)), '∫sin x dx = −cos x + C'],
            cos: [fn('sin', X), '∫cos x dx = sin x + C'],
            tan: [neg(lnAbs(fn('cos', X), v)), '∫{tan} x dx = −ln|cos x| + C'],
            cot: [lnAbs(fn('sin', X), v), '∫{cot} x dx = ln|sin x| + C'],
            sinh: [fn('cosh', X), '∫{sinh} x dx = {cosh} x + C'],
            cosh: [fn('sinh', X), '∫{cosh} x dx = {sinh} x + C'],
            tanh: [fn('ln', fn('cosh', X)), '∫{tanh} x dx = ln {cosh} x + C'],
            coth: [lnAbs(fn('sinh', X), v), '∫{coth} x dx = ln|{sinh} x| + C'],
            abs: [div(mul(X, fn('abs', X)), N2), '∫|x| dx = x|x|/2 + C'],
            sign: [fn('abs', X), '∫sgn x dx = |x| + C'],
            sec: [lnAbs(add(fn('sec', X), fn('tan', X)), v), '∫sec x dx = ln|sec x + {tan} x| + C'],
            csc: [lnAbs(fn('tan', div(X, N2)), v), '∫{csc} x dx = ln|{tan}(x/2)| + C'],
        }[f.name];
        if (!T) return null;
        return { F: T[0], law: lawIn(T[1], v) };
    }
    if (f.type === 'pow' && isNum(f.exp) && f.base.type === 'fn' && f.base.args.length === 1 && isVar(f.base.args[0], v)) {
        const e = f.exp.value;
        const nm = f.base.name;
        const hit = (name, k) => nm === name && e.eq(k);
        if (hit('cos', -2) || hit('sec', 2)) return { F: fn('tan', X), law: lawIn('∫dx/cos² x = {tan} x + C', v) };
        if (hit('sin', -2) || hit('csc', 2)) return { F: neg(fn('cot', X)), law: lawIn('∫dx/sin² x = −{cot} x + C', v) };
        if (hit('cosh', -2)) return { F: fn('tanh', X), law: lawIn('∫dx/{cosh}² x = {tanh} x + C', v) };
        if (hit('sinh', -2)) return { F: neg(fn('coth', X)), law: lawIn('∫dx/{sinh}² x = −{coth} x + C', v) };
        if (hit('cos', -1))
            return {
                F: lnAbs(fn('tan', add(div(X, N2), div(PI, num(4)))), v),
                law: lawIn('∫dx/cos x = ln|{tan}(x/2 + π/4)| + C', v),
            };
        if (hit('sin', -1)) return { F: lnAbs(fn('tan', div(X, N2)), v), law: lawIn('∫dx/sin x = ln|{tan}(x/2)| + C', v) };
        return null;
    }
    if (f.type === 'pow' && isNum(f.exp) && f.base.type === 'add') {
        const P = Poly.fromNode(f.base, v);
        const e = f.exp.value;
        if (e.eq(-1) && quadIs(P, 1, 0, 1)) return { F: fn('atan', X), law: lawIn('∫dx/(1 + x²) = {atan} x + C', v) };
        if (e.eq(q(-1, 2)) && quadIs(P, 1, 0, -1)) return { F: fn('asin', X), law: lawIn('∫dx/√(1 − x²) = {asin} x + C', v) };
        if (e.eq(q(-1, 2)) && quadIs(P, 1, 0, 1))
            return {
                F: fn('ln', add(X, fn('sqrt', add(pow(X, N2), N1)))),
                law: lawIn('∫dx/√(x² + 1) = ln(x + √(x² + 1)) + C', v),
            };
        if (e.eq(q(-1, 2)) && quadIs(P, -1, 0, 1))
            return {
                F: lnAbs(add(X, fn('sqrt', add(pow(X, N2), NM1))), v),
                law: lawIn('∫dx/√(x² − 1) = ln|x + √(x² − 1)| + C', v),
            };
    }
    return null;
}

export function mTable(f, ctx) {
    const { v } = ctx;
    const t = tableOf(f, v);
    if (!t) return null;
    const F = t.F;
    return {
        F,
        method: 'table',
        step: step({
            title: msg('calculus.integral.basic.table_integral'),
            tex: eachLanguage((L) => `${iTex(f, v, L)} = ${tx(trySimp(F) ?? F, L)}`),
            text: t.note
                ? msg('calculus.integral.basic.from_table_for_exponent_other_than', { p: t.law })
                : msg('calculus.integral.basic.from_table_of_integrals', { p: t.law }),
            rule: 'table',
        }),
    };
}

// ---- linearity

export function mLinearity(f, ctx) {
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
                title: msg('calculus.integral.basic.constant_factor'),
                tex: eachLanguage((L) => `${iTex(f, v, L)} = ${coefTex(c, L)}${iTex(g, v, L)} = ${tx(simp(F), L)}`),
                text: msg('calculus.integral.basic.constant_factor_comes_out_of_integral'),
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
                title: msg('calculus.integral.basic.integral_of_sum'),
                tex: eachLanguage(
                    (L) =>
                        `${iTex(f, v, L)} = ${parts
                            .map((p, i) => {
                                if (negLeading(p.t)) return (i === 0 ? '-' : ' - ') + iTex(simp(neg(p.t)), v, L);
                                const s = iTex(p.t, v, L);
                                return i === 0 ? s : ' + ' + s;
                            })
                            .join('')} = ${tx(simp(F), L)}`,
                ),
                text: msg('calculus.integral.basic.integral_of_sum_is_sum_of'),
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
export function mapPre(n, fnc) {
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

export function mLinearSub(f, ctx) {
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
                title: msg('calculus.integral.basic.linear_substitution'),
                tex: eachLanguage(
                    (L) =>
                        `${iTex(f, v, L)} = \\left[${t} = ${tx(Lx, L)},\\ d${t} = ${dTex(k, v, L)}\\right] = ${coefTex(simp(div(N1, k)), L)}${iTex(g, t, L)} = ${tx(simp(F), L)}`,
                ),
                text: msg('calculus.integral.basic.function_is_applied_to_linear_expression', { Lx: (lng) => plainish(Lx, lng) }),
                rule: 'linear-substitution',
                sub: [r.step],
            }),
        };
    }
    return null;
}

export function plainish(n, L) {
    return toTextSafe(prettyForm(n), L);
}

function toTextSafe(n, L) {
    try {
        let s = calcTex(n, L);
        s = s
            .replace(/\\left|\\right/g, '')
            .replace(/\\operatorname\{(\w+)\}/g, '$1')
            .replace(/\\cdot/g, '·')
            .replace(/\\,/g, ' ');
        s = s
            .replace(/\\frac\{([^{}]*)\}\{([^{}]*)\}/g, '($1)/($2)')
            .replace(/\\sqrt\{([^{}]*)\}/g, '√($1)')
            .replace(/\^\{(-?\d+)\}/g, (m, d) => supDigits(d))
            .replace(/\\([a-z]+)/g, '$1');
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
    if (f.type === 'mul')
        return f.args.some(
            (a) => a.type === 'add' || (a.type === 'pow' && a.base.type === 'add' && isNum(a.exp) && a.exp.value.isInt() && a.exp.value.isPos()),
        );
    return false;
}

export function mExpand(f, ctx) {
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
            title: msg('calculus.integral.basic.expand'),
            tex: eachLanguage((L) => `${iTex(f, v, L)} = ${iTex(X, v, L)}`),
            text: msg('calculus.integral.basic.multiplying_out_gives_sum_of_simple'),
            rule: 'expand',
            sub: [r.step],
        }),
    };
}

// ---- f = c·h′·hᵏ: the inner function's derivative is a factor (∫h′/h = ln|h|, ∫h′hᵏ = hᵏ⁺¹/(k + 1))

export function mDerivPattern(f, ctx) {
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
            ? msg('calculus.integral.basic.numerator_is_up_to_factor_derivative', { h: (lng) => plainish(h, lng) })
            : msg('calculus.integral.basic.derivative_of_h_is_up_to', { h: (lng) => plainish(h, lng) });
        return {
            F,
            method: 'substitution',
            step: step({
                title: k.eq(-1) ? msg('calculus.integral.basic.derivative_of_denominator_on_top') : msg('calculus.integral.basic.inner_derivative_is_factor'),
                tex: eachLanguage((L) => `${iTex(f, v, L)} = \\left[t = ${tx(h, L)},\\ dt = ${dTex(dh, v, L)}\\right] = ${tx(trySimp(F) ?? F, L)}`),
                text: law,
                rule: 'substitution',
            }),
        };
    }
    return null;
}
