// integral/parts — integration by parts (LIATE, repeated, cyclic) and the tabular way for P(x)·e^{kx}, P(x)·sin kx.

import { Poly } from '../../core/poly.js';
import { containsVar, mul, num, add, neg, sym, fn, pow } from '../../core/ast.js';
import { splitCoeff } from '../../core/simplify.js';
import { MathError } from '../../core/rational.js';
import { quickDerivative } from '../derivative/index.js';
import { step } from '../../core/steps.js';
import { plainish } from './basic.js';
import { N0, checkAnti, iTex, isNum, isOne, isVar, isZero, linearParts, simp, trySimp, tx } from './common.js';
import { I, sub } from './engine.js';
import { cleanAnti } from './integrate.js';
import { msg, eachLanguage } from '../../i18n/index.js';

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
    L: msg('calculus.integral.parts.logarithm_turns_into_fraction_when_differentiated'),
    I: msg('calculus.integral.parts.inverse_trigonometric_function_becomes_algebraic_when'),
    A: msg('calculus.integral.parts.polynomial_loses_degree_when_differentiated'),
};

export function mParts(f, ctx) {
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
            title: msg('calculus.integral.parts.integration_by_parts'),
            tex: eachLanguage((L) => `\\left[u = ${tx(u, L)},\\ dv = ${dvT(L)};\\ du = ${isOne(du) ? '' : tx(du, L) + '\\,'}d${v},\\ v = ${tx(Vs, L)}\\right],\\quad ${iTex(f, v, L)} = ${tx(simp(mul(u, Vs)), L)} - ${iTex(inner, v, L)} = ${tx(trySimp(F) ?? F, L)}`),
            text: msg('calculus.integral.parts.formula_u_dv_uv_v_du', { u: (lng) => plainish(u, lng), p: why ?? msg('calculus.integral.parts.this_makes_integral_simpler'), Vs: (lng) => plainish(Vs, lng) }),
            rule: 'parts',
            sub: [rv.step, rj.step].filter(Boolean),
        }),
    };
}

// ---- P(x)·e^{kx+b}, P(x)·sin/cos(kx+b) of any degree: integration by parts n times (the tabular way)

export function mPolyTimes(f, ctx) {
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
            title: msg('calculus.integral.parts.by_parts_times', { degree: P.degree }),
            tex: eachLanguage((L) => `${iTex(f, v, L)} = ${tx(trySimp(F) ?? F, L)}`),
            text: msg('calculus.integral.parts.integrate_by_parts_times_each_time', { degree: P.degree }),
            rule: 'parts-tabular',
        }),
    };
}
