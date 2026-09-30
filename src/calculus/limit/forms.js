// limit/forms — indeterminate forms: rational functions, equivalents, the conjugate, leading terms, L'Hôpital,
// dividing by the fastest-growing term, splitting a fraction, ∞ − ∞, 0·∞ and powers.

import { ratFunctionOf, niceForm, quickDerivative } from '../derivative/index.js';
import { nodeKey, num, sym, div, mul, pow, add, neg, fn, containsVar, isConst, substitute } from '../../core/ast.js';
import { step } from '../../core/steps.js';
import { expand } from '../../core/expand.js';
import { combineFractions } from '../../core/fractions.js';
import { Poly } from '../../core/poly.js';
import { toText } from '../../core/print.js';
import { splitCoeff } from '../../core/simplify.js';
import { Q } from '../../core/rational.js';
import { chainEq, fin, infV, isZeroV, limTex, lt, negLeadNode, paren2, splitNumDen, asym } from './common.js';
import { msg, eachLanguage, notation, joined, sameText, DEFAULT_LANGUAGE } from '../../i18n/index.js';
import { calcTex, prettyForm, isNum, paren, simp, trySimp, N0, N1, NM1, N2, HALF, E_, isZero } from '../display.js';

// ---------------------------------------------------------------- indeterminate forms

// the evaluator comes with the context (it calls resolve(), so this module cannot import it)
const ev = (n, C) => C.ev(n, C);

export const FORM_TEX = {
    '0/0': '\\frac{0}{0}',
    'inf/inf': '\\frac{\\infty}{\\infty}',
    'inf-inf': '\\infty - \\infty',
    '0*inf': '0 \\cdot \\infty',
    '1^inf': '1^{\\infty}',
    '0^0': '0^{0}',
    'inf^0': '\\infty^{0}',
};
export const FORM_NAME = { '0/0': '0/0', 'inf/inf': '∞/∞', 'inf-inf': '∞ − ∞', '0*inf': '0·∞', '1^inf': '1^∞', '0^0': '0⁰', 'inf^0': '∞⁰' };

function vTex(L, Lg) {
    if (!L) return '?';
    if (L.k === 'fin') return calcTex(prettyForm(L.node), Lg);
    if (L.k === 'inf') return L.s > 0 ? '+\\infty' : '-\\infty';
    return msg('calculus.limit.forms.does_not_exist').in(Lg);
}

export function resolve(n, C, form) {
    if (C.depth > 8) return null;
    const key = nodeKey(n) + '|' + form;
    if (C.active.has(key)) return null;
    C.active.add(key);
    const C2 = { ...C, depth: C.depth + 1, log: [] };
    let res = null;
    try {
        for (const m of METHODS[form] ?? []) {
            C2.log = [];
            const r = m(n, C2, form);
            if (r && r.val) {
                res = r;
                break;
            }
        }
    } finally {
        C.active.delete(key);
    }
    if (!res) return null;
    C.log.push(
        step({
            title: res.title,
            tex: res.tex,
            text: res.text,
            rule: res.rule,
            sub: [...(res.sub ?? []), ...C2.log],
        }),
    );
    C.methods.add(res.rule);
    return res.val;
}

function limSub(n, C) {
    // the limit of a transformed expression; its own steps go into C.log
    return ev(n, C);
}

// ---- rational functions

function mRational(n, C, form) {
    const { v, P } = C;
    const r = ratFunctionOf(n, v);
    if (!r) return null;
    if (!Number.isFinite(P.x)) {
        // degree comparison
        const p = r.num;
        const q = r.den;
        const dp = p.degree;
        const dq = q.degree;
        let val;
        if (dp < dq) val = fin(N0);
        else if (dp === dq) val = fin(num(p.lead.div(q.lead)));
        else {
            let s = Math.sign(p.lead.div(q.lead).toNumber());
            if (P.x < 0 && (dp - dq) % 2 === 1) s = -s;
            val = infV(s);
        }
        const k = Math.max(dq, dp > dq ? dq : dp);
        const X = sym(v);
        if (dq === 0 && dp >= 1) {
            // a polynomial: the leading term decides — take x^deg out of the brackets
            const inner = simp(expand(div(p.toNode(v), mul(num(q.lead), pow(X, num(dp))))));
            const lead = simp(mul(num(p.lead.div(q.lead)), pow(X, num(dp))));
            return {
                val,
                title: msg('calculus.limit.forms.take_out_highest_power'),
                tex: eachLanguage((L) =>
                    `${limTex(P, v, L)} ${lt(n, L)} = ${limTex(P, v, L)} ${dp === 1 && p.lead.div(q.lead).isOne() ? calcTex(X, L) : lt(lead, L)}${inner.type === 'add' ? paren(calcTex(inner, L)) : ''} = ${vTex(val, L)}`.replace(
                        /\\cdot\s*$/,
                        '',
                    ),
                ),
                text: msg('calculus.limit.forms.as_polynomial_behaves_like_its_leading', { v, p: P.x > 0 ? '+∞' : '−∞', dp: supd(dp) }),
                rule: 'leading-power',
            };
        }
        return {
            val,
            title: form === 'inf-inf' ? msg('calculus.limit.forms.common_denominator') : msg('calculus.limit.forms.divide_by_highest_power'),
            tex: eachLanguage((L) =>
                chainEq([
                    `${limTex(P, v, L)} ${lt(n, L)}`,
                    `${limTex(P, v, L)} ${lt(q.degree > 0 ? div(p.toNode(v), q.toNode(v)) : p.toNode(v), L)}`,
                    k > 0 ? `${limTex(P, v, L)} \\frac{${calcTex(dividedBy(p, k, v), L)}}{${calcTex(dividedBy(q, k, v), L)}}` : null,
                    vTex(val, L),
                ]),
            ),
            text:
                dp < dq
                    ? msg('calculus.limit.forms.numerator_s_degree_is_less_than', { dp, dq, v, k: supd(k) })
                    : dp === dq
                      ? msg('calculus.limit.forms.degrees_are_equal_divide_both_by', { dp, v, k: supd(k) })
                      : msg('calculus.limit.forms.numerator_s_degree_exceeds_denominator_s', { dp, dq }),
            rule: 'rational-infinity',
        };
    }
    // finite point: factor and cancel
    const nd = combineFractionsSafe(n);
    const Pn = nd ? Poly.fromNode(nd.num, v) : null;
    const Pd = nd ? Poly.fromNode(nd.den, v) : null;
    const reduced = r.den.degree < 1 ? simp(div(r.num.toNode(v), r.den.toNode(v))) : div(r.num.toNode(v), r.den.toNode(v));
    const L = ev(simp(reduced), { ...C, depth: C.depth + 1 });
    if (!L) return null;
    const showFactor = Pn && Pd && Pd.degree >= 1;
    const fN = showFactor ? factorTex(Pn, v) : null;
    const fD = showFactor ? factorTex(Pd, v) : null;
    return {
        val: L,
        title: msg('calculus.limit.forms.factor_and_cancel'),
        tex: eachLanguage(
            (Lg) =>
                `${limTex(P, v, Lg)} ${lt(n, Lg)}${showFactor ? ` = ${limTex(P, v, Lg)} \\frac{${fN(Lg)}}{${fD(Lg)}}` : ''} = ${limTex(P, v, Lg)} ${lt(reduced, Lg)} = ${vTex(L, Lg)}`,
        ),
        text: msg('calculus.limit.forms.both_numerator_and_denominator_vanish_at', { v, P: (lng) => plainNum(P, lng) }),
        rule: 'factor-cancel',
    };
}

/** P(x)/x^k written from the highest power down, unsimplified: 1 − 4/x + 6/x² … */
function dividedBy(Pl, k, v) {
    const X = sym(v);
    const terms = [];
    for (let i = Pl.degree; i >= 0; i--) {
        const c = Pl.coeff(i);
        if (c.isZero()) continue;
        const e = i - k;
        const pw = e === 0 ? null : e === 1 ? X : pow(X, num(e));
        if (!pw) terms.push(num(c));
        else if (c.isOne()) terms.push(pw);
        else terms.push(mul(num(c), pw));
    }
    if (!terms.length) return N0;
    return terms.length === 1 ? terms[0] : add(terms);
}

function supd(k) {
    const S = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹' };
    return k === 1
        ? ''
        : String(k)
              .split('')
              .map((c) => S[c])
              .join('');
}

/** The point a as readable text in a language (π, √, ·), for the explanations. */
export function plainNum(P, lang = DEFAULT_LANGUAGE) {
    try {
        return toText(prettyForm(P.a), { lang })
            .replace(/\bpi\b/g, 'π')
            .replace(/sqrt\(/g, '√(')
            .replace(/\*/g, '·');
    } catch {
        return String(P.x);
    }
}

function combineFractionsSafe(n) {
    try {
        const c = combineFractions(n, { cancel: false });
        return c.type === 'div' ? { num: c.num, den: c.den } : { num: c, den: N1 };
    } catch {
        return null;
    }
}

function factorTex(Pl, v) {
    const { constant, factors } = Pl.factor();
    const fs = [];
    if (!constant.isOne()) fs.push(num(constant));
    for (const { poly, mult } of factors) fs.push(mult === 1 ? poly.toNode(v) : pow(poly.toNode(v), num(mult)));
    const node = fs.length === 0 ? num(constant) : fs.length === 1 ? fs[0] : mul(fs);
    return (L) => calcTex(node, L);
}

// ---- equivalent infinitesimals

const EQUIV_FN = new Set(['sin', 'tan', 'asin', 'atan', 'sinh', 'tanh', 'asinh', 'atanh']);
// a function's name in a language's notation (tg or tan), for the equivalence laws
const fnName = (name, lang) => notation(lang).fnText?.[name] ?? name;

function tendsTo(n, target, C) {
    const L = ev(n, { ...C, log: [], depth: C.depth + 1 });
    if (!L || L.k !== 'fin') return false;
    const d = trySimp(add(L.node, neg(target)));
    return d !== null && isZero(d);
}

/** Equivalent of an infinitesimal factor F: {E, law} (the law as text per language) or null. */
function equivalentOf(F, C) {
    if (F.type === 'fn' && EQUIV_FN.has(F.name) && tendsTo(F.args[0], N0, C)) {
        return { E: F.args[0], law: eachLanguage((l) => `${fnName(F.name, l)} u ~ u`) };
    }
    if (F.type === 'fn' && (F.name === 'ln' || F.name === 'lg') && tendsTo(F.args[0], N1, C)) {
        const E = add(F.args[0], NM1);
        return F.name === 'ln'
            ? { E, law: 'ln(1 + u) ~ u' }
            : { E: div(E, fn('ln', num(10))), law: eachLanguage((l) => `${notation(l).log10Text}(1 + u) ~ u/ln 10`) };
    }
    if (F.type === 'fn' && F.name === 'log' && tendsTo(F.args[1], N1, C))
        return { E: div(add(F.args[1], NM1), fn('ln', F.args[0])), law: 'logₐ(1 + u) ~ u/ln a' };
    if (F.type === 'add' && F.args.length === 2) {
        const kIdx = F.args.findIndex((t) => isNum(t));
        if (kIdx < 0) return null;
        const k = F.args[kIdx].value;
        const t1 = F.args[1 - kIdx];
        // F = t1 + k = −k·(Y − 1) with Y = t1/(−k)
        const Y = trySimp(div(t1, num(k.neg())));
        if (!Y) return null;
        const outer = num(k.neg());
        const wrap = (E, law) => ({ E: k.eq(-1) ? E : mul(outer, E), law });
        if (Y.type === 'pow' && !containsVar(Y.base, C.v) && tendsTo(Y.exp, N0, C)) {
            const isE = isConst(Y.base) && Y.base.name === 'e';
            return wrap(isE ? Y.exp : mul(Y.exp, fn('ln', Y.base)), isE ? 'eᵘ − 1 ~ u' : 'aᵘ − 1 ~ u·ln a');
        }
        if (Y.type === 'fn' && Y.name === 'cos' && tendsTo(Y.args[0], N0, C)) {
            return wrap(neg(div(pow(Y.args[0], N2), N2)), '1 − cos u ~ u²/2');
        }
        if (Y.type === 'pow' && isNum(Y.exp) && tendsTo(Y.base, N1, C)) {
            return wrap(mul(Y.exp, add(Y.base, NM1)), '(1 + u)ᵃ − 1 ~ a·u');
        }
        if (Y.type === 'fn' && Y.name === 'cosh' && tendsTo(Y.args[0], N0, C)) {
            return wrap(
                div(pow(Y.args[0], N2), N2),
                eachLanguage((l) => `${fnName('cosh', l)} u − 1 ~ u²/2`),
            );
        }
    }
    return null;
}

function mEquivalents(n, C) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S) return null;
    const { coef, rest } = splitCoeff(S);
    if (!rest) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    const used = [];
    const out = [num(coef)];
    let changed = false;
    for (const f of fs) {
        const base = f.type === 'pow' && isNum(f.exp) ? f.base : f;
        const e = f.type === 'pow' && isNum(f.exp) ? f.exp : null;
        if (!containsVar(base, v)) {
            out.push(f);
            continue;
        }
        const eq = tendsTo(base, N0, C) ? equivalentOf(base, C) : null;
        if (!eq) {
            out.push(f);
            continue;
        }
        changed = true;
        used.push({ from: base, to: trySimp(eq.E) ?? eq.E, law: eq.law });
        out.push(e ? pow(eq.E, e) : eq.E);
    }
    if (!changed) return null;
    const next = trySimp(mul(out));
    if (!next) return null;
    const C2 = { ...C, depth: C.depth + 1 };
    const L = limSub(next, C2);
    if (!L) return null;
    const laws = used.map((u) => u.law).filter((x, i, all) => all.findIndex((y) => sameText(x, y)) === i);
    return {
        val: L,
        title: msg('calculus.limit.forms.equivalent_infinitesimals'),
        tex: eachLanguage(
            (Lg) =>
                `${used.map((u) => `${calcTex(u.from, Lg)} \\sim ${calcTex(u.to, Lg)}`).join(',\\quad ')};\\qquad ${limTex(P, v, Lg)} ${lt(n, Lg)} = ${containsVar(next, v) ? `${limTex(P, v, Lg)} ${paren2(calcTex(next, Lg), next)} = ` : ''}${vTex(L, Lg)}`,
        ),
        text: msg('calculus.limit.forms.replace_infinitesimal_factors_by_equivalent_ones', { laws: joined(laws, '; ') }),
        rule: 'equivalents',
    };
}

// ---- conjugate

function rootDeg(t) {
    const { rest } = splitCoeff(t);
    const b = rest ?? t;
    if (b.type === 'pow' && isNum(b.exp) && b.exp.value.n === 1n && (b.exp.value.d === 2n || b.exp.value.d === 3n)) return Number(b.exp.value.d);
    return 0;
}
const isRoot = (t) => rootDeg(t) > 0;

function mConjugate(n, C) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S) return null;
    // find a two-term sum with a square root: the whole expression or a factor (possibly in the denominator)
    const fs = S.type === 'mul' ? S.args : [S];
    for (let i = 0; i < fs.length; i++) {
        const f = fs[i];
        const base = f.type === 'pow' && isNum(f.exp) && f.exp.value.isInt() ? f.base : f;
        const e = base === f ? Q.ONE : f.exp.value;
        if (base.type !== 'add' || base.args.length !== 2 || !base.args.some(isRoot)) continue;
        if (!e.abs().isOne()) continue;
        const [A, B] = base.args;
        const cube = base.args.some((t) => rootDeg(t) === 3);
        // a + b = (a² − b²)/(a − b);  for cube roots a + b = (a³ + b³)/(a² − ab + b²)
        const conj0 = cube ? add(pow(A, N2), neg(mul(A, B)), pow(B, N2)) : add(A, neg(B));
        const conj = trySimp(conj0) ?? conj0;
        const numer = trySimp(expand(cube ? add(pow(A, num(3)), pow(B, num(3))) : add(pow(A, N2), neg(pow(B, N2)))));
        if (!numer) continue;
        const replaced = e.isOne() ? div(numer, conj) : div(conj, numer);
        const next = trySimp(mul([...fs.slice(0, i), replaced, ...fs.slice(i + 1)]));
        if (!next) continue;
        const L = limSub(next, { ...C, depth: C.depth + 1 });
        if (!L) continue;
        return {
            val: L,
            title: msg('calculus.limit.forms.multiply_by_conjugate'),
            tex: eachLanguage(
                (Lg) =>
                    `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} \\frac{${paren(calcTex(base, Lg))}${paren(calcTex(conj, Lg))}}{${calcTex(conj, Lg)}}${e.isOne() ? '' : '^{-1}'} = ${limTex(P, v, Lg)} ${lt(next, Lg)} = ${vTex(L, Lg)}`,
            ),
            text: cube
                ? msg('calculus.limit.forms.difference_of_cube_roots_is_indeterminate')
                : msg('calculus.limit.forms.difference_with_root_is_indeterminate_multiply'),
            rule: 'conjugate',
        };
    }
    return null;
}

// ---- leading terms at ±∞ (algebraic expressions)

function mLeading(n, C) {
    const { v, P } = C;
    if (Number.isFinite(P.x)) return null;
    const S = trySimp(n);
    if (!S) return null;
    const flip = P.x < 0;
    const work = flip ? trySimp(substitute(S, { [v]: neg(sym(v)) })) : S;
    if (!work) return null;
    const { top, bot } = splitNumDen(work);
    const u = top.length ? mul(top) : N1;
    const w = bot.length ? mul(bot) : N1;
    const au = asym(simp(u), v);
    const aw = asym(simp(w), v);
    if (!au || !aw) return null;
    const p = au.p.sub(aw.p);
    const c = au.c / aw.c;
    let val;
    if (p.isNeg()) val = fin(N0);
    else if (p.isZero()) {
        const exact = exactFromFloat(c);
        if (!exact) return null;
        val = fin(exact);
    } else val = infV(Math.sign(c));
    const k = aw.p;
    return {
        val,
        title: msg('calculus.limit.forms.divide_by_highest_power'),
        tex: eachLanguage((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${vTex(val, Lg)}`),
        text: msg('calculus.limit.forms.as_each_sum_is_dominated_by', {
            v,
            p: flip ? '−∞' : '+∞',
            p2: k.isOne() ? '' : '^' + k.toString(),
            p3: (lng) =>
                flip
                    ? msg('calculus.limit.forms.for_negative').in(lng) +
                      v +
                      msg('calculus.limit.forms.formula').in(lng) +
                      v +
                      msg('calculus.limit.forms.formula_2').in(lng) +
                      v +
                      ')'
                    : '',
        }),
        rule: 'leading-terms',
    };
}

function exactFromFloat(c) {
    if (!Number.isFinite(c)) return null;
    for (const d of [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 25, 100]) {
        const k = Math.round(c * d);
        if (Math.abs(k / d - c) < 1e-10 * Math.max(1, Math.abs(c))) return num(new Q(BigInt(k), BigInt(d)));
    }
    // c = r·√m
    for (const m of [2, 3, 5, 6, 7, 10]) {
        for (const d of [1, 2, 3, 4, 5, 6, 10]) {
            const k = Math.round((c * d) / Math.sqrt(m));
            if (k && Math.abs((k * Math.sqrt(m)) / d - c) < 1e-10 * Math.max(1, Math.abs(c)))
                return simp(mul(num(new Q(BigInt(k), BigInt(d))), pow(num(m), HALF)));
        }
    }
    return null;
}

// ---- L'Hôpital

export function quotientParts(n, v) {
    if (n.type === 'div') return { u: n.num, w: n.den };
    const S = trySimp(n);
    if (!S) return null;
    const { top, bot } = splitNumDen(S);
    if (!bot.length) return null;
    return { u: top.length ? mul(top) : N1, w: bot.length === 1 ? bot[0] : mul(bot) };
}

function mLHopital(n, C, form) {
    const { v, P } = C;
    if ((C.rounds ?? 0) >= 5) return null;
    const qp = quotientParts(n, v);
    if (!qp) return null;
    let du;
    let dw;
    try {
        du = niceForm(quickDerivative(qp.u, v), v);
        dw = niceForm(quickDerivative(qp.w, v), v);
    } catch {
        return null;
    }
    if (isZero(trySimp(dw) ?? dw)) return null;
    const uS = niceForm(qp.u, v);
    const wS = niceForm(qp.w, v);
    const next = div(du, dw);
    const nextS = simp(next);
    const tidy = niceForm(nextS, v);
    const L = limSub(nextS, { ...C, depth: C.depth + 1, rounds: (C.rounds ?? 0) + 1 });
    // the rule says nothing when the ratio of the derivatives has no limit ((x + sin x)/x at ∞)
    if (!L || L.k === 'dne' || L.k === 'bnd') return null;
    return {
        val: L,
        title: msg('calculus.limit.forms.l_h_pital_s_rule'),
        tex: eachLanguage(
            (Lg) =>
                `${limTex(P, v, Lg)} \\frac{${calcTex(uS, Lg)}}{${calcTex(wS, Lg)}} = ${limTex(P, v, Lg)} \\frac{${paren(calcTex(uS, Lg))}'}{${paren(calcTex(wS, Lg))}'} = ${limTex(P, v, Lg)} ${lt(next, Lg)}${calcTex(tidy, Lg) !== calcTex(next, Lg) ? ` = ${limTex(P, v, Lg)} ${paren2(calcTex(tidy, Lg), tidy)}` : ''} = ${vTex(L, Lg)}`,
        ),
        text: msg('calculus.limit.forms.form_numerator_and_denominator_are_differentiable', { p: FORM_NAME[form] }),
        rule: 'lhopital',
    };
}

// ---- ∞/∞: divide the numerator and the denominator by the fastest-growing term

function mDivideDominant(n, C) {
    const { v, P } = C;
    const qp = quotientParts(n, v);
    if (!qp) return null;
    const pool = [...(qp.w.type === 'add' ? qp.w.args : [qp.w]), ...(qp.u.type === 'add' ? qp.u.args : [qp.u])];
    for (const T of pool) {
        const TL = ev(T, { ...C, log: [], depth: C.depth + 1 });
        if (!TL || TL.k !== 'inf') continue;
        let a;
        let b;
        try {
            a = simp(expand(div(qp.u, T)));
            b = simp(expand(div(qp.w, T)));
        } catch {
            continue;
        }
        const C2 = { ...C, depth: C.depth + 1, log: [] };
        const A = ev(a, C2);
        const B = ev(b, C2);
        if (!A || !B || A.k === 'dne' || B.k === 'dne' || A.k === 'bnd' || B.k === 'bnd') continue;
        let val = null;
        if (A.k === 'fin' && B.k === 'fin' && !isZeroV(B)) val = fin(div(A.node, B.node));
        else if (A.k === 'fin' && B.k === 'inf') val = fin(N0);
        else if (A.k === 'inf' && B.k === 'fin' && !isZeroV(B) && Number.isFinite(B.x)) val = infV(A.s * Math.sign(B.x));
        if (!val) continue;
        return {
            val,
            title: msg('calculus.limit.forms.divide_by_dominant_term'),
            tex: eachLanguage((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} \\frac{${calcTex(a, Lg)}}{${calcTex(b, Lg)}} = ${vTex(val, Lg)}`),
            text: msg('calculus.limit.forms.divide_numerator_and_denominator_by_fastest', { term: (lng) => toText(prettyForm(T), { lang: lng }) }),
            rule: 'divide-dominant',
            sub: C2.log,
        };
    }
    return null;
}

// ---- split the fraction into a sum ((x + sin x)/x = 1 + sin x/x)

function mSplitFraction(n, C) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'mul' || !S.args.some((f) => f.type === 'add')) return null;
    let X;
    try {
        X = simp(expand(S));
    } catch {
        return null;
    }
    if (X.type !== 'add' || X.args.length > 8 || nodeKey(X) === nodeKey(S)) return null;
    const L = limSub(X, { ...C, depth: C.depth + 1 });
    if (!L) return null;
    return {
        val: L,
        title: msg('calculus.limit.forms.divide_term_by_term'),
        tex: eachLanguage((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} ${paren(calcTex(X, Lg))} = ${vTex(L, Lg)}`),
        text: msg('calculus.limit.forms.divide_each_term_of_numerator_by'),
        rule: 'split-fraction',
    };
}

// ---- ∞ − ∞, 0·∞, powers

function mCommonDen(n, C) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'add') return null;
    let cf;
    try {
        cf = combineFractions(S);
    } catch {
        return null;
    }
    if (cf.type !== 'div') return null;
    const L = limSub(simp(cf), { ...C, depth: C.depth + 1 });
    if (!L) return null;
    return {
        val: L,
        title: msg('calculus.limit.forms.bring_to_common_denominator'),
        tex: eachLanguage((Lg) => `${limTex(P, v, Lg)} ${paren(calcTex(n, Lg))} = ${limTex(P, v, Lg)} ${lt(cf, Lg)} = ${vTex(L, Lg)}`),
        text: msg('calculus.limit.forms.form_combine_fractions_into_one_which'),
        rule: 'common-denominator',
    };
}

function mDominant(n, C) {
    // ∞ − ∞ for a sum: take out the fastest-growing term T: n = T·(1 + Σ others/T)
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'add') return null;
    for (const T of S.args) {
        const TL = ev(T, { ...C, log: [], depth: C.depth + 1 });
        if (!TL || TL.k !== 'inf') continue;
        const rest = trySimp(div(add(S.args.filter((t) => t !== T)), T));
        if (!rest) continue;
        const C2 = { ...C, depth: C.depth + 1, log: [] };
        const R = ev(rest, C2);
        if (!R || R.k !== 'fin') continue;
        const f = R.x + 1;
        if (!Number.isFinite(f) || Math.abs(f) < 1e-12) continue;
        const val = infV(TL.s * Math.sign(f));
        return {
            val,
            title: msg('calculus.limit.forms.take_out_dominant_term'),
            tex: eachLanguage(
                (Lg) =>
                    `${limTex(P, v, Lg)} ${paren(calcTex(n, Lg))} = ${limTex(P, v, Lg)} ${T.type === 'add' || T.type === 'mul' ? paren(calcTex(T, Lg)) : calcTex(T, Lg)}\\left(${calcTex(add(N1, rest), Lg)}\\right) = ${vTex(val, Lg)}`,
            ),
            text: msg('calculus.limit.forms.take_out_fastest_growing_term_bracket'),
            rule: 'dominant-term',
            sub: C2.log,
        };
    }
    return null;
}

function mZeroInf(n, C) {
    // u·w with u → 0, w → ∞: write as u / (1/w) or w / (1/u) (logarithms stay on top)
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'mul') return null;
    const zeros = [];
    const infs = [];
    const rest = [];
    for (const f of S.args) {
        const L = ev(f, { ...C, log: [], depth: C.depth + 1 });
        if (L && L.k === 'inf') infs.push(f);
        else if (isZeroV(L)) zeros.push(f);
        else rest.push(f);
    }
    if (!zeros.length || !infs.length) return null;
    const Z = mul([...rest, ...zeros]);
    const W = mul(infs);
    const logOnTop = infs.some((f) => /ln|log|atan|asin|acos/.test(nodeKey(f)));
    const expBelow = zeros.some((f) => f.type === 'pow' && !containsVar(f.base, v));
    const recip = (X) => niceForm(pow(X, NM1), v);
    const q = logOnTop || expBelow ? div(W, recip(Z)) : div(Z, recip(W));
    const L = limSub(q, { ...C, depth: C.depth + 1 });
    if (!L) return null;
    return {
        val: L,
        title: msg('calculus.limit.forms.form_0_fraction'),
        tex: eachLanguage((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} ${lt(q, Lg)} = ${vTex(L, Lg)}`),
        text: msg('calculus.limit.forms.rewrite_product_of_infinitesimal_and_infinitely'),
        rule: 'rewrite-fraction',
    };
}

function mSecondRemarkable(n, C) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'pow') return null;
    const B = S.base;
    const Ex = S.exp;
    const inner = trySimp(mul(Ex, add(B, NM1)));
    if (!inner) return null;
    const C2 = { ...C, depth: C.depth + 1, log: [] };
    const L = ev(inner, C2);
    if (!L) return null;
    let val;
    if (L.k === 'fin') val = fin(pow(E_, L.node));
    else if (L.k === 'inf') val = L.s > 0 ? infV(1) : fin(N0);
    else return null;
    return {
        val,
        title: msg('calculus.limit.forms.second_remarkable_limit'),
        tex: eachLanguage((Lg) => {
            const u = niceForm(add(B, NM1), v);
            const uT = u.type === 'add' || negLeadNode(u) ? paren(calcTex(u, Lg)) : calcTex(u, Lg);
            const inv = niceForm(pow(u, NM1), v);
            const innerN = niceForm(inner, v);
            const core = `\\left(1 + ${uT}\\right)^{${calcTex(inv, Lg)}}`;
            const outer = isNum(innerN) && innerN.value.isOne() ? core : `\\left[${core}\\right]^{${calcTex(innerN, Lg)}}`;
            return chainEq([
                `${limTex(P, v, Lg)} ${lt(n, Lg)}`,
                `${limTex(P, v, Lg)} ${outer}`,
                containsVar(innerN, v) ? `e^{${limTex(P, v, Lg)} ${lt(innerN, Lg)}}` : null,
                vTex(val, Lg),
            ]);
        }),
        text: msg('calculus.limit.forms.form_1_write_base_as_1'),
        rule: 'second-remarkable',
        sub: C2.log,
    };
}

function mExpLog(n, C, form) {
    const { v, P } = C;
    const S = trySimp(n);
    if (!S || S.type !== 'pow') return null;
    const inner = trySimp(mul(S.exp, fn('ln', S.base)));
    if (!inner) return null;
    const C2 = { ...C, depth: C.depth + 1, log: [] };
    const L = ev(inner, C2);
    if (!L) return null;
    let val;
    if (L.k === 'fin') val = fin(pow(E_, L.node));
    else if (L.k === 'inf') val = L.s > 0 ? infV(1) : fin(N0);
    else return null;
    return {
        val,
        title: msg('calculus.limit.forms.take_logarithm'),
        tex: eachLanguage((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = e^{${limTex(P, v, Lg)} ${lt(inner, Lg)}} = ${vTex(val, Lg)}`),
        text: msg('calculus.limit.forms.form_write_u_e_v_ln', { p: FORM_NAME[form] }),
        rule: 'exp-log',
        sub: C2.log,
    };
}

const METHODS = {
    '0/0': [mRational, mEquivalents, mConjugate, mLHopital, mSplitFraction],
    'inf/inf': [mRational, mLeading, mConjugate, mLHopital, mSplitFraction, mDivideDominant],
    'inf-inf': [mRational, mConjugate, mCommonDen, mLeading, mDominant],
    '0*inf': [mEquivalents, mRational, mLeading, mZeroInf],
    '1^inf': [mSecondRemarkable, mExpLog],
    '0^0': [mExpLog],
    'inf^0': [mExpLog],
};
