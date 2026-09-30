// limit/forms — indeterminate forms: rational functions, equivalents, the conjugate, leading terms, L'Hôpital,
// dividing by the fastest-growing term, splitting a fraction, ∞ − ∞, 0·∞ and powers.

import { prettyForm, ratFunctionOf, calcTex, niceForm, quickDerivative } from '../derivative/index.js';
import { nodeKey, num, sym, div, mul, pow, add, neg, fn, containsVar, isConst, substitute } from '../../core/ast.js';
import { step } from '../../core/steps.js';
import { expand, combineFractions } from '../../core/expand.js';
import { Poly } from '../../core/poly.js';
import { toText } from '../../core/print.js';
import { splitCoeff } from '../../core/simplify.js';
import { Q } from '../../core/rational.js';
import { evaluate } from '../../core/evaluate.js';
import { E_, HALF, N0, N1, N2, NM1, T_, bt, chainEq, fin, infV, isNum, isZeroN, isZeroV, limTex, lt, negLeadNode, paren, paren2, qn2, simp, trySimp, tx } from './common.js';
import { ev, splitNumDen } from './evaluator.js';

// ---------------------------------------------------------------- indeterminate forms

export const FORM_TEX = { '0/0': '\\frac{0}{0}', 'inf/inf': '\\frac{\\infty}{\\infty}', 'inf-inf': '\\infty - \\infty', '0*inf': '0 \\cdot \\infty', '1^inf': '1^{\\infty}', '0^0': '0^{0}', 'inf^0': '\\infty^{0}' };
export const FORM_NAME = { '0/0': '0/0', 'inf/inf': '∞/∞', 'inf-inf': '∞ − ∞', '0*inf': '0·∞', '1^inf': '1^∞', '0^0': '0⁰', 'inf^0': '∞⁰' };

function vTex(L, Lg) {
    if (!L) return '?';
    if (L.k === 'fin') return tx(prettyForm(L.node), Lg);
    if (L.k === 'inf') return L.s > 0 ? '+\\infty' : '-\\infty';
    return Lg === 'ru' ? '\\text{не существует}' : '\\text{does not exist}';
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
    C.log.push(step({
        title: res.title,
        tex: res.tex,
        text: res.text,
        rule: res.rule,
        sub: [...(res.sub ?? []), ...C2.log],
    }));
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
            const inner = simp(expand(div(p.toNode(v), mul(qn2(q.lead), pow(X, num(dp))))));
            const lead = simp(mul(qn2(p.lead.div(q.lead)), pow(X, num(dp))));
            return {
                val,
                title: T_('Выносим старшую степень', 'Take out the highest power'),
                tex: bt((L) => `${limTex(P, v, L)} ${lt(n, L)} = ${limTex(P, v, L)} ${dp === 1 && p.lead.div(q.lead).isOne() ? tx(X, L) : lt(lead, L)}${inner.type === 'add' ? paren(tx(inner, L)) : ''} = ${vTex(val, L)}`.replace(/\\cdot\s*$/, '')),
                text: T_(`Многочлен при ${v} → ${P.x > 0 ? '+∞' : '−∞'} ведёт себя как его старший член: выносим ${v}${supd(dp)} за скобки, в скобках все слагаемые, кроме первого, стремятся к нулю.`,
                    `As ${v} → ${P.x > 0 ? '+∞' : '−∞'} a polynomial behaves like its leading term: take ${v}${supd(dp)} out of the brackets; inside, every term but the first tends to zero.`),
                rule: 'leading-power',
            };
        }
        return {
            val,
            title: form === 'inf-inf' ? T_('Приводим к общему знаменателю', 'Common denominator') : T_('Делим на старшую степень', 'Divide by the highest power'),
            tex: bt((L) => chainEq([`${limTex(P, v, L)} ${lt(n, L)}`, `${limTex(P, v, L)} ${lt(q.degree > 0 ? div(p.toNode(v), q.toNode(v)) : p.toNode(v), L)}`, k > 0 ? `${limTex(P, v, L)} \\frac{${tx(dividedBy(p, k, v), L)}}{${tx(dividedBy(q, k, v), L)}}` : null, vTex(val, L)])),
            text: dp < dq
                ? T_(`Степень числителя (${dp}) меньше степени знаменателя (${dq}): делим числитель и знаменатель на ${v}${supd(k)}, все слагаемые вида c/${v}ᵐ стремятся к нулю, и предел равен 0.`, `The numerator's degree (${dp}) is less than the denominator's (${dq}): divide both by ${v}${supd(k)}; every term c/${v}ᵐ tends to zero, so the limit is 0.`)
                : dp === dq
                    ? T_(`Степени числителя и знаменателя равны (${dp}): делим оба на ${v}${supd(k)}, и остаётся отношение старших коэффициентов.`, `The degrees are equal (${dp}): divide both by ${v}${supd(k)}; what remains is the ratio of the leading coefficients.`)
                    : T_(`Степень числителя (${dp}) больше степени знаменателя (${dq}), поэтому дробь растёт неограниченно; знак определяют старшие коэффициенты.`, `The numerator's degree (${dp}) exceeds the denominator's (${dq}), so the fraction grows without bound; the leading coefficients fix the sign.`),
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
        title: T_('Раскладываем на множители и сокращаем', 'Factor and cancel'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)}${showFactor ? ` = ${limTex(P, v, Lg)} \\frac{${fN(Lg)}}{${fD(Lg)}}` : ''} = ${limTex(P, v, Lg)} ${lt(reduced, Lg)} = ${vTex(L, Lg)}`),
        text: T_(`Числитель и знаменатель обращаются в ноль при ${v} = ${plainNum(P)}, значит, у обоих есть множитель (${v} − ${plainNum(P)}). Раскладываем их на множители, сокращаем этот общий множитель — он не равен нулю, пока ${v} ≠ ${plainNum(P)}, — и после этого подставляем.`,
            `Both the numerator and the denominator vanish at ${v} = ${plainNum(P)}, so both have the factor (${v} − ${plainNum(P)}). Factor them, cancel the common factor (it is nonzero while ${v} ≠ ${plainNum(P)}), and then substitute.`),
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
    return k === 1 ? '' : String(k).split('').map((c) => S[c]).join('');
}

export function plainNum(P) {
    try {
        return toText(prettyForm(P.a), { lang: 'en' }).replace(/\bpi\b/g, 'π').replace(/sqrt\(/g, '√(').replace(/\*/g, '·');
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
const FN_RU = { sin: 'sin', tan: 'tg', asin: 'arcsin', atan: 'arctg', sinh: 'sh', tanh: 'th', asinh: 'arsh', atanh: 'arth' };
const FN_EN = { sin: 'sin', tan: 'tan', asin: 'arcsin', atan: 'arctan', sinh: 'sinh', tanh: 'tanh', asinh: 'arsinh', atanh: 'artanh' };

function tendsTo(n, target, C) {
    const L = ev(n, { ...C, log: [], depth: C.depth + 1 });
    if (!L || L.k !== 'fin') return false;
    const d = trySimp(add(L.node, neg(target)));
    return d !== null && isZeroN(d);
}

/** Equivalent of an infinitesimal factor F: {E, ru, en} or null. */
function equivalentOf(F, C) {
    if (F.type === 'fn' && EQUIV_FN.has(F.name) && tendsTo(F.args[0], N0, C)) {
        return { E: F.args[0], ru: `${FN_RU[F.name]} u ~ u`, en: `${FN_EN[F.name]} u ~ u` };
    }
    if (F.type === 'fn' && (F.name === 'ln' || F.name === 'lg') && tendsTo(F.args[0], N1, C)) {
        const E = add(F.args[0], NM1);
        return F.name === 'ln' ? { E, ru: 'ln(1 + u) ~ u', en: 'ln(1 + u) ~ u' } : { E: div(E, fn('ln', num(10))), ru: 'lg(1 + u) ~ u/ln 10', en: 'log₁₀(1 + u) ~ u/ln 10' };
    }
    if (F.type === 'fn' && F.name === 'log' && tendsTo(F.args[1], N1, C)) return { E: div(add(F.args[1], NM1), fn('ln', F.args[0])), ru: 'logₐ(1 + u) ~ u/ln a', en: 'logₐ(1 + u) ~ u/ln a' };
    if (F.type === 'add' && F.args.length === 2) {
        const kIdx = F.args.findIndex((t) => isNum(t));
        if (kIdx < 0) return null;
        const k = F.args[kIdx].value;
        const t1 = F.args[1 - kIdx];
        // F = t1 + k = −k·(Y − 1) with Y = t1/(−k)
        const Y = trySimp(div(t1, num(k.neg())));
        if (!Y) return null;
        const outer = num(k.neg());
        const wrap = (E, ru, en) => ({ E: k.eq(-1) ? E : mul(outer, E), ru, en });
        if (Y.type === 'pow' && !containsVar(Y.base, C.v) && tendsTo(Y.exp, N0, C)) {
            const isE = isConst(Y.base) && Y.base.name === 'e';
            return wrap(isE ? Y.exp : mul(Y.exp, fn('ln', Y.base)), isE ? 'eᵘ − 1 ~ u' : 'aᵘ − 1 ~ u·ln a', isE ? 'eᵘ − 1 ~ u' : 'aᵘ − 1 ~ u·ln a');
        }
        if (Y.type === 'fn' && Y.name === 'cos' && tendsTo(Y.args[0], N0, C)) {
            return wrap(neg(div(pow(Y.args[0], N2), N2)), '1 − cos u ~ u²/2', '1 − cos u ~ u²/2');
        }
        if (Y.type === 'pow' && isNum(Y.exp) && tendsTo(Y.base, N1, C)) {
            return wrap(mul(Y.exp, add(Y.base, NM1)), '(1 + u)ᵃ − 1 ~ a·u', '(1 + u)ᵃ − 1 ~ a·u');
        }
        if (Y.type === 'fn' && Y.name === 'cosh' && tendsTo(Y.args[0], N0, C)) {
            return wrap(div(pow(Y.args[0], N2), N2), 'ch u − 1 ~ u²/2', 'cosh u − 1 ~ u²/2');
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
        used.push({ from: base, to: trySimp(eq.E) ?? eq.E, ru: eq.ru, en: eq.en });
        out.push(e ? pow(eq.E, e) : eq.E);
    }
    if (!changed) return null;
    const next = trySimp(mul(out));
    if (!next) return null;
    const C2 = { ...C, depth: C.depth + 1 };
    const L = limSub(next, C2);
    if (!L) return null;
    const laws = [...new Set(used.map((u) => u.ru))];
    const lawsEn = [...new Set(used.map((u) => u.en))];
    return {
        val: L,
        title: T_('Эквивалентные бесконечно малые', 'Equivalent infinitesimals'),
        tex: bt((Lg) => `${used.map((u) => `${tx(u.from, Lg)} \\sim ${tx(u.to, Lg)}`).join(',\\quad ')};\\qquad ${limTex(P, v, Lg)} ${lt(n, Lg)} = ${containsVar(next, v) ? `${limTex(P, v, Lg)} ${paren2(tx(next, Lg), next)} = ` : ''}${vTex(L, Lg)}`),
        text: T_(`Бесконечно малые множители заменяем эквивалентными (${laws.join('; ')}, где u → 0). В произведении и частном такая замена не меняет предела.`,
            `Replace the infinitesimal factors by equivalent ones (${lawsEn.join('; ')}, where u → 0). In a product or a quotient this does not change the limit.`),
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
            title: T_('Умножаем на сопряжённое', 'Multiply by the conjugate'),
            tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} \\frac{${paren(tx(base, Lg))}${paren(tx(conj, Lg))}}{${tx(conj, Lg)}}${e.isOne() ? '' : '^{-1}'} = ${limTex(P, v, Lg)} ${lt(next, Lg)} = ${vTex(L, Lg)}`),
            text: cube
                ? T_('Разность кубических корней даёт неопределённость. Домножаем до разности кубов: (a − b)(a² + ab + b²) = a³ − b³, и корни уходят из этого множителя.',
                    'The difference of cube roots is indeterminate. Complete it to a difference of cubes: (a − b)(a² + ab + b²) = a³ − b³, which removes the roots from this factor.')
                : T_('Разность с корнем даёт неопределённость. Умножаем и делим на сопряжённое выражение: (a − b)(a + b) = a² − b², и корень уходит из этого множителя.',
                    'The difference with a root is indeterminate. Multiply and divide by the conjugate: (a − b)(a + b) = a² − b², which removes the root from this factor.'),
            rule: 'conjugate',
        };
    }
    return null;
}

// ---- leading terms at ±∞ (algebraic expressions)

/** n ~ c·t^p as t → +∞ (t is the variable): {c: number, p: Q} or null. */
export function asym(n, v) {
    switch (n.type) {
        case 'num':
            return n.value.isZero() ? null : { c: n.value.toNumber(), p: Q.ZERO };
        case 'sym':
            if (n.name === v && !isConst(n)) return { c: 1, p: Q.ONE };
            if (isConst(n) && (n.name === 'pi' || n.name === 'e')) return { c: evaluate(n), p: Q.ZERO };
            return null;
        case 'mul': {
            let c = 1;
            let p = Q.ZERO;
            for (const f of n.args) {
                const a = asym(f, v);
                if (!a) return null;
                c *= a.c;
                p = p.add(a.p);
            }
            return { c, p };
        }
        case 'pow': {
            if (!isNum(n.exp)) return null;
            const a = asym(n.base, v);
            if (!a) return null;
            const r = n.exp.value;
            if (a.c < 0 && !r.isInt()) return null;
            return { c: Math.pow(a.c, r.toNumber()), p: a.p.mul(r) };
        }
        case 'add': {
            let best = null;
            let sum = 0;
            for (const t of n.args) {
                const a = asym(t, v);
                if (!a) return null;
                if (!best || a.p.gt(best.p)) {
                    best = { ...a };
                    sum = a.c;
                } else if (a.p.eq(best.p)) sum += a.c;
            }
            if (!best || Math.abs(sum) < 1e-12 * Math.max(1, Math.abs(best.c))) return null;
            return { c: sum, p: best.p };
        }
        default:
            return null;
    }
}

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
        title: T_('Делим на старшую степень', 'Divide by the highest power'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${vTex(val, Lg)}`),
        text: T_(`При ${v} → ${flip ? '−∞' : '+∞'} в каждой сумме главное — слагаемое со старшей степенью ${v}. Делим числитель и знаменатель на ${v}${k.isOne() ? '' : '^' + k.toString()}${flip ? ' (при отрицательных ' + v + ' корень из ' + v + '² равен −' + v + ')' : ''}: остальные слагаемые стремятся к нулю, и остаётся отношение старших членов.`,
            `As ${v} → ${flip ? '−∞' : '+∞'} each sum is dominated by its highest power of ${v}. Divide the numerator and the denominator by ${v}${k.isOne() ? '' : '^' + k.toString()}${flip ? ' (for negative ' + v + ', √(' + v + '²) = −' + v + ')' : ''}: the other terms tend to zero and the ratio of the leading terms remains.`),
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
            if (k && Math.abs((k * Math.sqrt(m)) / d - c) < 1e-10 * Math.max(1, Math.abs(c))) return simp(mul(num(new Q(BigInt(k), BigInt(d))), pow(num(m), HALF)));
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
    if (isZeroN(trySimp(dw) ?? dw)) return null;
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
        title: T_('Правило Лопиталя', "L'Hôpital's rule"),
        tex: bt((Lg) => `${limTex(P, v, Lg)} \\frac{${tx(uS, Lg)}}{${tx(wS, Lg)}} = ${limTex(P, v, Lg)} \\frac{${paren(tx(uS, Lg))}'}{${paren(tx(wS, Lg))}'} = ${limTex(P, v, Lg)} ${lt(next, Lg)}${tx(tidy, Lg) !== tx(next, Lg) ? ` = ${limTex(P, v, Lg)} ${paren2(tx(tidy, Lg), tidy)}` : ''} = ${vTex(L, Lg)}`),
        text: T_(`Неопределённость ${FORM_NAME[form]}: числитель и знаменатель дифференцируемы, производная знаменателя вблизи точки не обращается в ноль. По правилу Лопиталя предел отношения функций равен пределу отношения их производных (если последний существует).`,
            `The form ${FORM_NAME[form]}: numerator and denominator are differentiable and the derivative of the denominator does not vanish near the point. By L'Hôpital's rule the limit of the ratio equals the limit of the ratio of the derivatives (when that exists).`),
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
            title: T_('Делим на главное слагаемое', 'Divide by the dominant term'),
            tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} \\frac{${tx(a, Lg)}}{${tx(b, Lg)}} = ${vTex(val, Lg)}`),
            text: T_(`Делим числитель и знаменатель на слагаемое ${toText(prettyForm(T), { lang: 'ru' })}, которое растёт быстрее остальных: остальные части стремятся к конечным пределам (ограниченная функция, делённая на бесконечно большую, стремится к нулю).`,
                `Divide the numerator and the denominator by ${toText(prettyForm(T), { lang: 'en' })}, the fastest-growing term: what remains tends to finite limits (a bounded function over an infinitely large one tends to zero).`),
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
        title: T_('Делим почленно', 'Divide term by term'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} ${paren(tx(X, Lg))} = ${vTex(L, Lg)}`),
        text: T_('Делим каждое слагаемое числителя на знаменатель: получается сумма, предел каждого слагаемого находится сразу (ограниченная функция, делённая на бесконечно большую, стремится к нулю).',
            'Divide each term of the numerator by the denominator: the limit of each term of the sum is immediate (a bounded function over an infinitely large one tends to zero).'),
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
        title: T_('Приводим к общему знаменателю', 'Bring to a common denominator'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${paren(tx(n, Lg))} = ${limTex(P, v, Lg)} ${lt(cf, Lg)} = ${vTex(L, Lg)}`),
        text: T_('Неопределённость ∞ − ∞: сводим разность дробей к одной дроби — получается неопределённость вида 0/0 или ∞/∞, с которой уже можно работать.', 'The form ∞ − ∞: combine the fractions into one, which gives 0/0 or ∞/∞ that we can handle.'),
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
            title: T_('Выносим главное слагаемое', 'Take out the dominant term'),
            tex: bt((Lg) => `${limTex(P, v, Lg)} ${paren(tx(n, Lg))} = ${limTex(P, v, Lg)} ${T.type === 'add' || T.type === 'mul' ? paren(tx(T, Lg)) : tx(T, Lg)}\\left(${tx(add(N1, rest), Lg)}\\right) = ${vTex(val, Lg)}`),
            text: T_('Выносим за скобки слагаемое, которое растёт быстрее всех: в скобках остаётся величина с конечным ненулевым пределом, поэтому выражение стремится к бесконечности.', 'Take out the fastest-growing term: the bracket tends to a finite nonzero number, so the expression tends to infinity.'),
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
        title: T_('Неопределённость 0·∞ → дробь', 'The form 0·∞ → a fraction'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = ${limTex(P, v, Lg)} ${lt(q, Lg)} = ${vTex(L, Lg)}`),
        text: T_('Произведение бесконечно малой на бесконечно большую переписываем дробью: u·w = u/(1/w). Получается неопределённость 0/0 или ∞/∞.', 'Rewrite the product of an infinitesimal and an infinitely large quantity as a fraction: u·w = u/(1/w), giving 0/0 or ∞/∞.'),
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
        title: T_('Второй замечательный предел', 'The second remarkable limit'),
        tex: bt((Lg) => {
            const u = niceForm(add(B, NM1), v);
            const uT = u.type === 'add' || negLeadNode(u) ? paren(tx(u, Lg)) : tx(u, Lg);
            const inv = niceForm(pow(u, NM1), v);
            const innerN = niceForm(inner, v);
            const core = `\\left(1 + ${uT}\\right)^{${tx(inv, Lg)}}`;
            const outer = isNum(innerN) && innerN.value.isOne() ? core : `\\left[${core}\\right]^{${tx(innerN, Lg)}}`;
            return chainEq([`${limTex(P, v, Lg)} ${lt(n, Lg)}`, `${limTex(P, v, Lg)} ${outer}`, containsVar(innerN, v) ? `e^{${limTex(P, v, Lg)} ${lt(innerN, Lg)}}` : null, vTex(val, Lg)]);
        }),
        text: T_('Неопределённость 1^∞. Основание записываем как 1 + u, где u → 0, и пользуемся вторым замечательным пределом (1 + u)^(1/u) → e: весь предел равен e в степени lim u·(показатель).',
            'The form 1^∞. Write the base as 1 + u with u → 0 and use the second remarkable limit (1 + u)^(1/u) → e: the whole limit is e to the power lim u·(exponent).'),
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
        title: T_('Логарифмируем степень', 'Take the logarithm'),
        tex: bt((Lg) => `${limTex(P, v, Lg)} ${lt(n, Lg)} = e^{${limTex(P, v, Lg)} ${lt(inner, Lg)}} = ${vTex(val, Lg)}`),
        text: T_(`Неопределённость ${FORM_NAME[form]}: записываем uᵛ = e^(v·ln u). Экспонента непрерывна, поэтому достаточно найти предел показателя v·ln u.`,
            `The form ${FORM_NAME[form]}: write uᵛ = e^(v·ln u). The exponential is continuous, so it is enough to find the limit of v·ln u.`),
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
