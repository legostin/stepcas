// derivative/steps — the step tree that mirrors the expression: rule lines, table formulas, names, tidy assembly.

import { add, num, mul, neg, pow, fn, div, containsVar, freeVars, isConst, sym } from '../../core/ast.js';
import { Q, MathError } from '../../core/rational.js';
import { simplify } from '../../core/simplify.js';
import { step } from '../../core/steps.js';
import { niceForm } from './clean.js';
import { E_, N0, N1, N2, NM1, calcTex, isNum, isOne, isZero, negLeading, paren, plain } from './display.js';
import { FACT_ERR } from './quick.js';
import { msg, eachLanguage } from '../../i18n/index.js';

// ---------------------------------------------------------------- tidy assembly (unsimplified answers and step lines)

function tAdd(terms) {
    const out = [];
    for (const t of terms) {
        if (isZero(t)) continue;
        if (t.type === 'add') out.push(...t.args);
        else out.push(t);
    }
    if (!out.length) return N0;
    return out.length === 1 ? out[0] : add(out);
}

function tMul(factors) {
    let c = Q.ONE;
    const rest = [];
    for (let f of factors) {
        if (f.type === 'neg') {
            c = c.neg();
            f = f.arg;
        }
        if (isNum(f)) {
            if (f.value.isZero()) return N0;
            c = c.mul(f.value);
            continue;
        }
        if (f.type === 'mul') {
            for (const g of f.args) {
                if (isNum(g)) c = c.mul(g.value);
                else rest.push(g);
            }
            continue;
        }
        rest.push(f);
    }
    if (!rest.length) return num(c);
    if (c.isOne()) return rest.length === 1 ? rest[0] : mul(rest);
    if (c.eq(-1)) return neg(rest.length === 1 ? rest[0] : mul(rest));
    return mul([num(c), ...rest]);
}

function tNeg(a) {
    if (isZero(a)) return a;
    if (a.type === 'neg') return a.arg;
    if (isNum(a)) return num(a.value.neg());
    return neg(a);
}

// ---------------------------------------------------------------- TeX pieces for the rule lines
// A piece is {t: lang → TeX, k: 'atom' | 'prod' | 'sum' | 'neg' | 'zero' | 'one'}.

function kindOf(node) {
    if (isZero(node)) return 'zero';
    if (isOne(node)) return 'one';
    if (node.type === 'add') return 'sum';
    if (negLeading(node)) return 'neg';
    if (node.type === 'mul') return 'prod';
    return 'atom';
}

const pNode = (node) => ({ t: (L) => calcTex(node, L), k: kindOf(node) });
const pPrime = (node) => ({ t: (L) => `${paren(calcTex(node, L))}'`, k: 'atom' });

function pProd(pieces, { dropOnes = false } = {}) {
    let ps = pieces;
    if (ps.some((p) => p.k === 'zero')) return { t: () => '0', k: 'zero' };
    if (dropOnes) ps = ps.filter((p) => p.k !== 'one');
    if (!ps.length) return { t: () => '1', k: 'one' };
    if (ps.length === 1) return ps[0];
    const t = (L) =>
        ps
            .map((p, i) => {
                const s = p.t(L);
                return p.k === 'sum' || (p.k === 'neg' && i > 0) ? paren(s) : s;
            })
            .join(' \\cdot ');
    return { t, k: ps[0].k === 'neg' ? 'neg' : 'prod' };
}

/** terms: [{p, minus}] */
function pSum(terms, { dropZeros = false } = {}) {
    let ts = terms;
    if (dropZeros) ts = ts.filter((x) => x.p.k !== 'zero');
    if (!ts.length) return { t: () => '0', k: 'zero' };
    if (ts.length === 1 && !ts[0].minus) return ts[0].p;
    const t = (L) =>
        ts
            .map((x, i) => {
                let s = x.p.t(L);
                if (x.minus) {
                    if (x.p.k === 'sum' || x.p.k === 'neg') s = paren(s);
                    return (i ? ' - ' : '-') + s;
                }
                if (i && x.p.k === 'neg') return ' - ' + s.replace(/^-\s*/, '');
                return (i ? ' + ' : '') + s;
            })
            .join('');
    return { t, k: ts.length === 1 ? 'neg' : 'sum' };
}

const pFrac = (a, b) => ({ t: (L) => `\\frac{${a.t(L)}}{${b.t(L)}}`, k: 'atom' });
const pNeg = (a) => ({ t: (L) => '-' + (a.k === 'sum' || a.k === 'neg' ? paren(a.t(L)) : a.t(L)), k: 'neg' });

/** "lhs = a = b = c" without repeating equal neighbours. */
function chainTex(parts) {
    return eachLanguage((L) => {
        const out = [];
        for (const p of parts) {
            if (!p) continue;
            const s = typeof p === 'function' ? p(L) : p.t(L);
            const norm = (x) => x.replace(/\\left|\\right|\\cdot|\s+/g, '');
            if (out.length && norm(out[out.length - 1]) === norm(s)) {
                out[out.length - 1] = s;
                continue;
            }
            out.push(s);
        }
        return out.join(' = ');
    });
}

// x^{-2}, x^{\frac{1}{2}} written as a power (the printer would turn them into fractions and roots)
function texPowRaw(base, e, L) {
    let b = calcTex(base, L);
    if (!(base.type === 'sym' || (isNum(base) && base.value.isInt() && !base.value.isNeg()))) b = paren(b);
    return `${b}^{${e.toTex(L)}}`;
}

// ---------------------------------------------------------------- names and table formulas for the texts

// the names of the functions and their table derivatives are messages: calculus.derivative.steps.fn.<name>, .table.<name>
const FN_NAMED = new Set([
    'sin',
    'cos',
    'tan',
    'cot',
    'sec',
    'csc',
    'asin',
    'acos',
    'atan',
    'acot',
    'sinh',
    'cosh',
    'tanh',
    'coth',
    'asinh',
    'acosh',
    'atanh',
    'ln',
    'lg',
    'log',
    'sqrt',
    'abs',
]);

const FORMULA = new Set([
    'sin',
    'cos',
    'tan',
    'cot',
    'sec',
    'csc',
    'asin',
    'acos',
    'atan',
    'acot',
    'sinh',
    'cosh',
    'tanh',
    'coth',
    'asinh',
    'acosh',
    'atanh',
    'ln',
    'lg',
    'sqrt',
]);

function formula(name, u) {
    return FORMULA.has(name) ? msg(`calculus.derivative.steps.table.${name}`, { u }) : null;
}

/** f'(u) for the step lines (readable, not canonical). */
function outerReadable(name, u, args) {
    const u2 = pow(u, N2);
    switch (name) {
        case 'sin':
            return fn('cos', u);
        case 'cos':
            return neg(fn('sin', u));
        case 'tan':
            return div(N1, pow(fn('cos', u), N2));
        case 'cot':
            return neg(div(N1, pow(fn('sin', u), N2)));
        case 'sec':
            return mul(fn('sec', u), fn('tan', u));
        case 'csc':
            return neg(mul(fn('csc', u), fn('cot', u)));
        case 'asin':
            return div(N1, fn('sqrt', add(N1, neg(u2))));
        case 'acos':
            return neg(div(N1, fn('sqrt', add(N1, neg(u2)))));
        case 'atan':
            return div(N1, add(N1, u2));
        case 'acot':
            return neg(div(N1, add(N1, u2)));
        case 'sinh':
            return fn('cosh', u);
        case 'cosh':
            return fn('sinh', u);
        case 'tanh':
            return div(N1, pow(fn('cosh', u), N2));
        case 'coth':
            return neg(div(N1, pow(fn('sinh', u), N2)));
        case 'asinh':
            return div(N1, fn('sqrt', add(u2, N1)));
        case 'acosh':
            return div(N1, fn('sqrt', add(u2, NM1)));
        case 'atanh':
            return div(N1, add(N1, neg(u2)));
        case 'ln':
            return div(N1, u);
        case 'lg':
            return div(N1, mul(u, fn('ln', num(10))));
        case 'log':
            return div(N1, mul(u, fn('ln', args[0])));
        case 'sqrt':
            return div(N1, mul(N2, fn('sqrt', u)));
        case 'abs':
            return div(u, fn('abs', u));
        default:
            return null;
    }
}

// ---------------------------------------------------------------- the step tree

function splitSignTerm(t) {
    if (t.type === 'neg') return { minus: true, abs: t.arg };
    if (isNum(t) && t.value.isNeg()) return { minus: true, abs: num(t.value.neg()) };
    if (t.type === 'mul' && isNum(t.args[0]) && t.args[0].value.isNeg()) {
        const c = t.args[0].value.neg();
        const rest = t.args.slice(1);
        return { minus: true, abs: c.isOne() ? (rest.length === 1 ? rest[0] : mul(rest)) : mul([num(c), ...rest]) };
    }
    return { minus: false, abs: t };
}

function simplifyNum(node) {
    try {
        const s = simplify(node);
        return isNum(s) ? s.value : null;
    } catch {
        return null;
    }
}

/**
 * Differentiate n by ctx.v with steps → {raw, res, step, trivial?}: raw — the assembled derivative before
 * simplification, res — its clean form (display node), step — the Step of this node.
 */
export function dS(n, ctx) {
    const { v } = ctx;
    if (!containsVar(n, v)) {
        const others = freeVars(n).filter((w) => w !== v);
        const st = step({
            title: msg('calculus.derivative.steps.derivative_of_constant'),
            tex: eachLanguage((L) => `${paren(calcTex(n, L))}' = 0`),
            text: others.length
                ? msg('calculus.derivative.steps.it_does_not_depend_on_when', { v, p: others.join(', ') })
                : msg('calculus.derivative.steps.derivative_of_number_is_zero_constant'),
            rule: 'const',
        });
        return { raw: N0, res: N0, step: st, trivial: true };
    }
    switch (n.type) {
        case 'sym':
            return {
                raw: N1,
                res: N1,
                trivial: true,
                step: step({ title: msg('calculus.derivative.steps.derivative_of_variable'), tex: `(${calcTex(n)})' = 1`, rule: 'var' }),
            };
        case 'add':
            return dSum(n, ctx);
        case 'neg':
            return dNeg(n, ctx);
        case 'mul':
            return dMul(n, ctx);
        case 'div':
            return dDiv(n, ctx);
        case 'pow':
            return dPow(n, ctx);
        case 'fn':
            return dFn(n, ctx);
        default:
            throw new MathError(msg('calculus.derivative.steps.cannot_differentiate_this_expression'), null, null, 'unsupported');
    }
}

const subSteps = (kids) => kids.filter((c) => c && c.step && !c.trivial).map((c) => c.step);

function finish(shown, ctx, { title, text, rule, ruleLine, assembled, asm, raw, kids, extraSub }) {
    const res = niceForm(asm, ctx.v);
    const tex = chainTex([(L) => `${paren(calcTex(shown, L))}'`, ruleLine, assembled, pNode(res)]);
    const sub = [...(extraSub ?? []), ...subSteps(kids ?? [])];
    return { raw, res, step: step({ title, tex, text, rule, sub }) };
}

function dSum(n, ctx) {
    const terms = n.args.map(splitSignTerm);
    const kids = terms.map((t) => dS(t.abs, ctx));
    return finish(n, ctx, {
        title: msg('calculus.derivative.steps.derivative_of_sum'),
        text: msg('calculus.derivative.steps.derivative_of_sum_is_sum_of'),
        rule: 'sum',
        ruleLine: pSum(terms.map((t) => ({ p: pPrime(t.abs), minus: t.minus }))),
        assembled: pSum(
            terms.map((t, i) => ({ p: pNode(kids[i].res), minus: t.minus })),
            { dropZeros: true },
        ),
        asm: tAdd(terms.map((t, i) => (t.minus ? tNeg(kids[i].res) : kids[i].res))),
        raw: tAdd(terms.map((t, i) => (t.minus ? tNeg(kids[i].raw) : kids[i].raw))),
        kids,
    });
}

function dNeg(n, ctx) {
    const k = dS(n.arg, ctx);
    return finish(n, ctx, {
        title: msg('calculus.derivative.steps.take_minus_out'),
        text: msg('calculus.derivative.steps.minus_sign_is_factor_1_it'),
        rule: 'neg',
        ruleLine: pNeg(pPrime(n.arg)),
        assembled: pNeg(pNode(k.res)),
        asm: tNeg(k.res),
        raw: tNeg(k.raw),
        kids: [k],
    });
}

function dMul(n, ctx) {
    const { v } = ctx;
    const consts = n.args.filter((f) => !containsVar(f, v));
    const vars = n.args.filter((f) => containsVar(f, v));
    if (consts.length) {
        const c = consts.length === 1 ? consts[0] : mul(consts);
        const u = vars.length === 1 ? vars[0] : mul(vars);
        const k = dS(u, ctx);
        return finish(n, ctx, {
            title: msg('calculus.derivative.steps.constant_factor'),
            text: msg('calculus.derivative.steps.constant_factor_comes_out_of_derivative'),
            rule: 'const-factor',
            ruleLine: pProd([pNode(c), pPrime(u)]),
            assembled: pProd([pNode(c), pNode(k.res)], { dropOnes: true }),
            asm: tMul([c, k.res]),
            raw: tMul([c, k.raw]),
            kids: [k],
        });
    }
    const kids = vars.map((f) => dS(f, ctx));
    const termOf = (i, d) => tMul(vars.map((g, j) => (i === j ? d : g)));
    const two = vars.length === 2;
    return finish(n, ctx, {
        title: msg('calculus.derivative.steps.product_rule'),
        text: two
            ? msg('calculus.derivative.steps.by_product_rule_derivative_of_first')
            : msg('calculus.derivative.steps.product_rule_for_several_factors_differentiate'),
        rule: 'product',
        ruleLine: pSum(vars.map((_, i) => ({ p: pProd(vars.map((g, j) => (i === j ? pPrime(g) : pNode(g)))) }))),
        assembled: pSum(
            vars.map((_, i) => ({
                p: pProd(
                    vars.map((g, j) => pNode(i === j ? kids[i].res : g)),
                    { dropOnes: true },
                ),
            })),
            { dropZeros: true },
        ),
        asm: tAdd(vars.map((_, i) => termOf(i, kids[i].res))),
        raw: tAdd(vars.map((_, i) => termOf(i, kids[i].raw))),
        kids,
    });
}

/** w = v, v^k, √v, ⁿ√v → the exponent (Q), else null. */
function powerOfVar(w, v) {
    const isV = (x) => x.type === 'sym' && x.name === v && !isConst(x);
    if (isV(w)) return Q.ONE;
    if (w.type === 'pow' && isV(w.base)) return simplifyNum(w.exp);
    if (w.type === 'fn' && w.name === 'sqrt' && isV(w.args[0])) return Q.HALF;
    if (w.type === 'fn' && w.name === 'root' && isV(w.args[0])) {
        const k = simplifyNum(w.args[1]);
        return k && !k.isZero() ? k.inv() : null;
    }
    return null;
}

function dDiv(n, ctx) {
    const { v } = ctx;
    const u = n.num;
    const w = n.den;
    const uv = containsVar(u, v);
    const wv = containsVar(w, v);
    if (!wv) {
        const k = dS(u, ctx);
        return finish(n, ctx, {
            title: msg('calculus.derivative.steps.division_by_constant'),
            text: msg('calculus.derivative.steps.denominator_does_not_depend_on_variable'),
            rule: 'const-factor',
            ruleLine: pFrac(pPrime(u), pNode(w)),
            assembled: pFrac(pNode(k.res), pNode(w)),
            asm: div(k.res, w),
            raw: div(k.raw, w),
            kids: [k],
        });
    }
    if (!uv) {
        const e = powerOfVar(w, v);
        if (e) {
            // c / x^k = c·x^(−k)
            const X = sym(v);
            const k = e.neg();
            const rewritten = isOne(u) ? pow(X, num(k)) : mul(u, pow(X, num(k)));
            const inner = dS(rewritten, ctx);
            const coefT = (L) => (isOne(u) ? '' : u.type === 'add' ? paren(calcTex(u, L)) : calcTex(u, L));
            const st = step({
                title: msg('calculus.derivative.steps.write_it_as_power'),
                tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, (L) => `${paren(coefT(L) + texPowRaw(X, k, L))}'`, pNode(inner.res)]),
                text: msg('calculus.derivative.steps.variable_is_only_in_denominator_so', { v }),
                rule: 'rewrite-power',
                sub: inner.step && !inner.trivial ? [inner.step] : [],
            });
            return { raw: inner.raw, res: inner.res, step: st };
        }
        const k = dS(w, ctx);
        const w2 = pow(w, N2);
        return finish(n, ctx, {
            title: msg('calculus.derivative.steps.constant_over_function'),
            text: msg('calculus.derivative.steps.numerator_is_constant_so_only_one'),
            rule: 'quotient',
            ruleLine: pNeg(pFrac(pProd([pNode(u), pPrime(w)], { dropOnes: true }), pNode(w2))),
            assembled: pNeg(pFrac(pProd([pNode(u), pNode(k.res)], { dropOnes: true }), pNode(w2))),
            asm: tNeg(div(tMul([u, k.res]), w2)),
            raw: tNeg(div(tMul([u, k.raw]), w2)),
            kids: [k],
        });
    }
    const ku = dS(u, ctx);
    const kw = dS(w, ctx);
    const w2 = pow(w, N2);
    return finish(n, ctx, {
        title: msg('calculus.derivative.steps.quotient_rule'),
        text: msg('calculus.derivative.steps.derivative_of_fraction_derivative_of_numerator'),
        rule: 'quotient',
        ruleLine: pFrac(pSum([{ p: pProd([pPrime(u), pNode(w)]) }, { p: pProd([pNode(u), pPrime(w)]), minus: true }]), pNode(w2)),
        assembled: pFrac(
            pSum([{ p: pProd([pNode(ku.res), pNode(w)], { dropOnes: true }) }, { p: pProd([pNode(u), pNode(kw.res)], { dropOnes: true }), minus: true }], {
                dropZeros: true,
            }),
            pNode(w2),
        ),
        asm: div(tAdd([tMul([ku.res, w]), tNeg(tMul([u, kw.res]))]), w2),
        raw: div(tAdd([tMul([ku.raw, w]), tNeg(tMul([u, kw.raw]))]), w2),
        kids: [ku, kw],
    });
}

/** TeX of n·b^(n−1) for the power rule (b^{n−1} written as a power). */
function powerPiece(b, e, eq) {
    const t = (L) => {
        let coef;
        if (eq) coef = eq.isOne() ? '' : eq.eq(-1) ? '-' : eq.toTex(L);
        else coef = e.type === 'add' || negLeading(e) ? paren(calcTex(e, L)) : calcTex(e, L);
        let pw;
        if (eq) {
            const m = eq.sub(Q.ONE);
            if (m.isZero()) pw = '';
            else if (m.isOne()) pw = b.type === 'sym' ? calcTex(b, L) : paren(calcTex(b, L));
            else pw = texPowRaw(b, m, L);
        } else {
            const bt0 = b.type === 'sym' ? calcTex(b, L) : paren(calcTex(b, L));
            pw = `${bt0}^{${calcTex(add(e, NM1), L)}}`;
        }
        if (!pw) return coef === '' ? '1' : coef === '-' ? '-1' : coef;
        const sep = /\\frac/.test(coef) || (!eq && coef.length > 1) ? ' \\cdot ' : '';
        return coef + sep + pw;
    };
    return { t, k: eq && eq.isNeg() ? 'neg' : 'prod' };
}

function dPow(n, ctx, shown = n) {
    const { v } = ctx;
    const b = n.base;
    const e = n.exp;
    const bv = containsVar(b, v);
    const ev = containsVar(e, v);
    if (bv && !ev) {
        const eq = simplifyNum(e);
        const outer = tMul([eq ? num(eq) : e, pow(b, eq ? num(eq.sub(Q.ONE)) : add(e, NM1))]);
        const piece = powerPiece(b, e, eq);
        if (b.type === 'sym') {
            const res = niceForm(outer, v);
            return {
                raw: outer,
                res,
                step: step({
                    title: msg('calculus.derivative.steps.power_rule'),
                    tex: chainTex([(L) => `${paren(calcTex(shown, L))}'`, piece, pNode(res)]),
                    text: msg('calculus.derivative.steps.n_exponent_becomes_factor_and_power', { v }),
                    rule: 'power',
                }),
            };
        }
        const k = dS(b, ctx);
        return finish(shown, ctx, {
            title: msg('calculus.derivative.steps.power_of_function_chain_rule'),
            text: msg('calculus.derivative.steps.composite_function_outer_one_is_power', { b: (lng) => plain(b, lng) }),
            rule: 'chain',
            ruleLine: pProd([piece, pPrime(b)]),
            assembled: pProd([piece, pNode(k.res)], { dropOnes: true }),
            asm: tMul([outer, k.res]),
            raw: tMul([outer, k.raw]),
            kids: [k],
        });
    }
    if (!bv && ev) {
        const isE = isConst(b) && b.name === 'e';
        const lnB = fn('ln', b);
        const outer = isE ? n : mul(n, lnB);
        if (e.type === 'sym') {
            const res = niceForm(outer, v);
            return {
                raw: outer,
                res,
                step: step({
                    title: isE ? msg('calculus.derivative.steps.derivative_of_exponential') : msg('calculus.derivative.steps.exponential_function'),
                    tex: chainTex([(L) => `${paren(calcTex(shown, L))}'`, pNode(outer), pNode(res)]),
                    text: isE
                        ? msg('calculus.derivative.steps.e_e_exponential_is_its_own', { v })
                        : msg('calculus.derivative.steps.table_derivative_ln', { v }),
                    rule: isE ? 'exp' : 'exp-base',
                }),
            };
        }
        const k = dS(e, ctx);
        const outerPieces = isE ? [pNode(n)] : [pNode(n), pNode(lnB)];
        return finish(shown, ctx, {
            title: isE ? msg('calculus.derivative.steps.exponential_of_function') : msg('calculus.derivative.steps.exponential_function_of_function'),
            text: isE
                ? msg('calculus.derivative.steps.composite_function_outer_one_is_exponential', { e: (lng) => plain(e, lng) })
                : msg('calculus.derivative.steps.composite_function_outer_one_is_inner', { e: (lng) => plain(e, lng) }),
            rule: 'chain',
            ruleLine: pProd([...outerPieces, pPrime(e)]),
            assembled: pProd([...outerPieces, pNode(k.res)], { dropOnes: true }),
            asm: tMul([outer, k.res]),
            raw: tMul([outer, k.raw]),
            kids: [k],
        });
    }
    // both vary: u^w = e^(w ln u)
    const prod = mul(e, fn('ln', b));
    const k = dS(prod, ctx);
    return finish(shown, ctx, {
        title: msg('calculus.derivative.steps.logarithmic_differentiation'),
        text: msg('calculus.derivative.steps.variable_is_both_in_base_and'),
        rule: 'log-diff',
        ruleLine: pProd([pNode(n), pPrime(prod)]),
        assembled: pProd([pNode(n), pNode(k.res)], { dropOnes: true }),
        asm: tMul([n, k.res]),
        raw: tMul([n, k.raw]),
        kids: [k],
    });
}

function dFn(n, ctx) {
    const { v } = ctx;
    const name = n.name;
    if (name === 'fact') throw FACT_ERR();
    if (name === 'exp') return dPow(pow(E_, n.args[0]), ctx, n);
    if (name === 'root') {
        const [x, k] = n.args;
        const kq = simplifyNum(k);
        if (!kq || kq.isZero()) return dS(pow(x, div(N1, k)), ctx);
        const inner = dPow(pow(x, num(kq.inv())), ctx);
        const st = step({
            title: msg('calculus.derivative.steps.root_as_power'),
            tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, (L) => `${paren(texPowRaw(x, kq.inv(), L))}'`, pNode(inner.res)]),
            text: msg('calculus.derivative.steps.n_th_root_is_power_with'),
            rule: 'rewrite-power',
            sub: inner.step ? [inner.step] : [],
        });
        return { raw: inner.raw, res: inner.res, step: st };
    }
    if (name === 'log' && containsVar(n.args[0], v)) {
        const q = div(fn('ln', n.args[1]), fn('ln', n.args[0]));
        const inner = dS(q, ctx);
        const st = step({
            title: msg('calculus.derivative.steps.change_to_natural_logarithm'),
            tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, (L) => `${paren(calcTex(q, L))}'`, pNode(inner.res)]),
            text: msg('calculus.derivative.steps.base_depends_on_variable_so_switch'),
            rule: 'log-base',
            sub: inner.step ? [inner.step] : [],
        });
        return { raw: inner.raw, res: inner.res, step: st };
    }
    if (name === 'sign' || name === 'floor' || name === 'ceil') {
        const text =
            name === 'sign'
                ? msg('calculus.derivative.steps.sgn_is_constant_on_each_side')
                : msg('calculus.derivative.steps.function_is_constant_between_consecutive_whole');
        return {
            raw: N0,
            res: N0,
            step: step({
                title: msg('calculus.derivative.steps.step_function'),
                tex: eachLanguage((L) => `${paren(calcTex(n, L))}' = 0`),
                text,
                rule: 'step-fn',
            }),
        };
    }
    const u = name === 'log' ? n.args[1] : n.args[0];
    const outer = outerReadable(name, u, n.args);
    if (!outer) throw new MathError(msg('calculus.derivative.steps.cannot_differentiate', { name }), null, null, 'unsupported');
    const absNote = name === 'abs' ? msg('calculus.derivative.steps.this_holds_for_u_0_absolute') : '';
    if (u.type === 'sym' && u.name === v && !isConst(u)) {
        const res = niceForm(outer, v);
        const f = formula(name, v);
        let text;
        if (name === 'abs') text = msg('calculus.derivative.steps.it_is_1_for_0_and', { v });
        else if (name === 'log') text = msg('calculus.derivative.steps.table_derivative_log_1_ln', { v });
        else if (f) text = msg('calculus.derivative.steps.table_derivative', { p: f });
        return {
            raw: outer,
            res,
            step: step({
                title: msg('calculus.derivative.steps.table_derivative_2'),
                tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, pNode(outer), pNode(res)]),
                text,
                rule: 'table',
            }),
        };
    }
    const k = dS(u, ctx);
    const nm = FN_NAMED.has(name) ? msg(`calculus.derivative.steps.fn.${name}`) : name;
    const f = formula(name, 'u');
    let law;
    if (name === 'log') law = '(logₐ u)′ = u′/(u·ln a)';
    else if (name === 'abs') law = '(|u|)′ = u/|u|·u′';
    else law = eachLanguage((l) => `${f.in(l)}·u′`);
    return finish(n, ctx, {
        title: msg('calculus.derivative.steps.chain_rule', { f: nm }),
        text: msg('calculus.derivative.steps.outer_function_is_inner_one_is', { f: nm, u: (lng) => plain(u, lng), law, note: absNote }),
        rule: 'chain',
        ruleLine: pProd([pNode(outer), pPrime(u)]),
        assembled: pProd([pNode(outer), pNode(k.res)], { dropOnes: true }),
        asm: tMul([outer, k.res]),
        raw: tMul([outer, k.raw]),
        kids: [k],
    });
}
