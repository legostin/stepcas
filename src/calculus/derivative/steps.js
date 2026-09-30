// derivative/steps — the step tree that mirrors the expression: rule lines, table formulas, names, tidy assembly.

import { add, num, mul, neg, pow, fn, div, containsVar, freeVars, isConst, sym } from '../../core/ast.js';
import { Q, MathError } from '../../core/rational.js';
import { simplify } from '../../core/simplify.js';
import { step } from '../../core/steps.js';
import { niceForm } from './clean.js';
import { E_, N0, N1, N2, NM1, T_, bt, calcTex, isNum, isOne, isZero, negLeading, paren, plain } from './display.js';
import { FACT_ERR } from './quick.js';

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
    return bt((L) => {
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

const FN_NAME = {
    sin: ['синус', 'sine'],
    cos: ['косинус', 'cosine'],
    tan: ['тангенс', 'tangent'],
    cot: ['котангенс', 'cotangent'],
    sec: ['секанс', 'secant'],
    csc: ['косеканс', 'cosecant'],
    asin: ['арксинус', 'arcsine'],
    acos: ['арккосинус', 'arccosine'],
    atan: ['арктангенс', 'arctangent'],
    acot: ['арккотангенс', 'arccotangent'],
    sinh: ['гиперболический синус', 'hyperbolic sine'],
    cosh: ['гиперболический косинус', 'hyperbolic cosine'],
    tanh: ['гиперболический тангенс', 'hyperbolic tangent'],
    coth: ['гиперболический котангенс', 'hyperbolic cotangent'],
    asinh: ['обратный гиперболический синус', 'inverse hyperbolic sine'],
    acosh: ['обратный гиперболический косинус', 'inverse hyperbolic cosine'],
    atanh: ['обратный гиперболический тангенс', 'inverse hyperbolic tangent'],
    ln: ['натуральный логарифм', 'natural logarithm'],
    lg: ['десятичный логарифм', 'common logarithm'],
    log: ['логарифм', 'logarithm'],
    sqrt: ['квадратный корень', 'square root'],
    abs: ['модуль', 'absolute value'],
};

const FORMULA = {
    sin: (u) => [`(sin ${u})′ = cos ${u}`],
    cos: (u) => [`(cos ${u})′ = −sin ${u}`],
    tan: (u) => [`(tg ${u})′ = 1/cos² ${u}`, `(tan ${u})′ = 1/cos² ${u}`],
    cot: (u) => [`(ctg ${u})′ = −1/sin² ${u}`, `(cot ${u})′ = −1/sin² ${u}`],
    sec: (u) => [`(sec ${u})′ = sec ${u}·tg ${u}`, `(sec ${u})′ = sec ${u}·tan ${u}`],
    csc: (u) => [`(cosec ${u})′ = −cosec ${u}·ctg ${u}`, `(csc ${u})′ = −csc ${u}·cot ${u}`],
    asin: (u) => [`(arcsin ${u})′ = 1/√(1 − ${u}²)`],
    acos: (u) => [`(arccos ${u})′ = −1/√(1 − ${u}²)`],
    atan: (u) => [`(arctg ${u})′ = 1/(1 + ${u}²)`, `(arctan ${u})′ = 1/(1 + ${u}²)`],
    acot: (u) => [`(arcctg ${u})′ = −1/(1 + ${u}²)`, `(arccot ${u})′ = −1/(1 + ${u}²)`],
    sinh: (u) => [`(sh ${u})′ = ch ${u}`, `(sinh ${u})′ = cosh ${u}`],
    cosh: (u) => [`(ch ${u})′ = sh ${u}`, `(cosh ${u})′ = sinh ${u}`],
    tanh: (u) => [`(th ${u})′ = 1/ch² ${u}`, `(tanh ${u})′ = 1/cosh² ${u}`],
    coth: (u) => [`(cth ${u})′ = −1/sh² ${u}`, `(coth ${u})′ = −1/sinh² ${u}`],
    asinh: (u) => [`(arsh ${u})′ = 1/√(${u}² + 1)`, `(arsinh ${u})′ = 1/√(${u}² + 1)`],
    acosh: (u) => [`(arch ${u})′ = 1/√(${u}² − 1)`, `(arcosh ${u})′ = 1/√(${u}² − 1)`],
    atanh: (u) => [`(arth ${u})′ = 1/(1 − ${u}²)`, `(artanh ${u})′ = 1/(1 − ${u}²)`],
    ln: (u) => [`(ln ${u})′ = 1/${u}`],
    lg: (u) => [`(lg ${u})′ = 1/(${u}·ln 10)`, `(log₁₀ ${u})′ = 1/(${u}·ln 10)`],
    sqrt: (u) => [`(√${u})′ = 1/(2√${u})`],
};

function formula(name, u) {
    const f = FORMULA[name];
    if (!f) return null;
    const [ru, en] = f(u);
    return { ru, en: en ?? ru };
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
            title: T_('Производная постоянной', 'Derivative of a constant'),
            tex: bt((L) => `${paren(calcTex(n, L))}' = 0`),
            text: others.length
                ? T_(`От ${v} не зависит: ${others.join(', ')} при дифференцировании по ${v} считаем постоянными. Производная постоянной равна нулю.`,
                    `It does not depend on ${v}: when differentiating with respect to ${v} we treat ${others.join(', ')} as constants. The derivative of a constant is zero.`)
                : T_('Производная числа равна нулю: постоянная не меняется.', 'The derivative of a number is zero: a constant does not change.'),
            rule: 'const',
        });
        return { raw: N0, res: N0, step: st, trivial: true };
    }
    switch (n.type) {
        case 'sym':
            return { raw: N1, res: N1, trivial: true, step: step({ title: T_('Производная переменной', 'Derivative of the variable'), tex: `(${calcTex(n)})' = 1`, rule: 'var' }) };
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
            throw new MathError({ ru: 'Не умею дифференцировать это выражение', en: 'Cannot differentiate this expression' }, null, null, 'unsupported');
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
        title: T_('Производная суммы', 'Derivative of a sum'),
        text: T_('Производная суммы равна сумме производных: дифференцируем каждое слагаемое отдельно.', 'The derivative of a sum is the sum of the derivatives: differentiate term by term.'),
        rule: 'sum',
        ruleLine: pSum(terms.map((t) => ({ p: pPrime(t.abs), minus: t.minus }))),
        assembled: pSum(terms.map((t, i) => ({ p: pNode(kids[i].res), minus: t.minus })), { dropZeros: true }),
        asm: tAdd(terms.map((t, i) => (t.minus ? tNeg(kids[i].res) : kids[i].res))),
        raw: tAdd(terms.map((t, i) => (t.minus ? tNeg(kids[i].raw) : kids[i].raw))),
        kids,
    });
}

function dNeg(n, ctx) {
    const k = dS(n.arg, ctx);
    return finish(n, ctx, {
        title: T_('Минус выносим', 'Take the minus out'),
        text: T_('Знак минус — это множитель −1, его выносим за знак производной.', 'The minus sign is a factor −1; it comes out of the derivative.'),
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
            title: T_('Постоянный множитель', 'Constant factor'),
            text: T_('Постоянный множитель выносим за знак производной: (c·u)′ = c·u′.', 'A constant factor comes out of the derivative: (c·u)′ = c·u′.'),
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
        title: T_('Правило произведения', 'Product rule'),
        text: two
            ? T_('По правилу произведения: производная первого множителя на второй плюс первый на производную второго, (uv)′ = u′v + uv′.',
                'By the product rule: the derivative of the first factor times the second plus the first times the derivative of the second, (uv)′ = u′v + uv′.')
            : T_('Правило произведения для нескольких множителей: по очереди дифференцируем один множитель, остальные оставляем как есть, и всё складываем.',
                'The product rule for several factors: differentiate one factor at a time, keep the others as they are, and add everything up.'),
        rule: 'product',
        ruleLine: pSum(vars.map((_, i) => ({ p: pProd(vars.map((g, j) => (i === j ? pPrime(g) : pNode(g)))) }))),
        assembled: pSum(vars.map((_, i) => ({ p: pProd(vars.map((g, j) => pNode(i === j ? kids[i].res : g)), { dropOnes: true }) })), { dropZeros: true }),
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
            title: T_('Деление на постоянную', 'Division by a constant'),
            text: T_('Знаменатель от переменной не зависит — это постоянный множитель 1/c, его выносим за знак производной.', 'The denominator does not depend on the variable: it is a constant factor 1/c that comes out of the derivative.'),
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
                title: T_('Записываем как степень', 'Write it as a power'),
                tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, (L) => `${paren(coefT(L) + texPowRaw(X, k, L))}'`, pNode(inner.res)]),
                text: T_(`Переменная стоит только в знаменателе, поэтому удобно записать дробь как степень с отрицательным показателем: 1/${v}ᵏ = ${v}⁻ᵏ, и взять производную степени.`,
                    `The variable is only in the denominator, so write the fraction as a power with a negative exponent, 1/${v}ᵏ = ${v}⁻ᵏ, and use the power rule.`),
                rule: 'rewrite-power',
                sub: inner.step && !inner.trivial ? [inner.step] : [],
            });
            return { raw: inner.raw, res: inner.res, step: st };
        }
        const k = dS(w, ctx);
        const w2 = pow(w, N2);
        return finish(n, ctx, {
            title: T_('Постоянная, делённая на функцию', 'A constant over a function'),
            text: T_('Числитель постоянный, поэтому от правила частного остаётся одно слагаемое: (c/v)′ = −c·v′/v².', 'The numerator is constant, so only one term of the quotient rule is left: (c/v)′ = −c·v′/v².'),
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
        title: T_('Правило частного', 'Quotient rule'),
        text: T_('Производная дроби: производная числителя на знаменатель минус числитель на производную знаменателя, и всё делим на квадрат знаменателя: (u/v)′ = (u′v − uv′)/v².',
            'The derivative of a fraction: the derivative of the numerator times the denominator minus the numerator times the derivative of the denominator, all over the denominator squared: (u/v)′ = (u′v − uv′)/v².'),
        rule: 'quotient',
        ruleLine: pFrac(pSum([{ p: pProd([pPrime(u), pNode(w)]) }, { p: pProd([pNode(u), pPrime(w)]), minus: true }]), pNode(w2)),
        assembled: pFrac(
            pSum([{ p: pProd([pNode(ku.res), pNode(w)], { dropOnes: true }) }, { p: pProd([pNode(u), pNode(kw.res)], { dropOnes: true }), minus: true }], { dropZeros: true }),
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
                    title: T_('Производная степени', 'Power rule'),
                    tex: chainTex([(L) => `${paren(calcTex(shown, L))}'`, piece, pNode(res)]),
                    text: T_(`(${v}ⁿ)′ = n·${v}ⁿ⁻¹: показатель становится множителем, а степень уменьшается на единицу.`, `(${v}ⁿ)′ = n·${v}ⁿ⁻¹: the exponent becomes a factor and the power drops by one.`),
                    rule: 'power',
                }),
            };
        }
        const k = dS(b, ctx);
        return finish(shown, ctx, {
            title: T_('Степень сложной функции', 'Power of a function (chain rule)'),
            text: T_(`Сложная функция: внешняя — степень uⁿ, внутренняя — u = ${plain(b, 'ru')}. По цепному правилу (uⁿ)′ = n·uⁿ⁻¹·u′.`,
                `A composite function: the outer one is the power uⁿ, the inner one is u = ${plain(b, 'en')}. By the chain rule (uⁿ)′ = n·uⁿ⁻¹·u′.`),
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
                    title: isE ? T_('Производная экспоненты', 'Derivative of the exponential') : T_('Показательная функция', 'Exponential function'),
                    tex: chainTex([(L) => `${paren(calcTex(shown, L))}'`, pNode(outer), pNode(res)]),
                    text: isE
                        ? T_(`(e^${v})′ = e^${v}: экспонента при дифференцировании не меняется.`, `(e^${v})′ = e^${v}: the exponential is its own derivative.`)
                        : T_(`Табличная производная: (a^${v})′ = a^${v}·ln a.`, `A table derivative: (a^${v})′ = a^${v}·ln a.`),
                    rule: isE ? 'exp' : 'exp-base',
                }),
            };
        }
        const k = dS(e, ctx);
        const outerPieces = isE ? [pNode(n)] : [pNode(n), pNode(lnB)];
        return finish(shown, ctx, {
            title: isE ? T_('Экспонента от функции', 'Exponential of a function') : T_('Показательная функция от функции', 'Exponential function of a function'),
            text: isE
                ? T_(`Сложная функция: внешняя — экспонента, внутренняя — u = ${plain(e, 'ru')}. (eᵘ)′ = eᵘ·u′.`, `A composite function: the outer one is the exponential, the inner one is u = ${plain(e, 'en')}. (eᵘ)′ = eᵘ·u′.`)
                : T_(`Сложная функция: внешняя — показательная aᵘ, внутренняя — u = ${plain(e, 'ru')}. (aᵘ)′ = aᵘ·ln a·u′.`, `A composite function: the outer one is aᵘ, the inner one is u = ${plain(e, 'en')}. (aᵘ)′ = aᵘ·ln a·u′.`),
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
        title: T_('Логарифмическое дифференцирование', 'Logarithmic differentiation'),
        text: T_('Переменная есть и в основании, и в показателе, поэтому не подходит ни правило степени, ни правило показательной функции. Запишем uᵛ = e^(v·ln u): тогда (uᵛ)′ = uᵛ·(v·ln u)′. То же получится, если прологарифмировать: ln y = v·ln u.',
            'The variable is both in the base and in the exponent, so neither the power rule nor the exponential rule applies. Write uᵛ = e^(v·ln u); then (uᵛ)′ = uᵛ·(v·ln u)′. Taking logarithms, ln y = v·ln u, gives the same.'),
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
            title: T_('Корень как степень', 'A root as a power'),
            tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, (L) => `${paren(texPowRaw(x, kq.inv(), L))}'`, pNode(inner.res)]),
            text: T_('Корень n-й степени — это степень с показателем 1/n: ⁿ√u = u^(1/n). Дальше — правило степени.', 'An n-th root is a power with exponent 1/n: ⁿ√u = u^(1/n). Then the power rule.'),
            rule: 'rewrite-power',
            sub: inner.step ? [inner.step] : [],
        });
        return { raw: inner.raw, res: inner.res, step: st };
    }
    if (name === 'log' && containsVar(n.args[0], v)) {
        const q = div(fn('ln', n.args[1]), fn('ln', n.args[0]));
        const inner = dS(q, ctx);
        const st = step({
            title: T_('Переход к натуральному логарифму', 'Change to the natural logarithm'),
            tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, (L) => `${paren(calcTex(q, L))}'`, pNode(inner.res)]),
            text: T_('Основание логарифма зависит от переменной, поэтому переходим к натуральным логарифмам: logₐb = ln b / ln a.', 'The base depends on the variable, so switch to natural logarithms: logₐb = ln b / ln a.'),
            rule: 'log-base',
            sub: inner.step ? [inner.step] : [],
        });
        return { raw: inner.raw, res: inner.res, step: st };
    }
    if (name === 'sign' || name === 'floor' || name === 'ceil') {
        const text = name === 'sign'
            ? T_('Функция sgn постоянна и слева, и справа от нуля, поэтому её производная равна 0 везде, где аргумент не равен нулю (в самом нуле скачок, и производной нет).',
                'sgn is constant on each side of zero, so its derivative is 0 wherever the argument is not zero (at zero there is a jump and no derivative).')
            : T_('Функция постоянна между соседними целыми значениями аргумента, поэтому производная равна 0 везде, кроме точек, где аргумент целый (там скачок, и производной нет).',
                'The function is constant between consecutive whole values of the argument, so the derivative is 0 except where the argument is a whole number (there it jumps and has no derivative).');
        return { raw: N0, res: N0, step: step({ title: T_('Ступенчатая функция', 'A step function'), tex: bt((L) => `${paren(calcTex(n, L))}' = 0`), text, rule: 'step-fn' }) };
    }
    const u = name === 'log' ? n.args[1] : n.args[0];
    const outer = outerReadable(name, u, n.args);
    if (!outer) throw new MathError({ ru: `Не умею дифференцировать функцию ${name}`, en: `Cannot differentiate ${name}` }, null, null, 'unsupported');
    const absNote = name === 'abs'
        ? T_(' Это верно при u ≠ 0: в нуле у модуля излом, и производной там нет.', ' This holds for u ≠ 0: the absolute value has a corner at zero, with no derivative there.')
        : T_('', '');
    if (u.type === 'sym' && u.name === v && !isConst(u)) {
        const res = niceForm(outer, v);
        const f = formula(name, v);
        let text;
        if (name === 'abs') text = T_(`(|${v}|)′ = ${v}/|${v}|: это +1 при ${v} > 0 и −1 при ${v} < 0. В нуле у модуля излом, и производной там нет.`, `(|${v}|)′ = ${v}/|${v}|: it is +1 for ${v} > 0 and −1 for ${v} < 0. At zero there is a corner, with no derivative.`);
        else if (name === 'log') text = T_(`Табличная производная: (logₐ ${v})′ = 1/(${v}·ln a).`, `A table derivative: (logₐ ${v})′ = 1/(${v}·ln a).`);
        else if (f) text = T_(`Табличная производная: ${f.ru}.`, `A table derivative: ${f.en}.`);
        return {
            raw: outer,
            res,
            step: step({ title: T_('Табличная производная', 'Table derivative'), tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, pNode(outer), pNode(res)]), text, rule: 'table' }),
        };
    }
    const k = dS(u, ctx);
    const nm = FN_NAME[name] ?? [name, name];
    const f = formula(name, 'u');
    let law;
    if (name === 'log') law = T_('(logₐ u)′ = u′/(u·ln a)', '(logₐ u)′ = u′/(u·ln a)');
    else if (name === 'abs') law = T_('(|u|)′ = u/|u|·u′', '(|u|)′ = u/|u|·u′');
    else law = T_(`${f.ru}·u′`, `${f.en}·u′`);
    return finish(n, ctx, {
        title: T_(`Сложная функция: ${nm[0]}`, `Chain rule: ${nm[1]}`),
        text: T_(`Внешняя функция — ${nm[0]}, внутренняя — u = ${plain(u, 'ru')}. Берём производную внешней функции по u и умножаем на производную внутренней: ${law.ru}.${absNote.ru}`,
            `The outer function is the ${nm[1]}, the inner one is u = ${plain(u, 'en')}. Differentiate the outer function with respect to u and multiply by the derivative of the inner one: ${law.en}.${absNote.en}`),
        rule: 'chain',
        ruleLine: pProd([pNode(outer), pPrime(u)]),
        assembled: pProd([pNode(outer), pNode(k.res)], { dropOnes: true }),
        asm: tMul([outer, k.res]),
        raw: tMul([outer, k.raw]),
        kids: [k],
    });
}
