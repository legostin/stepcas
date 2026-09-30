// algebra — school transformations step by step: factoring, expanding, reducing fractions (ОГЭ, ЕГЭ base).
//
//   factorSteps("x^3 - x")              → {result, steps}   x(x − 1)(x + 1)
//   expandSteps("(x + 1)^2 - (x - 1)^2") → {result, steps}   4x
//   simplifySteps("(x^2 - 9)/(x - 3)")   → {result, steps, restrictions}   x + 3, x ≠ 3
//
// Polynomials in one variable with rational coefficients. Factoring goes the school way: the common factor,
// the difference of squares, the sum and difference of cubes, a perfect square, a quadratic through its roots,
// a rational root found among the divisors of the free term and divided out (Horner). Every result is checked
// against the input polynomial.
import { Q, MathError } from '../core/rational.js';
import { num, sym, add, mul, div, neg, pow, nodeKey, freeVars, containsVar, numValue } from '../core/ast.js';
import { parse } from '../core/parse.js';
import { toTex, toText } from '../core/print.js';
import { simplify } from '../core/simplify.js';
import { expand, numDen } from '../core/expand.js';
import { L, step } from '../core/steps.js';
import { Poly } from '../core/poly.js';

const tex = (n, l = 'ru') => toTex(n, { lang: l });
const bt = (f) => L(f('ru'), f('en'));
const simpO = (n) => {
    try {
        return simplify(n);
    } catch {
        return n;
    }
};
const asNode = (x) => (typeof x === 'string' ? parse(x) : x);
const polyTex = (P, v, l) => tex(P.toNode(v), l);

/* ------------------------------------------------------------------ factoring */

// a rational q = r² → r (positive), else null
const sq = (q) => (q.isNeg() ? null : q.exactRoot(2));
const cube = (q) => q.exactRoot(3);
// the linear factor px + q with integer coefficients and a positive p, for a root r = −q/p
const linFromRoot = (r) => new Poly([new Q(-r.n), new Q(r.d)]);

/**
 * Factor one polynomial → {factors: [{poly, mult}], constant, steps}; each step names its formula.
 * The factors are primitive (integer coefficients, positive leading), the constant carries the rest.
 */
function factorPoly(P, v) {
    const steps = [];
    let constant = Q.ONE;
    const out = [];
    let R = P;
    // the common factor: the content and the lowest power of v
    const c = R.content();
    let m = 0;
    while (m < R.c.length && R.c[m].isZero()) m++;
    if (!c.isOne() || m > 0) {
        const X = sym(v);
        const common = mul([...(c.isOne() ? [] : [num(c)]), ...(m === 0 ? [] : [m === 1 ? X : pow(X, num(m))])]);
        R = new Poly(R.c.slice(m)).scale(c.inv());
        constant = c;
        if (m > 0) out.push({ poly: new Poly([Q.ZERO, Q.ONE]), mult: m });
        if (R.degree >= 1) {
            steps.push(step({
                title: L('Выносим общий множитель за скобки', 'Take the common factor out'),
                tex: bt((l) => `${polyTex(P, v, l)} = ${tex(common, l)}\\left(${polyTex(R, v, l)}\\right)`),
            }));
        }
    }
    const queue = R.degree >= 1 ? [R] : [];
    if (R.degree < 1) constant = constant.mul(R.coeff(0));
    while (queue.length) {
        const F = queue.shift();
        if (F.degree === 1) {
            const k = F.content();
            constant = constant.mul(k);
            out.push({ poly: F.scale(k.inv()), mult: 1 });
            continue;
        }
        const [a, b, cc] = [F.coeff(F.degree), F.coeff(1), F.coeff(0)];
        const X = sym(v);
        const onlyEnds = F.c.slice(1, -1).every((z) => z.isZero());
        // a²x² − b²: the difference of squares (also for x⁴ − 16 and the like: x^(2k))
        if (onlyEnds && F.degree % 2 === 0 && a.isPos() && cc.isNeg() && sq(a) && sq(cc.neg())) {
            const h = F.degree / 2;
            const p = sq(a);
            const q = sq(cc.neg());
            const base = h === 1 ? X : pow(X, num(h));
            const u = Poly.monomial(p, h);
            const f1 = u.sub(new Poly([q]));
            const f2 = u.add(new Poly([q]));
            steps.push(step({
                title: L('Разность квадратов', 'The difference of squares'),
                tex: bt((l) => {
                    const pb = simpO(mul(num(p), base));
                    const pT = pb.type === 'sym' ? tex(pb, l) : `\\left(${tex(pb, l)}\\right)`;
                    return `${polyTex(F, v, l)} = ${pT}^2 - ${q.toTex(l)}^2 = \\left(${polyTex(f1, v, l)}\\right)\\left(${polyTex(f2, v, l)}\\right)`;
                }),
                text: L('$a^2 - b^2 = (a - b)(a + b)$.'),
            }));
            queue.push(f1, f2);
            continue;
        }
        // a³x³ ± b³: the sum or the difference of cubes
        if (onlyEnds && F.degree === 3 && cube(a) && cube(cc)) {
            const p = cube(a);
            const q = cube(cc);
            const lin = new Poly([q, p]);
            const quad = new Poly([q.mul(q), p.mul(q).neg(), p.mul(p)]);
            const plus = q.isPos();
            steps.push(step({
                title: plus ? L('Сумма кубов', 'The sum of cubes') : L('Разность кубов', 'The difference of cubes'),
                tex: bt((l) => `${polyTex(F, v, l)} = \\left(${polyTex(lin, v, l)}\\right)\\left(${polyTex(quad, v, l)}\\right)`),
                text: plus ? L('$a^3 + b^3 = (a + b)(a^2 - ab + b^2)$.') : L('$a^3 - b^3 = (a - b)(a^2 + ab + b^2)$.'),
            }));
            queue.push(lin, quad);
            continue;
        }
        if (F.degree === 2) {
            const D = b.mul(b).sub(a.mul(cc).mul(new Q(4n)));
            if (D.isNeg()) {
                constant = constant.mul(F.content());
                out.push({ poly: F.primitive(), mult: 1 });
                steps.push(step({ title: L('Трёхчлен не раскладывается', 'The quadratic does not factor'), tex: bt((l) => `${polyTex(F, v, l)}:\\ D = ${D.toTex(l)} < 0`), text: L('Действительных корней нет.', 'It has no real roots.') }));
                continue;
            }
            const sd = D.exactRoot(2);
            if (!sd) {
                constant = constant.mul(F.content());
                out.push({ poly: F.primitive(), mult: 1 });
                steps.push(step({ title: L('Корни иррациональные', 'The roots are irrational'), tex: bt((l) => `${polyTex(F, v, l)}:\\ D = ${D.toTex(l)}`), text: L('Над рациональными числами трёхчлен не раскладывается.', 'The quadratic does not factor over the rationals.') }));
                continue;
            }
            const x1 = b.neg().sub(sd).div(a.mul(new Q(2n)));
            const x2 = b.neg().add(sd).div(a.mul(new Q(2n)));
            if (D.isZero()) {
                const f = linFromRoot(x1);
                const k = a.div(f.lead.mul(f.lead));
                constant = constant.mul(k);
                out.push({ poly: f, mult: 2 });
                steps.push(step({
                    title: L('Полный квадрат', 'A perfect square'),
                    tex: bt((l) => `${polyTex(F, v, l)} = ${k.isOne() ? '' : k.toTex(l)}\\left(${polyTex(f, v, l)}\\right)^2`),
                    text: L('$a^2 \\pm 2ab + b^2 = (a \\pm b)^2$ (дискриминант равен нулю).', '$a^2 \\pm 2ab + b^2 = (a \\pm b)^2$ (the discriminant is zero).'),
                }));
                continue;
            }
            const f1 = linFromRoot(x1);
            const f2 = linFromRoot(x2);
            const k = a.div(f1.lead.mul(f2.lead));
            constant = constant.mul(k);
            out.push({ poly: f1, mult: 1 }, { poly: f2, mult: 1 });
            steps.push(step({
                title: L('Раскладываем квадратный трёхчлен по корням', 'Factor the quadratic through its roots'),
                tex: bt((l) => `D = ${D.toTex(l)},\\ ${v}_1 = ${x1.toTex(l)},\\ ${v}_2 = ${x2.toTex(l)} \\;\\Rightarrow\\; ${polyTex(F, v, l)} = ${k.isOne() ? '' : k.eq(-1) ? '-' : k.toTex(l)}\\left(${polyTex(f1, v, l)}\\right)\\left(${polyTex(f2, v, l)}\\right)`),
                text: x1.isInt() && x2.isInt()
                    ? L(`$a${v}^2 + b${v} + c = a(${v} - ${v}_1)(${v} - ${v}_2)$.`)
                    : L(`$a${v}^2 + b${v} + c = a(${v} - ${v}_1)(${v} - ${v}_2)$; дробный корень записываем без дроби, внося знаменатель в скобку: ${[x1, x2].filter((z) => !z.isInt()).map((z) => `$${v} - ${z.toTex('ru')} \\to ${polyTex(linFromRoot(z), v, 'ru')}$`).join(', ')}.`, `$a${v}^2 + b${v} + c = a(${v} - ${v}_1)(${v} - ${v}_2)$; a fractional root goes into its bracket without the fraction: ${[x1, x2].filter((z) => !z.isInt()).map((z) => `$${v} - ${z.toTex('en')} \\to ${polyTex(linFromRoot(z), v, 'en')}$`).join(', ')}.`),
            }));
            continue;
        }
        // a rational root among the divisors: divide it out
        const roots = F.rationalRoots();
        if (roots.length) {
            const r = roots[0].root ?? roots[0];
            const f = linFromRoot(r);
            const { q: G, r: rem } = F.divmod(f);
            if (!rem.isZero()) break;
            steps.push(step({
                title: L('Подбираем корень и делим', 'Find a root and divide'),
                tex: bt((l) => `${polyTex(F, v, l)} = \\left(${polyTex(f, v, l)}\\right)\\left(${polyTex(G, v, l)}\\right)`),
                text: L(`Корень ищем среди делителей свободного члена (делённых на делители старшего коэффициента): $${v} = ${r.toTex('ru')}$ обращает многочлен в ноль. Делим на $${polyTex(f, v, 'ru')}$ уголком или по схеме Горнера.`, `A root is sought among the divisors of the free term (over the divisors of the leading coefficient): $${v} = ${r.toTex('en')}$ makes it zero. Divide by $${polyTex(f, v, 'en')}$ (long division or Horner).`),
            }));
            queue.push(f, G);
            continue;
        }
        constant = constant.mul(F.content());
        out.push({ poly: F.primitive(), mult: 1 });
    }
    // merge equal factors
    const merged = [];
    for (const f of out) {
        const same = merged.find((g) => g.poly.equals(f.poly));
        if (same) same.mult += f.mult;
        else merged.push({ ...f });
    }
    // x first, then linear factors by their roots, then the rest
    const key = (f) => (f.poly.degree === 1 && f.poly.coeff(0).isZero() ? -Infinity : f.poly.degree === 1 ? f.poly.coeff(0).neg().div(f.poly.coeff(1)).toNumber() : 1e9 + f.poly.degree);
    merged.sort((p, q) => key(p) - key(q));
    return { factors: merged, constant, steps };
}

function productNode(constant, factors, v) {
    const fs = factors.map(({ poly, mult }) => (mult === 1 ? poly.toNode(v) : pow(poly.toNode(v), num(mult))));
    if (constant.eq(-1)) return neg(mul(fs.length ? fs : [num(1)]));
    return mul([...(constant.isOne() && fs.length ? [] : [num(constant)]), ...fs]);
}

function onlyVar(node) {
    const vs = freeVars(node);
    if (vs.length !== 1) throw new MathError(L('Нужно выражение с одной переменной.', 'An expression in one variable is needed.'));
    return vs[0];
}

/** Factor a polynomial in one variable with the school formulas. */
export function factorSteps(input, opts = {}) {
    const node = asNode(input);
    const v = opts.v ?? onlyVar(node);
    const P = Poly.fromNode(node, v);
    if (!P || P.degree < 1) return null;
    const r = factorPoly(P, v);
    const result = productNode(r.constant, r.factors, v);
    // the check
    let back = new Poly([r.constant]);
    for (const { poly, mult } of r.factors) back = back.mul(poly.pow(mult));
    if (!back.equals(P)) return null;
    const steps = [step({ title: L('Выражение', 'The expression'), tex: bt((l) => tex(node, l)) }), ...r.steps];
    if (!r.steps.length) steps.push(step({ title: L('Разложить нельзя', 'It does not factor'), text: L('Многочлен неприводим над рациональными числами.', 'The polynomial is irreducible over the rationals.') }));
    steps.push(step({ title: L('Ответ', 'Answer'), tex: bt((l) => `${tex(node, l)} = ${tex(result, l)}`) }));
    steps[steps.length - 1].final = true;
    return { result, steps, factors: r.factors, constant: r.constant };
}

/* ------------------------------------------------------------------ expanding */

// one product or power expanded by its formula, the terms kept apart: (x + 1)² → x² + 2x + 1
function expandOne(t) {
    const S = (n) => simpO(n);
    if (t.type === 'pow' && numValue(t.exp)?.eq(2) && t.base.type === 'add' && t.base.args.length === 2) {
        const [a, b0] = t.base.args;
        const minus = b0.type === 'neg';
        const b = minus ? b0.arg : b0;
        const mid = S(mul(num(2), a, b));
        return { node: add(S(pow(a, num(2))), minus ? neg(mid) : mid, S(pow(b, num(2)))), rule: minus ? L('квадрат разности $(a - b)^2 = a^2 - 2ab + b^2$', 'the square of a difference $(a - b)^2 = a^2 - 2ab + b^2$') : L('квадрат суммы $(a + b)^2 = a^2 + 2ab + b^2$', 'the square of a sum $(a + b)^2 = a^2 + 2ab + b^2$') };
    }
    if (t.type === 'pow' && numValue(t.exp)?.eq(3) && t.base.type === 'add' && t.base.args.length === 2) {
        const [a, b0] = t.base.args;
        const minus = b0.type === 'neg';
        const b = minus ? b0.arg : b0;
        const t2 = S(mul(num(3), pow(a, num(2)), b));
        const t4 = S(pow(b, num(3)));
        return { node: add(S(pow(a, num(3))), minus ? neg(t2) : t2, S(mul(num(3), a, pow(b, num(2)))), minus ? neg(t4) : t4), rule: minus ? L('куб разности', 'the cube of a difference') : L('куб суммы', 'the cube of a sum') };
    }
    if (t.type === 'mul' && t.args.length === 2 && t.args.every((f) => f.type === 'add' && f.args.length === 2)) {
        const [[a1, b1], [a2, b2]] = t.args.map((f) => f.args);
        if (nodeKey(S(a1)) === nodeKey(S(a2)) && nodeKey(S(b1)) === nodeKey(S(neg(b2)))) {
            const b = b1.type === 'neg' ? b1.arg : b1;
            return { node: add(S(pow(a1, num(2))), neg(S(pow(b, num(2))))), rule: L('разность квадратов $(a - b)(a + b) = a^2 - b^2$', 'the difference of squares $(a - b)(a + b) = a^2 - b^2$') };
        }
    }
    if (t.type === 'mul' && t.args.some((f) => f.type === 'add')) {
        let e;
        try {
            e = expand(t);
        } catch {
            return null;
        }
        return { node: e, rule: L('раскрываем скобки: каждый член умножаем на каждый', 'open the brackets: every term times every term') };
    }
    return null;
}

/** Open the brackets with the school formulas, then collect like terms. */
export function expandSteps(input) {
    const node = asNode(input);
    const terms = node.type === 'add' ? node.args : [node];
    const rules = [];
    let changed = false;
    const opened = terms.map((t) => {
        const negT = t.type === 'neg';
        const core = negT ? t.arg : t;
        const r = expandOne(core);
        if (!r) return t;
        changed = true;
        if (!rules.some((x) => x.ru === r.rule.ru)) rules.push(r.rule);
        return negT ? neg(r.node) : r.node;
    });
    let result;
    try {
        result = simpO(expand(node));
    } catch {
        return null;
    }
    const steps = [step({ title: L('Выражение', 'The expression'), tex: bt((l) => tex(node, l)) })];
    const mid = opened.length === 1 ? opened[0] : add(opened);
    if (changed) {
        steps.push(step({
            title: L('Раскрываем скобки', 'Open the brackets'),
            tex: bt((l) => `${tex(node, l)} = ${tex(mid, l)}`),
            text: L(`По формулам: ${rules.map((r) => r.ru).join('; ')}.`, `By the formulas: ${rules.map((r) => r.en).join('; ')}.`),
        }));
    }
    if (tex(mid) !== tex(result)) steps.push(step({ title: L('Приводим подобные', 'Collect like terms'), tex: bt((l) => `${tex(mid, l)} = ${tex(result, l)}`) }));
    steps.push(step({ title: L('Ответ', 'Answer'), tex: bt((l) => `${tex(node, l)} = ${tex(result, l)}`) }));
    steps[steps.length - 1].final = true;
    return { result, steps };
}

/* ------------------------------------------------------------------ fractions */

/** Simplify: a fraction of polynomials is factored and reduced (with the excluded values); a polynomial is expanded. */
export function simplifySteps(input) {
    const node = asNode(input);
    let nd = null;
    try {
        nd = numDen(node);
    } catch {
        nd = null;
    }
    const vs = freeVars(node);
    if (!nd || !containsVar(nd.den, vs[0] ?? 'x') || vs.length !== 1) return expandSteps(node);
    const v = vs[0];
    const N = Poly.fromNode(nd.num, v);
    const D = Poly.fromNode(nd.den, v);
    if (!N || !D) return null;
    const fN = factorPoly(N, v);
    const fD = factorPoly(D, v);
    const steps = [step({ title: L('Выражение', 'The expression'), tex: bt((l) => tex(node, l)) })];
    // the excluded values: zeros of the denominator
    const zeros = D.rationalRoots().map((r) => r.root ?? r);
    const G = N.gcd(D);
    const numF = productNode(fN.constant, fN.factors, v);
    const denF = productNode(fD.constant, fD.factors, v);
    if (fN.steps.length || fD.steps.length) {
        steps.push(step({ title: L('Раскладываем числитель и знаменатель на множители', 'Factor the numerator and the denominator'), tex: bt((l) => `${tex(node, l)} = \\frac{${tex(numF, l)}}{${tex(denF, l)}}`), sub: [...fN.steps, ...fD.steps] }));
    }
    const Nr = N.divmod(G).q;
    const Dr = D.divmod(G).q;
    // integer coefficients on both floors: (x/2 + 1/2)/(x + 1/2) → (x + 1)/(2x + 1)
    let result;
    if (Dr.degree === 0) result = Nr.scale(Dr.coeff(0).inv()).toNode(v);
    else {
        const k = Nr.content().div(Dr.content());
        const top = Nr.primitive().scale(new Q(k.n));
        const bottom = Dr.primitive().scale(new Q(k.d));
        result = div(top.toNode(v), bottom.toNode(v));
    }
    const restr = zeros.length ? bt((l) => zeros.map((z) => `${v} \\ne ${z.toTex(l)}`).join(',\\ ')) : null;
    if (G.degree >= 1) {
        steps.push(step({
            title: L('Сокращаем дробь', 'Reduce the fraction'),
            tex: bt((l) => `\\frac{${tex(numF, l)}}{${tex(denF, l)}} = ${tex(result, l)}`),
            text: L(`Сокращаем на $${polyTex(G.primitive(), v, 'ru')}$. Это можно, пока знаменатель не равен нулю: ${zeros.map((z) => `$${v} \\ne ${z.toTex('ru')}$`).join(', ')}.`, `Cancel $${polyTex(G.primitive(), v, 'en')}$. This is allowed while the denominator is not zero: ${zeros.map((z) => `$${v} \\ne ${z.toTex('en')}$`).join(', ')}.`),
        }));
    }
    steps.push(step({ title: L('Ответ', 'Answer'), tex: bt((l) => `${tex(node, l)} = ${tex(result, l)}${restr ? `,\\quad ${restr[l] ?? restr}` : ''}`) }));
    steps[steps.length - 1].final = true;
    return { result, steps, restrictions: zeros };
}
