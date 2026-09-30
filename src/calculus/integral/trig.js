// integral/trig — trigonometric forms, trigonometric substitutions for square roots, the universal t = tg(x/2).

import { div, fn, mapNode, containsVar, nodeKey, mul, num, substitute, sym, add, neg, pow, nodeChildren } from '../../core/ast.js';
import { splitCoeff } from '../../core/simplify.js';
import { ratFunctionOf } from '../derivative/index.js';
import { step } from '../../core/steps.js';
import { expand } from '../../core/expand.js';
import { Q } from '../../core/rational.js';
import { Poly } from '../../core/poly.js';
import { plainish } from './basic.js';
import { HALF, N1, N2, NM1, T_, bt, coefTex, freshVar, iTex, isNum, isVar, linearParts, paren, simp, trySimp, tx } from './common.js';
import { I, sub } from './engine.js';
import { qn } from './rational.js';

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
export function canonicalRational(node, v) {
    const r = ratFunctionOf(node, v);
    if (!r) return null;
    if (r.den.degree < 1) return trySimp(r.num.scale(r.den.coeff(0).inv()).toNode(v));
    return trySimp(div(r.num.toNode(v), r.den.toNode(v)));
}

export function substResult(f, ctx, { t, uNode, g, title, text, rule, dtTex }) {
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

export function mTrig(f, ctx) {
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
export function mTrigLower(f, ctx) {
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

export function mTrigSub(f, ctx) {
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
export function mCyclic(f, ctx) {
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

export function mWeierstrass(f, ctx) {
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
