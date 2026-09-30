// solve/exponential — powers of a common base and exponential equations.

import { sym, num, fn, containsVar, mul, add, nodeKey, pow, div, neg, numValue } from '../core/ast.js';
import { Q } from '../core/rational.js';
import { linearForm, Poly } from '../core/poly.js';
import { N1, S, T, approxOf, byLang, exactZero, isolated, qGcd, simpOr, tex } from './common.js';
import { subSolve } from './equation.js';
import { isZeroNode, partStep, polyTex, pushPart, solveAnyPoly, sumNode } from './polynomial.js';
import { solveNodePoly, termsOfSum } from './rational.js';
import { mergeRoots } from './roots.js';

// ---------------------------------------------------------------- powers of a common base

export const E_SYM = sym('e');
export const isE = (n) => n.type === 'sym' && n.name === 'e' && !n.var;

/** q = c^k with the smallest c > 1 (k integer, negative for q < 1); q > 0, q ≠ 1. */
function primitivePower(q) {
    if (q.lt(1)) {
        const [c, k] = primitivePower(q.inv());
        return [c, -k];
    }
    const bits = Math.max(q.n.toString(2).length, q.d.toString(2).length);
    for (let k = Math.min(bits, 64); k >= 2; k--) {
        const r = q.exactRoot(k);
        if (r && !r.isOne()) return [r, k];
    }
    return [q, 1];
}

/** base node → {c: Q | 'e', k: Q} with base = c^k, or null. */
export function baseInfo(b) {
    if (b.type === 'num' && b.value.isPos() && !b.value.isOne()) {
        const [c, k] = primitivePower(b.value);
        return { c, k: new Q(BigInt(k)) };
    }
    if (isE(b)) return { c: 'e', k: Q.ONE };
    if (b.type === 'pow' && b.exp.type === 'num') {
        const inner = baseInfo(b.base);
        return inner && { c: inner.c, k: inner.k.mul(b.exp.value) };
    }
    return null;
}

export const sameBase = (a, b) => (a === 'e' || b === 'e' ? a === b : a.eq(b));
export const baseNode = (c) => (c === 'e' ? E_SYM : num(c));

/** R = c^r with rational r → r, else null. */
export function exactPower(c, R) {
    const s = simpOr(R);
    if (s.type === 'num' && s.value.isOne()) return Q.ZERO;
    const bi = s.type === 'num' || isE(s) || s.type === 'pow' ? baseInfo(s) : null;
    if (bi && sameBase(bi.c, c)) return bi.k;
    return null;
}

/** log_c(x) node: ln, lg or log_c. */
export function logNode(c, x) {
    if (c === 'e') return fn('ln', x);
    if (c instanceof Q && c.eq(10)) return fn('lg', x);
    return fn('log', c instanceof Q ? num(c) : c, x);
}

/** log with a base given as a node. */
export function logNodeB(b, x) {
    if (isE(b)) return fn('ln', x);
    if (b.type === 'num' && b.value.eq(10)) return fn('lg', x);
    return fn('log', b, x);
}

// ---------------------------------------------------------------- exponential equations

export function analyzeExp(E, v) {
    let c = null;
    let mixed = false;
    const terms = [];
    const constant = [];
    for (const t of termsOfSum(E)) {
        if (!containsVar(t, v)) {
            constant.push(t);
            continue;
        }
        const fs = t.type === 'mul' ? t.args : [t];
        const coefF = [];
        const gs = [];
        const pows = [];
        for (const f of fs) {
            if (!containsVar(f, v)) {
                coefF.push(f);
                continue;
            }
            if (f.type !== 'pow' || containsVar(f.base, v)) return null;
            const bi = baseInfo(f.base);
            if (!bi) return null;
            if (c === null) c = bi.c;
            else if (!sameBase(c, bi.c)) mixed = true;
            gs.push(simpOr(mul(num(bi.k), f.exp)));
            pows.push(f);
        }
        terms.push({ coef: coefF.length ? simpOr(coefF.length === 1 ? coefF[0] : mul(coefF)) : N1, g: gs.length === 1 ? gs[0] : simpOr(add(gs)), pows, t });
    }
    if (!terms.length) return null;
    return { c, terms, constant: simpOr(sumNode(constant)), mixed };
}

/** a^f · b^f → (ab)^f inside each term (numeric bases), or null when nothing merges. */
function mergeSameExponent(E, v) {
    let changed = false;
    const terms = termsOfSum(E).map((t) => {
        if (t.type !== 'mul') return t;
        const groups = new Map();
        const rest = [];
        for (const f of t.args) {
            if (f.type === 'pow' && f.base.type === 'num' && f.base.value.isPos() && containsVar(f.exp, v)) {
                const k = nodeKey(f.exp);
                const g = groups.get(k);
                if (g) {
                    g.base = g.base.mul(f.base.value);
                    g.n++;
                } else groups.set(k, { base: f.base.value, exp: f.exp, n: 1 });
            } else rest.push(f);
        }
        if (![...groups.values()].some((g) => g.n > 1)) return t;
        changed = true;
        return mul([...rest, ...[...groups.values()].map((g) => pow(num(g.base), g.exp))]);
    });
    return changed ? simpOr(sumNode(terms)) : null;
}

export function solveExponential(lhs, rhs, E, ctx) {
    const v = ctx.v;
    const merged = mergeSameExponent(E, v);
    if (merged) {
        const r = solveExponential(lhs, rhs, merged, ctx);
        if (!r) return null;
        const pre = S(T('Перемножаем степени с одинаковыми показателями', 'Multiply the powers with equal exponents'), {
            tex: byLang((l) => `${tex(merged, l)} = 0`),
            text: T('$a^{f} \\cdot b^{f} = (ab)^{f}$.', '$a^{f} \\cdot b^{f} = (ab)^{f}$.'),
        });
        return { ...r, steps: [pre, ...r.steps] };
    }
    const info = analyzeExp(E, v);
    if (!info) return null;
    if (info.mixed) return solveExpMixed(info, ctx);
    const { c, terms, constant } = info;
    const cN = baseNode(c);
    const steps = [];
    const positive = T('Степень положительного числа всегда положительна — корней нет.', 'A power of a positive number is always positive: no roots.');
    if (terms.length === 1) {
        const { coef, g, pows } = terms[0];
        const R = simpOr(div(neg(constant), coef));
        const single = pows.length === 1;
        const b = single ? pows[0].base : cN;
        const f = single ? pows[0].exp : g;
        const left = single ? pows[0] : pow(cN, g);
        if (!isolated(lhs, rhs, left, R)) steps.push(S(T('Уединяем степень', 'Isolate the power'), { tex: byLang((l) => `${tex(left, l)} = ${tex(R, l)}`) }));
        const Rv = approxOf(R);
        if (!(Rv > 0) || exactZero(R) === true) {
            steps.push(S(T('Справа неположительное число', 'The right side is not positive'), { text: positive }));
            return { kind: 'none', roots: [], steps, type: 'exponential' };
        }
        const rb = single ? exactPower(baseInfo(b).c, R) : null;
        const kb = single ? baseInfo(b).k : Q.ONE;
        const rc = exactPower(c, R);
        let sub;
        if (rc !== null) {
            const rOwn = rc.div(kb); // R = b^(rc/kb)
            const rOwnOk = single && rb !== null;
            if (rOwnOk && (rOwn.isInt() || kb.isOne())) {
                steps.push(S(T(`Записываем правую часть как степень числа $${tex(b)}$`, `Write the right side as a power of $${tex(b, 'en')}$`), {
                    tex: byLang((l) => `${tex(left, l)} = ${tex(pow(b, num(rOwn)), l)}`),
                    text: T('Основания равны — значит, равны и показатели (показательная функция монотонна).', 'The bases are equal, so the exponents are equal too (an exponential function is monotonic).'),
                }));
                sub = subSolve(f, num(rOwn), ctx);
                pushPart(steps, f, num(rOwn), sub, v);
            } else {
                steps.push(S(T(`Приводим обе части к основанию $${tex(cN)}$`, `Write both sides as powers of $${tex(cN, 'en')}$`), {
                    tex: byLang((l) => `${tex(pow(cN, g), l)} = ${tex(pow(cN, num(rc)), l)}`),
                    text: T('Основания равны — приравниваем показатели.', 'The bases are equal, so we equate the exponents.'),
                }));
                sub = subSolve(g, num(rc), ctx);
                pushPart(steps, g, num(rc), sub, v);
            }
        } else {
            const Lg = logNodeB(b, R);
            steps.push(S(T(`Логарифмируем по основанию $${tex(b)}$`, `Take the logarithm to base $${tex(b, 'en')}$`), {
                tex: byLang((l) => `${tex(f, l)} = ${tex(Lg, l)}`),
                text: T(`По определению логарифма: $${tex(b)}^{y} = a \\Leftrightarrow y = ${tex(logNodeB(b, sym('a')))}$.`, `By the definition of the logarithm: $${tex(b, 'en')}^{y} = a \\Leftrightarrow y = ${tex(logNodeB(b, sym('a')), 'en')}$.`),
            }));
            sub = subSolve(f, Lg, ctx);
            pushPart(steps, f, Lg, sub, v);
        }
        if (sub.kind === 'unsupported') return null;
        return { ...sub, steps, type: 'exponential' };
    }
    if (terms.length === 2 && isZeroNode(constant)) {
        const K = simpOr(div(neg(terms[1].coef), terms[0].coef));
        const [g1, g2] = [terms[0].g, terms[1].g];
        const Kv = approxOf(K);
        if (!(Kv > 0)) {
            steps.push(S(T('Степени с разными знаками', 'Powers of opposite signs'), { text: positive }));
            return { kind: 'none', roots: [], steps, type: 'exponential' };
        }
        if (exactZero(add(K, num(-1))) === true) {
            steps.push(S(T(`Приводим обе части к основанию $${tex(cN)}$`, `Write both sides as powers of $${tex(cN, 'en')}$`), {
                tex: byLang((l) => `${tex(pow(cN, g1), l)} = ${tex(pow(cN, g2), l)}`),
                text: T('Основания равны — приравниваем показатели.', 'The bases are equal, so we equate the exponents.'),
            }));
            const sub = subSolve(g1, g2, ctx);
            if (sub.kind === 'unsupported') return null;
            pushPart(steps, g1, g2, sub, v);
            return { ...sub, steps, type: 'exponential' };
        }
        const g = simpOr(add(g1, neg(g2)));
        steps.push(S(T(`Делим обе части на $${tex(pow(cN, g2))}$`, `Divide both sides by $${tex(pow(cN, g2), 'en')}$`), {
            tex: byLang((l) => `${tex(pow(cN, g), l)} = ${tex(K, l)}`),
            text: T('Степень положительна, поэтому делить можно.', 'A power is positive, so the division is allowed.'),
        }));
        const sub = subSolve(pow(cN, g), K, ctx);
        if (sub.kind === 'unsupported') return null;
        steps.push(...sub.steps);
        return { ...sub, steps, type: 'exponential' };
    }
    // substitution t = c^(m·x)
    const lin = [];
    for (const t of terms) {
        const lf = linearForm(t.g, [v]);
        const k = numValue(t.coef);
        if (!lf || !k || lf.coeffs[v].isZero()) return null;
        lin.push({ m: lf.coeffs[v], s: lf.constant, k, t });
    }
    let m = lin[0].m.abs();
    for (const x of lin) m = qGcd(m, x.m.abs());
    const C0 = numValue(constant);
    if (!C0) return null;
    const coefs = new Map();
    let jmin = 0;
    for (const x of lin) {
        const j = x.m.div(m);
        if (!j.isInt()) return null;
        let cs;
        if (x.s.isZero()) cs = Q.ONE;
        else if (c !== 'e' && x.s.isInt()) cs = c.pow(x.s.n);
        else return null;
        const jj = Number(j.n);
        jmin = Math.min(jmin, jj);
        coefs.set(jj, (coefs.get(jj) ?? Q.ZERO).add(x.k.mul(cs)));
    }
    coefs.set(0, (coefs.get(0) ?? Q.ZERO).add(C0));
    const maxJ = Math.max(...coefs.keys());
    if (maxJ - jmin > 8) return null;
    const arr = new Array(maxJ - jmin + 1).fill(Q.ZERO);
    for (const [j, q] of coefs) arr[j - jmin] = arr[j - jmin].add(q);
    const Pt = new Poly(arr);
    if (Pt.degree < 1) return null;
    const Bq = c !== 'e' && m.isInt() ? c.pow(m.n) : null;
    const tNode = Bq ? pow(num(Bq), sym(v)) : pow(cN, simpOr(mul(num(m), sym(v))));
    const tTex = (l) => tex(tNode, l);
    const tSym = sym('t');
    const rewrites = (l) => lin.map((x) => {
        const j = x.m.div(m);
        const cs = x.s.isZero() ? Q.ONE : c.pow(x.s.n);
        const node = simpOr(mul(num(x.k.mul(cs)), pow(tSym, num(j))));
        return `${tex(x.t.t, l)} = ${tex(node, l)}`;
    }).join(l === 'ru' ? ';\\ ' : ',\\ ');
    steps.push(S(T(`Замена $t = ${tTex('ru')}$, где $t > 0$`, `Substitute $t = ${tTex('en')}$, where $t > 0$`), {
        tex: byLang((l) => `${polyTex(Pt, 't', l)} = 0`),
        text: T(`Все степени выражаются через $t$: $${rewrites('ru')}$${jmin < 0 ? `; умножили обе части на $t^{${-jmin}}$ (это не ноль)` : ''}.`, `Every power is expressed through $t$: $${rewrites('en')}$${jmin < 0 ? `; we multiplied both sides by $t^{${-jmin}}$ (it is not zero)` : ''}.`),
    }));
    const tr = solveAnyPoly(Pt, { v: 't', domain: 'real' });
    steps.push(partStep(byLang((l) => `${polyTex(Pt, 't', l)} = 0`), tr, 't'));
    const good = tr.roots.filter((r) => r.approx > 1e-12);
    const bad = tr.roots.filter((r) => !(r.approx > 1e-12));
    if (bad.length) {
        steps.push(S(T('Отбрасываем $t \\le 0$', 'Drop $t \\le 0$'), {
            tex: byLang((l) => bad.map((r) => `t = ${tex(r.node, l)}`).join(',\\ ')),
            text: T(`$${tTex('ru')} > 0$ при любом $${v}$.`, `$${tTex('en')} > 0$ for every $${v}$.`),
        }));
    }
    let roots = [];
    let numeric = !!tr.numeric;
    for (const r of good) {
        const sub = subSolve(tNode, r.node, ctx);
        if (sub.kind === 'unsupported') return null;
        roots.push(...sub.roots);
        if (sub.numeric) numeric = true;
        steps.push(partStep(byLang((l) => `${tTex(l)} = ${tex(r.node, l)}`), sub, v));
    }
    roots = mergeRoots(roots);
    return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'exponential', numeric };
}

/** a^f = K·b^g with different bases: take logarithms of both sides. */
function solveExpMixed(info, ctx) {
    const v = ctx.v;
    const { terms, constant } = info;
    if (terms.length !== 2 || !isZeroNode(constant) || terms.some((t) => t.pows.length !== 1)) return null;
    const [A, B] = terms;
    const K = simpOr(div(neg(B.coef), A.coef));
    const steps = [];
    const left = A.pows[0];
    const right = simpOr(mul(K, B.pows[0]));
    steps.push(S(T('Переносим степени в разные части', 'Put the powers on different sides'), { tex: byLang((l) => `${tex(left, l)} = ${tex(right, l)}`) }));
    if (!(approxOf(K) > 0)) {
        steps.push(S(T('Части разных знаков', 'The sides have opposite signs'), { text: T('Степени положительны, а коэффициент отрицателен — корней нет.', 'The powers are positive and the coefficient is negative: no roots.') }));
        return { kind: 'none', roots: [], steps, type: 'exponential' };
    }
    const lhs2 = mul(left.exp, fn('ln', left.base));
    const rhs2 = add(fn('ln', K), mul(B.pows[0].exp, fn('ln', B.pows[0].base)));
    const l2 = simpOr(lhs2);
    const r2 = simpOr(rhs2);
    steps.push(S(T('Логарифмируем обе части (натуральным логарифмом)', 'Take the natural logarithm of both sides'), {
        tex: byLang((l) => `${tex(l2, l)} = ${tex(r2, l)}`),
        text: T('Обе части положительны, поэтому логарифмировать можно; $\\ln a^{f} = f\\ln a$.', 'Both sides are positive, so we may take logarithms; $\\ln a^{f} = f\\ln a$.'),
    }));
    const E2 = simpOr(add(l2, neg(r2)));
    const sub = solveNodePoly(E2, ctx);
    if (!sub) return null;
    steps.push(...sub.steps);
    return { ...sub, steps, type: 'exponential' };
}
