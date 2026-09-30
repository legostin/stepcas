// solve/logarithmic — logarithmic equations.

import { Q } from '../core/rational.js';
import { num, containsVar, numValue, mul, pow, nodeSome, add, fn, div, neg, nodeKey } from '../core/ast.js';
import { Poly } from '../core/poly.js';
import { N0, N1, S, T, approxOf, byLang, expd, isConstNode, isolated, outermost, simpOr, tex } from './common.js';
import { subSolve } from './equation.js';
import { E_SYM, baseInfo, baseNode, isE, logNode, sameBase } from './exponential.js';
import { isZeroNode, partStep, polyTex, pushPart, solveAnyPoly, sumNode } from './polynomial.js';
import { termsOfSum } from './rational.js';
import { mergeRoots } from './roots.js';

// ---------------------------------------------------------------- logarithmic equations

function logInfoOf(f, v) {
    if (f.type !== 'fn') return null;
    if (f.name === 'ln') return { c: 'e', k: Q.ONE, arg: f.args[0], base: E_SYM };
    if (f.name === 'lg') return { c: new Q(10n), k: Q.ONE, arg: f.args[0], base: num(10) };
    if (f.name !== 'log') return null;
    const b = f.args[0];
    if (containsVar(b, v)) return { varBase: true, arg: f.args[1], base: b };
    const bi = baseInfo(b);
    return bi && { c: bi.c, k: bi.k, arg: f.args[1], base: b };
}

export function analyzeLog(E, v) {
    const vt = [];
    const constant = [];
    for (const t of termsOfSum(E)) {
        if (!containsVar(t, v)) {
            constant.push(t);
            continue;
        }
        const fs = t.type === 'mul' ? t.args : [t];
        const withV = fs.filter((f) => containsVar(f, v));
        if (withV.length !== 1) return null;
        let F = withV[0];
        let p = 1;
        if (F.type === 'pow') {
            const e = numValue(F.exp);
            if (!e || !e.isInt() || !e.isPos() || e.gt(6)) return null;
            p = Number(e.n);
            F = F.base;
        }
        const info = logInfoOf(F, v);
        if (!info || !containsVar(F, v)) return null;
        const rest = fs.filter((f) => !containsVar(f, v));
        vt.push({ coef: rest.length ? simpOr(rest.length === 1 ? rest[0] : mul(rest)) : N1, p, F, info, t });
    }
    if (!vt.length) return null;
    return { vt, constant };
}

/**
 * A common exponential factor: x²·2ˣ − 4·2ˣ = 0 → 2ˣ(x² − 4) = 0, and 2ˣ > 0 is never zero, so x² − 4 = 0.
 * Only when dividing it out leaves no power with the unknown in the exponent.
 */
export function solveCommonExp(lhs, rhs, E, ctx) {
    const v = ctx.v;
    if (E.type !== 'add') return null;
    const varExp = (n) => n.type === 'pow' && !containsVar(n.base, v) && containsVar(n.exp, v) && ((n.base.type === 'num' && n.base.value.isPos() && !n.base.value.isOne()) || isE(n.base));
    const first = E.args[0].type === 'mul' ? E.args[0].args : [E.args[0]];
    for (const F of first.filter(varExp)) {
        const rest = expd(mul(E, pow(F, num(-1))));
        if (!rest || !containsVar(rest, v) || nodeSome(rest, (n) => n.type === 'pow' && containsVar(n.exp, v))) continue;
        const steps = [S(byLang((l) => (l === 'ru' ? `Выносим $${tex(F, l)}$ за скобки` : `Take $${tex(F, l)}$ out of the brackets`)), {
            tex: byLang((l) => `${tex(F, l)}\\left(${tex(rest, l)}\\right) = 0`),
            text: byLang((l) => (l === 'ru'
                ? `Показательная функция всегда положительна: $${tex(F, l)} > 0$, поэтому этот множитель нулю не равен и на него можно разделить: $${tex(rest, l)} = 0$.`
                : `An exponential is always positive: $${tex(F, l)} > 0$, so this factor is never zero and we may divide by it: $${tex(rest, l)} = 0$.`)),
        })];
        const sub = subSolve(rest, N0, ctx);
        if (sub.kind === 'unsupported' || sub.numeric) return null;
        steps.push(...sub.steps);
        return { ...sub, steps };
    }
    return null;
}

/**
 * A power with the unknown both in the base and in the exponent (x^(lg x) = 100x): take the logarithm of both
 * sides. The base is positive by the ОДЗ, so that side is positive and the other must be too; log turns
 * powers into products and products into sums. The roots are checked in the original equation afterwards.
 */
export function solveTakeLog(lhs, rhs, E, ctx) {
    const v = ctx.v;
    const varPow = (n) => n.type === 'pow' && containsVar(n.base, v) && containsVar(n.exp, v);
    if (!nodeSome(E, varPow) && !nodeSome(lhs, varPow) && !nodeSome(rhs, varPow)) return null;
    // the logarithm the equation already speaks: lg, ln, log_a; lg by default
    let base = num(10);
    let lname = 'lg';
    const lf = outermost(add(lhs, rhs), (n) => n.type === 'fn' && (n.name === 'lg' || n.name === 'ln' || (n.name === 'log' && isConstNode(n.args[0]))))[0];
    if (lf?.name === 'ln') [base, lname] = [E_SYM, 'ln'];
    else if (lf?.name === 'log') [base, lname] = [lf.args[0], 'log'];
    const L = (x) => (lname === 'log' ? fn('log', base, x) : fn(lname, x));
    const positive = (n) => {
        if (n.type === 'num') return n.value.isPos();
        if (n.type === 'mul') return n.args.every(positive);
        if (n.type === 'pow') return (n.base.type === 'num' && n.base.value.isPos()) || (containsVar(n.base, v) && containsVar(n.exp, v)) || isE(n.base);
        return isE(n);
    };
    const logOf = (n) => {
        if (n.type === 'mul') {
            const parts = n.args.map(logOf);
            return parts.some((x) => !x) ? null : add(parts);
        }
        if (n.type === 'pow') {
            const b = logOf(n.base);
            return b && mul(n.exp, b);
        }
        if (n.type === 'num') return n.value.isPos() ? simpOr(L(n)) : null;
        return L(n);
    };
    const A = simpOr(lhs);
    const B = simpOr(rhs);
    if (!positive(A) && !positive(B)) return null;
    const LA = logOf(A);
    const LB = logOf(B);
    if (!LA || !LB) return null;
    const L1 = simpOr(expd(LA) ?? LA);
    const L2 = simpOr(expd(LB) ?? LB);
    const lt = (l) => (lname === 'ln' ? '\\ln' : lname === 'lg' ? (l === 'ru' ? '\\lg' : '\\log_{10}') : `\\log_{${tex(base, l)}}`);
    const steps = [S(T('Логарифмируем обе части', 'Take the logarithm of both sides'), {
        tex: byLang((l) => `${tex(L1, l)} = ${tex(L2, l)}`),
        text: T(`Основание степени с переменным показателем положительно (ОДЗ), значит, обе части положительны и от них можно взять $${lt('ru')}$. Логарифм степени — произведение: $${lt('ru')} a^{b} = b\\,${lt('ru')} a$, логарифм произведения — сумма.`,
            `The base of a power with a variable exponent is positive (the domain), so both sides are positive and we may take $${lt('en')}$ of them. The logarithm of a power is a product, $${lt('en')} a^{b} = b\\,${lt('en')} a$, and of a product a sum.`),
    })];
    const sub = subSolve(L1, L2, ctx);
    if (sub.kind === 'unsupported' || sub.numeric) return null;
    steps.push(...sub.steps);
    return { ...sub, steps, type: 'logarithmic' };
}

export function solveLogarithmic(lhs, rhs, E, ctx) {
    const v = ctx.v;
    const an = analyzeLog(E, v);
    if (!an) return null;
    const { vt, constant } = an;
    const C = simpOr(sumNode(constant));
    const steps = [];
    const defText = T('По определению логарифма: $\\log_a b = c \\Leftrightarrow b = a^{c}$.', 'By the definition of the logarithm: $\\log_a b = c \\Leftrightarrow b = a^{c}$.');
    // a variable base: log_f(g) = R
    if (vt.some((x) => x.info.varBase)) {
        if (vt.length !== 1 || vt[0].p !== 1) return null;
        const { coef, info, F } = vt[0];
        const R = simpOr(div(neg(C), coef));
        if (!isConstNode(R)) return null;
        if (!isolated(lhs, rhs, F, R)) steps.push(S(T('Уединяем логарифм', 'Isolate the logarithm'), { tex: byLang((l) => `${tex(F, l)} = ${tex(R, l)}`) }));
        const l2 = expd(pow(info.base, R)) ?? pow(info.base, R);
        steps.push(S(T('Переходим к степени', 'Rewrite as a power'), { tex: byLang((l) => `${tex(l2, l)} = ${tex(info.arg, l)}`), text: defText }));
        const sub = subSolve(l2, info.arg, ctx);
        if (sub.kind === 'unsupported') return null;
        pushPart(steps, l2, info.arg, sub, v);
        return { ...sub, steps, type: 'logarithmic' };
    }
    const c = vt[0].info.c;
    if (vt.some((x) => !sameBase(x.info.c, c))) return null;
    const cN = baseNode(c);
    const args = new Set(vt.map((x) => nodeKey(x.info.arg)));
    const normalize = vt.some((x) => !x.info.k.isOne()) || new Set(vt.map((x) => nodeKey(x.info.base))).size > 1;
    // one argument: log_b(u) = R, or a polynomial in t = log_c(u)
    if (args.size === 1) {
        const u = vt[0].info.arg;
        if (vt.length === 1 && vt[0].p === 1) {
            const { coef, info, F } = vt[0];
            const R = simpOr(div(neg(C), coef));
            if (!isConstNode(R)) return null;
            if (!isolated(lhs, rhs, F, R)) steps.push(S(T('Уединяем логарифм', 'Isolate the logarithm'), { tex: byLang((l) => `${tex(F, l)} = ${tex(R, l)}`) }));
            const val = simpOr(pow(info.base, R));
            steps.push(S(T('Переходим от логарифма к степени', 'Go from the logarithm to a power'), {
                tex: byLang((l) => `${tex(u, l)} = ${tex(pow(info.base, R), l)}${nodeKey(val) !== nodeKey(pow(info.base, R)) ? ` = ${tex(val, l)}` : ''}`),
                text: defText,
            }));
            const sub = subSolve(u, val, ctx);
            if (sub.kind === 'unsupported') return null;
            pushPart(steps, u, val, sub, v);
            return { ...sub, steps, type: 'logarithmic' };
        }
        // polynomial in t
        const coefs = new Map();
        for (const x of vt) {
            const k = numValue(x.coef);
            if (!k) return null;
            const q = k.div(x.info.k.pow(x.p));
            coefs.set(x.p, (coefs.get(x.p) ?? Q.ZERO).add(q));
        }
        const C0 = numValue(C);
        if (!C0) return null;
        coefs.set(0, (coefs.get(0) ?? Q.ZERO).add(C0));
        const arr = new Array(Math.max(...coefs.keys()) + 1).fill(Q.ZERO);
        for (const [j, q] of coefs) arr[j] = q;
        const Pt = new Poly(arr);
        if (Pt.degree < 1) return null;
        const tN = logNode(c, u);
        steps.push(S(T(`Замена $t = ${tex(tN)}$`, `Substitute $t = ${tex(tN, 'en')}$`), {
            tex: byLang((l) => `${polyTex(Pt, 't', l)} = 0`),
            text: normalize ? T(`Логарифмы по разным основаниям переводим к основанию $${tex(cN)}$: $\\log_{a^k} u = \\frac{1}{k}\\log_a u$.`, `Logarithms to different bases are converted to base $${tex(cN, 'en')}$: $\\log_{a^k} u = \\frac{1}{k}\\log_a u$.`) : undefined,
        }));
        const tr = solveAnyPoly(Pt, { v: 't', domain: 'real' });
        steps.push(partStep(byLang((l) => `${polyTex(Pt, 't', l)} = 0`), tr, 't'));
        let roots = [];
        for (const r of tr.roots) {
            const val = simpOr(pow(cN, r.node));
            const sub = subSolve(u, val, ctx);
            if (sub.kind === 'unsupported') return null;
            roots.push(...sub.roots);
            steps.push(partStep(byLang((l) => `${tex(tN, l)} = ${tex(r.node, l)} \\quad\\Rightarrow\\quad ${tex(u, l)} = ${tex(val, l)}`), sub, v));
        }
        roots = mergeRoots(roots);
        return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'logarithmic' };
    }
    // several arguments: combine into one logarithm
    if (vt.some((x) => x.p !== 1)) return null;
    const ups = [];
    const downs = [];
    for (const x of vt) {
        const k = numValue(x.coef);
        if (!k) return null;
        const a = k.div(x.info.k);
        const piece = a.abs().isOne() ? x.info.arg : pow(x.info.arg, num(a.abs()));
        (a.isPos() ? ups : downs).push(piece);
    }
    // constant logarithms of the same base go to the right side as one logarithm
    const cUps = [];
    const cDowns = [];
    const rest = [];
    for (const t of constant) {
        const fs = t.type === 'mul' ? t.args : [t];
        const lg = fs.filter((f) => f.type === 'fn' && logInfoOf(f, v) && !logInfoOf(f, v).varBase);
        const k = numValue(simpOr(mul(fs.filter((f) => !lg.includes(f)).length ? fs.filter((f) => !lg.includes(f)) : [N1])));
        if (lg.length === 1 && k) {
            const info = logInfoOf(lg[0], v);
            if (sameBase(info.c, c)) {
                const a = k.div(info.k).neg();
                const piece = a.abs().isOne() ? info.arg : pow(info.arg, num(a.abs()));
                (a.isPos() ? cUps : cDowns).push(piece);
                continue;
            }
        }
        rest.push(t);
    }
    const R = simpOr(neg(sumNode(rest)));
    const prod = (xs) => (xs.length ? (xs.length === 1 ? xs[0] : mul(xs)) : N1);
    const F = downs.length ? div(prod(ups), prod(downs)) : prod(ups);
    const G = cDowns.length ? div(prod(cUps), prod(cDowns)) : prod(cUps);
    const Gs = simpOr(G);
    const hasG = !(Gs.type === 'num' && Gs.value.isOne());
    const K = simpOr(mul(Gs, pow(cN, R)));
    const logF = logNode(c, F);
    const rightT = (l) => (hasG ? (isZeroNode(R) ? tex(logNode(c, Gs), l) : `${tex(logNode(c, Gs), l)} ${approxOf(R) < 0 ? '' : '+'} ${tex(R, l)}`) : tex(R, l));
    const simpleEq = vt.length === 2 && !hasG && isZeroNode(R) && ups.length === 1 && downs.length === 1 && vt.every((x) => numValue(x.coef)?.abs().isOne() && x.info.k.isOne());
    if (simpleEq) {
        steps.push(S(T('Логарифмы с равными основаниями равны — равны и их аргументы', 'Equal logarithms to the same base: the arguments are equal'), {
            tex: byLang((l) => `${tex(ups[0], l)} = ${tex(downs[0], l)}`),
            text: T('Логарифмическая функция монотонна. Переход не учитывает ОДЗ — корни проверим по ней.', 'The logarithm is monotonic. This step ignores the domain, so we check the roots against it.'),
        }));
        const sub = subSolve(ups[0], downs[0], ctx);
        if (sub.kind === 'unsupported') return null;
        pushPart(steps, ups[0], downs[0], sub, v);
        return { ...sub, steps, type: 'logarithmic' };
    }
    steps.push(S(T('Собираем логарифмы в один', 'Combine the logarithms into one'), {
        tex: byLang((l) => `${tex(logF, l)} = ${rightT(l)}`),
        text: T(`Свойства: $\\log_a m + \\log_a n = \\log_a(mn)$, $\\log_a m - \\log_a n = \\log_a\\frac{m}{n}$, $k\\log_a m = \\log_a m^{k}$. Они верны при $m, n > 0$, поэтому корни потом сверим с ОДЗ.${normalize ? ` Логарифмы переведены к основанию $${tex(cN)}$.` : ''}`,
            `The rules $\\log_a m + \\log_a n = \\log_a(mn)$, $\\log_a m - \\log_a n = \\log_a\\frac{m}{n}$, $k\\log_a m = \\log_a m^{k}$ hold for $m, n > 0$, so we check the roots against the domain later.${normalize ? ` All logarithms are converted to base $${tex(cN, 'en')}$.` : ''}`),
    }));
    steps.push(S(T('Переходим от логарифма к аргументам', 'Pass from the logarithms to their arguments'), {
        tex: byLang((l) => `${tex(F, l)} = ${tex(K, l)}`),
        text: defText,
    }));
    const sub = subSolve(F, K, ctx);
    if (sub.kind === 'unsupported') return null;
    pushPart(steps, F, K, sub, v);
    return { ...sub, steps, type: 'logarithmic' };
}
