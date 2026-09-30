// integral/substitution — u-substitution g(h(x))·h′(x) and the rationalising substitution t = ⁿ√(ax + b).

import { containsVar, nodeKey, pow, sym, num, nodeChildren, div, nodeSome, substitute, add, mapNode, mul, nodeSize, neg } from '../../core/ast.js';
import { Poly } from '../../core/poly.js';
import { quickDerivative, ratFunctionOf } from '../derivative.js';
import { bigLcm } from '../../core/rational.js';
import { mapPre, plainish } from './basic.js';
import { E_, NM1, T_, freshVar, isNum, isOne, isVar, isZero, linearParts, paren, q, simp, trySimp, tx } from './common.js';
import { qn } from './rational.js';
import { substResult } from './trig.js';

// ---- u-substitution g(h(x))·h′(x)

function subCandidates(f, v) {
    const out = new Map();
    const visit = (n) => {
        if (!containsVar(n, v)) return;
        if (n !== f && !isVar(n, v)) out.set(nodeKey(n), n);
        if (n.type === 'pow' && containsVar(n.base, v) && !isVar(n.base, v)) out.set(nodeKey(n.base), n.base);
        // x/(x⁴ + 1): the helpful t = x² is not written anywhere, only its square x⁴
        if (n.type === 'pow' && isVar(n.base, v) && isNum(n.exp) && n.exp.value.isInt()) {
            const k = Number(n.exp.value.n);
            for (let d = 2; d <= k / 2 && k <= 24; d++) {
                if (k % d) continue;
                const u = pow(sym(v), num(d));
                out.set(nodeKey(u), u);
            }
        }
        for (const c of nodeChildren(n)) visit(c);
    };
    visit(f);
    return [...out.values()].filter((u) => !linearParts(u, v));
}

function replaceU(r, u, t, v) {
    const key = nodeKey(u);
    const T = sym(t);
    const expBase = u.type === 'pow' && !containsVar(u.base, v) ? u.base : null;
    const powW = u.type === 'pow' && isNum(u.exp) ? u.base : null;
    const powP = powW ? u.exp.value : null;
    const rootLike = powP && !powP.isInt();
    let g = mapPre(r, (m) => {
        if (nodeKey(m) === key) return T;
        if (expBase && m.type === 'pow' && nodeKey(m.base) === nodeKey(expBase) && containsVar(m.exp, v)) {
            const ratio = trySimp(div(m.exp, u.exp));
            if (ratio && isNum(ratio)) return pow(T, ratio);
        }
        if (powW && m.type === 'pow' && nodeKey(m.base) === nodeKey(powW) && isNum(m.exp)) {
            const e = m.exp.value.div(powP);
            if (rootLike || e.isInt()) return pow(T, num(e));
        }
        if (powW && rootLike && nodeKey(m) === nodeKey(powW)) return pow(T, num(powP.inv()));
        return undefined;
    });
    g = trySimp(g);
    if (!g) return null;
    if (containsVar(g, v) && u.type === 'fn' && u.name === 'ln' && isVar(u.args[0], v)
        && nodeSome(r, (m) => m.type === 'fn' && m.name !== 'ln' && nodeSome(m.args[0], (k) => nodeKey(k) === key))) {
        // cos(ln x): with t = ln x the leftover x is eᵗ (x·ln x is left to parts)
        g = trySimp(substitute(g, { [v]: pow(E_, T) }));
        return g && !containsVar(g, v) ? g : null;
    }
    if (containsVar(g, v)) {
        // u = a·v^k + b: v^m → ((t − b)/a)^(m/k) when k | m
        const P = Poly.fromNode(u, v);
        if (!P || P.degree < 2) return null;
        const nz = P.c.map((c, i) => (c.isZero() ? -1 : i)).filter((i) => i >= 0);
        if (nz.length > 2 || (nz.length === 2 && nz[0] !== 0)) return null;
        const kdeg = P.degree;
        const a = P.lead;
        const b = P.coeff(0);
        const back = div(add(T, qn(b.neg())), qn(a));
        g = mapNode(g, (m) => {
            if (m.type === 'pow' && isVar(m.base, v) && isNum(m.exp) && m.exp.value.isInt() && m.exp.value.n % BigInt(kdeg) === 0n) return pow(back, num(m.exp.value.div(kdeg)));
            return undefined;
        });
        g = trySimp(g);
        if (!g || containsVar(g, v)) return null;
    }
    return g;
}

export function mUSub(f, ctx) {
    const { v } = ctx;
    if (f.type === 'add') return null;
    const t = freshVar(f, v);
    const cands = [];
    for (const u of subCandidates(f, v)) {
        let du;
        try {
            du = simp(quickDerivative(u, v));
        } catch {
            continue;
        }
        if (isZero(du)) continue;
        const r = trySimp(mul(f, pow(du, NM1)));
        if (!r) continue;
        const g = replaceU(r, u, t, v);
        if (!g || containsVar(g, v)) continue;
        if (nodeKey(substitute(g, { [t]: sym(v) })) === nodeKey(f)) continue;
        cands.push({ u, du, g, size: nodeSize(g) });
    }
    // prefer a substitution that leaves an integral in t (t = x² for x·e^(x²)), then the simplest one
    const isConstG = (c) => !containsVar(c.g, t);
    cands.sort((a, b) => isConstG(a) - isConstG(b) || a.size - b.size || nodeSize(b.u) - nodeSize(a.u));
    for (const c of cands.slice(0, 5)) {
        const res = substResult(f, ctx, {
            t, uNode: c.u, g: c.g, rule: 'substitution',
            title: T_('Замена переменной', 'Substitution'),
            dtTex: (L) => `d${t} = ${isOne(c.du) ? '' : c.du.type === 'add' ? paren(tx(c.du, L)) : tx(c.du, L) + '\\,'}d${v}`,
            text: T_(`Замечаем, что производная выражения ${plainish(c.u, 'ru')} (с точностью до постоянного множителя) уже стоит множителем под интегралом. Делаем замену ${t} = ${plainish(c.u, 'ru')}: интеграл превращается в более простой.`,
                `The derivative of ${plainish(c.u, 'en')} is (up to a constant factor) already a factor of the integrand. Substitute ${t} = ${plainish(c.u, 'en')}: the integral becomes simpler.`),
        });
        if (res) return res;
    }
    return null;
}

// ---- rationalising substitution t = ⁿ√(ax + b)

export function mRationalizing(f, ctx) {
    const { v } = ctx;
    let base = null;
    let den = 1n;
    let ok = true;
    const visit = (n) => {
        if (n.type === 'pow' && isNum(n.exp) && !n.exp.value.isInt() && containsVar(n.base, v)) {
            if (base && nodeKey(base) !== nodeKey(n.base)) ok = false;
            base = n.base;
            den = bigLcm(den, n.exp.value.d);
        }
        for (const c of nodeChildren(n)) visit(c);
    };
    visit(f);
    if (!ok || !base || den < 2n || den > 12n) return null;
    const lp = linearParts(base, v);
    if (!lp || !isNum(lp.k) || !isNum(lp.b)) return null;
    const m = Number(den);
    const t = freshVar(f, v);
    const T = sym(t);
    const xOfT = div(add(pow(T, num(m)), neg(lp.b)), lp.k);
    let g = trySimp(mul(substitute(f, { [v]: xOfT }), div(mul(num(m), pow(T, num(m - 1))), lp.k)));
    if (!g) return null;
    g = trySimp(mapNode(g, (x) => (x.type === 'fn' && x.name === 'abs' && isVar(x.args[0], t) ? T : undefined)));
    if (!g || !ratFunctionOf(g, t)) return null;
    const uNode = pow(base, num(q(1, m)));
    return substResult(f, ctx, {
        t, uNode, g, rule: 'rationalizing',
        title: T_('Замена, убирающая корень', 'A substitution that removes the root'),
        dtTex: (L) => `${v} = ${tx(trySimp(xOfT) ?? xOfT, L)},\\ d${v} = ${tx(simp(div(mul(num(m), pow(T, num(m - 1))), lp.k)), L)}\\,d${t}`,
        text: T_(`Все корни — из одного и того же линейного выражения ${plainish(base, 'ru')}. Заменяем t = ${m === 2 ? '√' : `${m}-й корень из `}(${plainish(base, 'ru')}): корни исчезают, остаётся рациональная дробь от t.`,
            `All roots are of the same linear expression ${plainish(base, 'en')}. Substitute t = ${m === 2 ? '√' : `the ${m}-th root of `}(${plainish(base, 'en')}): the roots disappear and a rational function of t is left.`),
    });
}
