// solve/signs — sign charts: the method of intervals.

import { numDen } from '../core/expand.js';
import { Poly } from '../core/poly.js';
import { Q } from '../core/rational.js';
import { containsVar } from '../core/ast.js';
import { approxNode, approxOf, simp, texB } from './common.js';
import { relHoldsNum } from './domain.js';
import { IntervalSet, endOf } from './intervals.js';
import { solveAnyPoly } from './polynomial.js';
import { polyLcm, termsOfSum } from './rational.js';
import { mergeRoots, sameRoot } from './roots.js';

// ---------------------------------------------------------------- sign charts (the method of intervals)

/** Sum of polynomial fractions → {N, L} with E = N / L (L primitive, no cancelling), or null. */
export function ratParts(E, v) {
    const parts = [];
    for (const t of termsOfSum(E)) {
        let nd;
        try {
            nd = numDen(t);
        } catch {
            return null;
        }
        const Pn = Poly.fromNode(nd.num, v);
        const Pd = Poly.fromNode(nd.den, v);
        if (!Pn || !Pd || Pd.isZero()) return null;
        parts.push({ Pn, Pd });
    }
    let L = new Poly([Q.ONE]);
    for (const p of parts) L = polyLcm(L, p.Pd.monic());
    let N = new Poly([]);
    for (const p of parts) {
        const { q, r } = L.divmod(p.Pd);
        if (!r.isZero()) return null;
        N = N.add(p.Pn.mul(q));
    }
    const Lp = L.primitive();
    return { N: N.scale(Lp.lead.div(L.lead)), L: Lp };
}

/** Distinct real roots with multiplicities (square-free decomposition, so numeric roots get them right too). */
export function realRootsMult(P, v) {
    if (P.degree < 1) return [];
    const out = [];
    for (const { poly, mult } of P.squareFree()) {
        const r = solveAnyPoly(poly, { v, domain: 'real' });
        for (const x of r.roots) out.push({ ...x, mult });
    }
    return mergeRoots(out, true);
}

function testPoint(a, b) {
    if (a === null && b === null) return Q.ZERO;
    if (a === null) return Q.of(Math.floor(b.approx) - 1);
    if (b === null) return Q.of(Math.ceil(a.approx) + 1);
    const m = (a.approx + b.approx) / 2;
    return Q.of(Number(m.toPrecision(15)).toString());
}

/** Sign chart of N/L: {points: [{node, approx, kind, mN, mL, approxOnly}], signs: [+1|-1, …]} */
export function chartOf(N, L, v) {
    const zn = realRootsMult(N, v);
    const zl = L ? realRootsMult(L, v) : [];
    const pts = [];
    for (const r of zn) pts.push({ node: r.node, approx: r.approx, approxOnly: r.approxOnly, mN: r.mult, mL: 0 });
    for (const r of zl) {
        const p = pts.find((x) => sameRoot(x, r));
        if (p) p.mL = r.mult;
        else pts.push({ node: r.node, approx: r.approx, approxOnly: r.approxOnly, mN: 0, mL: r.mult });
    }
    pts.sort((a, b) => a.approx - b.approx);
    const signs = [];
    for (let k = 0; k <= pts.length; k++) {
        const t = testPoint(k ? pts[k - 1] : null, k < pts.length ? pts[k] : null);
        const a = N.evalAt(t).sign();
        const b = L ? L.evalAt(t).sign() : 1;
        signs.push(a * b);
    }
    for (const p of pts) p.kind = p.mL > 0 ? 'pole' : 'zero';
    return { points: pts, signs };
}

/** The set where N/L op 0 (op: > >= < <= != =) from its chart. */
export function setFromChart(chart, op) {
    const { points: pts, signs } = chart;
    const want = op === '>' || op === '>=' ? 1 : op === '<' || op === '<=' ? -1 : null;
    const parts = [];
    for (let k = 0; k <= pts.length; k++) {
        const s = signs[k];
        if ((want !== null && s === want) || (op === '!=' && s !== 0)) {
            parts.push({ lo: k ? endOfPoint(pts[k - 1]) : null, hi: k < pts.length ? endOfPoint(pts[k]) : null, loC: false, hiC: false });
        }
    }
    if (op === '>=' || op === '<=' || op === '=') {
        for (const p of pts) if (p.kind === 'zero') {
            const e = endOfPoint(p);
            parts.push({ lo: e, hi: e, loC: true, hiC: true });
        }
    }
    for (const p of pts) p.included = (op === '>=' || op === '<=' || op === '=') && p.kind === 'zero';
    return new IntervalSet(parts);
}

/** Endpoint of a chart point: exact, or a short decimal marked approx. */
function endOfPoint(p) {
    if (!p.approxOnly) return endOf(p.node);
    return Object.freeze({ node: approxNode(p.approx, 5), x: p.approx, q: null, approx: true });
}

/** Public chart shape for widgets. */
export function chartOut(chart) {
    return {
        points: chart.points.map((p) => ({ x: p.approx, tex: p.approxOnly ? texB(approxNode(p.approx, 5), { decimals: true }) : texB(p.node), kind: p.kind, included: !!p.included, mult: p.kind === 'pole' ? p.mL : p.mN, approx: !!p.approxOnly })),
        signs: chart.signs.map((s) => (s > 0 ? '+' : s < 0 ? '-' : '0')),
    };
}

/** Silent: the set where expr op 0 for rational expr (null when not rational). */
export function signSet(expr, op, v) {
    const s = simp(expr);
    if (!s) return null;
    if (!containsVar(s, v)) {
        const x = approxOf(s);
        if (!Number.isFinite(x)) return null;
        return relHoldsNum(op, x, 0) ? IntervalSet.all() : IntervalSet.empty();
    }
    const rp = ratParts(s, v);
    if (!rp || rp.N.isZero()) return rp && rp.N.isZero() ? (op === '>=' || op === '<=' || op === '=' ? IntervalSet.all() : IntervalSet.empty()).minus(IntervalSet.points(realRootsMult(rp.L, v).map((r) => r.node))) : null;
    return setFromChart(chartOf(rp.N, rp.L.degree >= 1 ? rp.L : null, v), op);
}
