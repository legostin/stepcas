// calculus/limit/table — the table of values approaching the point and the numeric cross-check.

import { step } from '../../core/steps.js';
import { HS, atPoint, evalAt } from './common.js';
import { plainNum } from './forms.js';
import { msg, eachLanguage, decimalIn } from '../../i18n/index.js';

// ---------------------------------------------------------------- numeric table and check

function numPoints(P) {
    if (!Number.isFinite(P.x)) return [10, 100, 1e3, 1e4, 1e5, 1e6].map((t) => (P.x > 0 ? t : -t));
    const scale = Math.max(1, Math.abs(P.x));
    const hs = [0.1, 0.01, 0.001, 1e-4, 1e-5, 1e-6];
    return hs.map((h) => (P.side === 'left' ? P.x - h * scale : P.x + h * scale));
}

export function tableFor(n, v, P) {
    const sides = P.side === 'both' && Number.isFinite(P.x) ? ['left', 'right'] : [P.side];
    const rows = [];
    for (const side of sides) {
        for (const x of numPoints({ ...P, side })) rows.push({ x, fx: evalAt(n, v, x), side: Number.isFinite(P.x) ? side : null });
    }
    return rows;
}

/** A numeric estimate on one side: {k: 'fin', x} | {k: 'inf', s} | null. */
export function numericEstimate(n, v, P) {
    const xs = !Number.isFinite(P.x) ? [1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8].map((t) => (P.x > 0 ? t : -t)) : [1e-1, ...HS].map((h) => atPoint(P, h));
    const ys = xs.map((x) => evalAt(n, v, x));
    const fins = ys.filter(Number.isFinite);
    if (fins.length < 4) return null;
    // growth like c/xᵏ: the same sign, no zeros, a steady growth ratio (round-off noise has none of these)
    const tail = ys.slice(-5);
    if (tail.every((y) => Number.isFinite(y) && y !== 0 && Math.sign(y) === Math.sign(tail[0])) && Math.abs(tail[tail.length - 1]) > 1e4) {
        const r = tail.slice(1).map((y, i) => Math.abs(y / tail[i]));
        if (r.every((q) => q > 1.5) && Math.max(...r) / Math.min(...r) < 3) return { k: 'inf', s: Math.sign(tail[0]) };
    }
    // the clean prefix: while the differences keep shrinking the values converge; once they stop, round-off
    // (or divergence) has taken over and the rest is ignored
    const pre = [];
    for (const y of ys) {
        if (!Number.isFinite(y)) {
            if (pre.length) break;
            continue;
        }
        pre.push(y);
        if (pre.length >= 3) {
            const d1 = Math.abs(pre[pre.length - 2] - pre[pre.length - 3]);
            const d2 = Math.abs(pre[pre.length - 1] - pre[pre.length - 2]);
            if (d2 > 1.1 * d1 && d2 > 1e-12 * Math.max(1, Math.abs(pre[pre.length - 1]))) {
                pre.pop();
                break;
            }
        }
    }
    if (pre.length < 3) return null;
    // geometric convergence (x^(−2/3), e^(−x)…): Aitken's Δ² on the last four clean values
    if (pre.length >= 4) {
        const [y0, y1, y2, y3] = pre.slice(-4);
        const d0 = y1 - y0;
        const d1 = y2 - y1;
        const d2 = y3 - y2;
        const r1 = d1 / d0;
        const r2 = d2 / d1;
        const geometric = d0 !== 0 && d1 !== 0 && r1 > 0 && r2 > 0 && r1 < 0.8 && r2 < 0.8 && Math.abs(r1 - r2) <= 0.01 * Math.max(r1, r2);
        if (geometric && Math.abs(d2 - d1) > 1e-300) {
            const Lx = y3 - (d2 * d2) / (d2 - d1);
            const scale = Math.max(1, Math.abs(y1));
            if (Number.isFinite(Lx) && Math.abs(Lx - y3) < 0.5 * scale) return { k: 'fin', x: Math.abs(Lx) < 1e-9 * scale ? 0 : Lx };
        }
    }
    const a = pre[pre.length - 1];
    const dLast = Math.abs(a - pre[pre.length - 2]);
    if (dLast < 1e-4 * Math.max(1, Math.abs(a))) return { k: 'fin', x: a };
    return null;
}

/** Does the numeric behaviour agree with the symbolic value on this side? 'agree' | 'contradict' | 'unclear' */
export function crossCheck(n, v, P, val) {
    const est = numericEstimate(n, v, P);
    const xs = !Number.isFinite(P.x)
        ? [1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e10, 1e12].map((t) => (P.x > 0 ? t : -t))
        : [...HS, 1e-9, 1e-10, 1e-12, 1e-14].map((h) => atPoint(P, h)).filter((x) => x !== P.x);
    const ys = xs.map((x) => evalAt(n, v, x));
    if (val.k === 'fin') {
        const L = val.x;
        if (!Number.isFinite(L)) return 'unclear';
        const errs = ys.filter(Number.isFinite).map((y) => Math.abs(y - L));
        if (errs.some((e) => e <= 1e-4 * Math.max(1, Math.abs(L)))) return 'agree';
        if (est && est.k === 'fin' && Math.abs(est.x - L) > 1e-3 * Math.max(1, Math.abs(L))) return 'contradict';
        if (est && est.k === 'inf') return 'contradict';
        return 'unclear';
    }
    if (val.k === 'inf') {
        const fy = ys.filter(Number.isFinite);
        const lastBig = fy.slice(-3);
        if (lastBig.length && lastBig.every((y) => Math.sign(y) === val.s) && Math.abs(lastBig[lastBig.length - 1]) > 100) return 'agree';
        const tail = fy.slice(-5);
        if (
            tail.length >= 4 &&
            tail.every((y, i) => Math.sign(y) === val.s && (i === 0 || Math.abs(y) > Math.abs(tail[i - 1]))) &&
            Math.abs(tail[tail.length - 1]) > 10
        )
            return 'agree';
        if (est && est.k === 'fin') return 'contradict';
        if (est && est.k === 'inf' && est.s !== val.s) return 'contradict';
        return 'unclear';
    }
    return 'unclear';
}

export function fmtNum(x, L) {
    if (!Number.isFinite(x)) return Number.isNaN(x) ? '\\text{—}' : x > 0 ? '+\\infty' : '-\\infty';
    const ax = Math.abs(x);
    let s;
    if (ax !== 0 && (ax >= 1e7 || ax < 1e-5)) {
        const [m, e] = x.toExponential(4).split('e');
        s = `${m.replace(/\.?0+$/, '')} \\cdot 10^{${Number(e)}}`;
    } else {
        s = x.toPrecision(8);
        if (s.includes('.')) s = s.replace(/\.?0+$/, '');
    }
    return decimalIn(s, L);
}

export function tableStep(rows, v, P, n) {
    const tex = eachLanguage((L) => {
        const lines = rows.map((r) => `${fmtNum(r.x, L)} & ${fmtNum(r.fx, L)}`).join(' \\\\ ');
        return `\\begin{array}{r|r} ${v} & f(${v}) \\\\ \\hline ${lines} \\end{array}`;
    });
    void n;
    return step({
        title: msg('calculus.limit.table.table_of_values'),
        tex,
        text: Number.isFinite(P.x)
            ? msg('calculus.limit.table.values_of_function_closer_and_closer', {
                  v,
                  P: (lng) => plainNum(P, lng),
                  p: (lng) =>
                      P.side === 'both'
                          ? msg('calculus.limit.table.from_both_sides').in(lng)
                          : P.side === 'left'
                            ? msg('calculus.limit.table.from_left').in(lng)
                            : msg('calculus.limit.table.from_right').in(lng),
              })
            : msg('calculus.limit.table.values_of_function_for_larger_and', { v }),
        rule: 'table',
    });
}
