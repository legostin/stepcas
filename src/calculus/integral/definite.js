// integral/definite — definite integrals: Newton–Leibniz with jumps and singular points, improper integrals as
// limits, numeric values marked ≈, and the area between two curves.

import { sym, neg, isConst, containsVar, fn, nodeChildren, num, mul, substitute, freeVars, add } from '../../core/ast.js';
import { evaluate, compile } from '../../core/evaluate.js';
import { MathError, Q } from '../../core/rational.js';
import { Poly } from '../../core/poly.js';
import { numFindRoots, numIntegrate } from '../../numbers/numeric/index.js';
import { limit } from '../limit/index.js';
import { step } from '../../core/steps.js';
import { niceForm } from '../derivative/index.js';
import { PI } from './common.js';
import { integrate } from './integrate.js';
import { msg, notation, eachLanguage, decimalIn } from '../../i18n/index.js';
import { asNode } from '../../core/parse.js';
import { prettyForm, isNum, paren, simp, trySimp, N0, checkExpr, calcTex } from '../display.js';

// ---------------------------------------------------------------- definite integrals

function boundNode(x) {
    if (x === Infinity) return sym('inf');
    if (x === -Infinity) return neg(sym('inf'));
    return asNode(x);
}

function boundValue(n) {
    const s = trySimp(n) ?? n;
    if (isConst(s) && s.name === 'inf') return { node: s, x: Infinity };
    if (s.type === 'mul' && s.args.length === 2 && isNum(s.args[0]) && s.args[0].value.isNeg() && isConst(s.args[1]) && s.args[1].name === 'inf')
        return { node: s, x: -Infinity };
    const x = evaluate(s);
    if (!Number.isFinite(x)) throw new MathError(msg('calculus.integral.definite.limits_of_integration_must_be_numbers'), null, null, 'range');
    return { node: s, x };
}

const boundTex = (b, L) => (b.x === Infinity ? '+\\infty' : b.x === -Infinity ? '-\\infty' : calcTex(b.node, L));

/** Candidate singular points of g on [lo, hi]: zeros of denominators and of log arguments, poles of tg/ctg/sec/cosec. */
function singularCandidates(g, v, lo, hi) {
    const bases = [];
    const walk = (n) => {
        if (n.type === 'pow' && isNum(n.exp) && n.exp.value.isNeg() && containsVar(n.base, v)) bases.push(n.base);
        if (n.type === 'fn' && (n.name === 'ln' || n.name === 'lg') && containsVar(n.args[0], v)) bases.push(n.args[0]);
        if (n.type === 'fn' && n.name === 'log' && containsVar(n.args[1], v)) bases.push(n.args[1]);
        if (n.type === 'fn' && (n.name === 'tan' || n.name === 'sec') && containsVar(n.args[0], v)) bases.push(fn('cos', n.args[0]));
        if (n.type === 'fn' && (n.name === 'cot' || n.name === 'csc') && containsVar(n.args[0], v)) bases.push(fn('sin', n.args[0]));
        if (n.type === 'fn' && n.name === 'abs' && containsVar(n.args[0], v)) bases.push(n.args[0]);
        nodeChildren(n).forEach(walk);
    };
    walk(g);
    const wl = Number.isFinite(lo) ? lo : -1000;
    const wh = Number.isFinite(hi) ? hi : 1000;
    const pts = [];
    for (const B of bases) {
        const P = Poly.fromNode(B, v);
        if (P && P.degree >= 1) {
            for (const { root } of P.rationalRoots()) {
                const x = root.toNumber();
                if (x >= wl && x <= wh) pts.push({ x, node: num(root) });
            }
        }
        let bc;
        try {
            bc = compile(B, [v]);
        } catch {
            continue;
        }
        try {
            for (const r of numFindRoots(bc, wl, wh, { samples: 2000 })) {
                if (r.kind === 'interval') continue;
                pts.push({ x: r.x, node: null });
            }
        } catch {
            // no roots found numerically
        }
    }
    return mergePoints(pts);
}

function mergePoints(list) {
    const sorted = [...list].sort((a, b) => a.x - b.x);
    const out = [];
    for (const p of sorted) {
        const last = out[out.length - 1];
        if (last && Math.abs(last.x - p.x) <= 1e-7 * Math.max(1, Math.abs(p.x))) {
            if (!last.node && p.node) out[out.length - 1] = p;
            continue;
        }
        out.push(p);
    }
    return out;
}

/** Points of [l, h] where F jumps although f stays bounded (a numeric scan refined by bisection). */
function jumpsOf(Fc, fc, l, h) {
    const N = 2000;
    const out = [];
    let prev = null;
    for (let i = 0; i <= N; i++) {
        const x = l + ((h - l) * (i + 0.37)) / (N + 1);
        const y = Fc(x);
        if (prev && Number.isFinite(y) && Number.isFinite(prev.y)) {
            const slope = Math.max(Math.abs(fc(x)), Math.abs(fc(prev.x)), Math.abs(fc((x + prev.x) / 2)), 1);
            if (Math.abs(y - prev.y) > 50 * slope * (x - prev.x) + 1e-6) {
                let a = prev.x;
                let b = x;
                const ya = prev.y;
                for (let k = 0; k < 80; k++) {
                    const m = (a + b) / 2;
                    const ym = Fc(m);
                    if (Number.isFinite(ym) && Math.abs(ym - ya) < Math.abs(Fc(b) - ym)) a = m;
                    else b = m;
                }
                out.push({ x: (a + b) / 2, node: null });
            }
        }
        prev = { x, y };
    }
    return out;
}

/** Snap a numeric point to a nice exact node (integers, simple fractions, multiples of π/12). */
function exactPoint(x) {
    for (const d of [1, 2, 3, 4, 5, 6, 8, 10, 12]) {
        const n = Math.round(x * d);
        if (Math.abs(n / d - x) < 1e-9 * Math.max(1, Math.abs(x))) return num(new Q(BigInt(n), BigInt(d)));
    }
    const k = Math.round((x / Math.PI) * 12);
    if (Math.abs((k / 12) * Math.PI - x) < 1e-9) return simp(mul(num(new Q(BigInt(k), 12n)), PI));
    return null;
}

/** Value of F at an end of a piece: exact substitution (unless forced), else a one-sided limit. */
function endValue(F, v, b, side, force) {
    if (Number.isFinite(b.x) && !force) {
        try {
            const s = simp(substitute(F, { [v]: b.node }));
            const x = evaluate(s);
            if (Number.isFinite(x)) return { kind: 'fin', node: s, x, how: 'subst' };
        } catch {
            // fall through to the limit
        }
    }
    const L = limit(F, v, b.node, { side });
    if (L.value === 'inf' || L.value === '-inf') return { kind: L.value, how: 'limit', lim: L };
    if (L.value && typeof L.value === 'object') {
        const x = evaluate(L.value);
        if (Number.isFinite(x)) return { kind: 'fin', node: L.value, x, how: 'limit', lim: L };
    }
    return { kind: 'unknown', how: 'limit', lim: L };
}

function numericValue(fc, lo, hi) {
    try {
        const r = numIntegrate(fc, lo, hi, { info: true });
        return Number.isFinite(r.value) ? r : null;
    } catch {
        return null;
    }
}

/** The numeric value with a convergence verdict ({value, ok, divergent, reason}), or null. */
function checkedValue(fc, lo, hi) {
    try {
        return numIntegrate(fc, lo, hi, { info: true, check: true });
    } catch {
        return null;
    }
}

/** For an improper integral computed numerically: do the partial integrals settle as the cut-off moves out? */
function improperSettles(fc, lo, hi) {
    const val = (a, b) => numericValue(fc, a, b)?.value ?? NaN;
    const seq = [];
    if (!Number.isFinite(hi) || !Number.isFinite(lo)) {
        for (const R of [1e2, 1e4, 1e6]) seq.push(val(Number.isFinite(lo) ? lo : -R, Number.isFinite(hi) ? hi : R));
    } else {
        const w = hi - lo;
        const l0 = !Number.isFinite(fc(lo)) || poleAt(fc, lo);
        const h0 = !Number.isFinite(fc(hi)) || poleAt(fc, hi);
        for (const e of [1e-2, 1e-4, 1e-6]) seq.push(val(l0 ? lo + e * w : lo, h0 ? hi - e * w : hi));
    }
    if (!seq.every(Number.isFinite)) return false;
    const d1 = Math.abs(seq[1] - seq[0]);
    const d2 = Math.abs(seq[2] - seq[1]);
    return d2 <= 1e-3 * Math.max(1, Math.abs(seq[2])) && d2 <= d1;
}

const poleAt = (fc, x) => {
    const d = 1e-8 * Math.max(1, Math.abs(x));
    const yl = fc(x - d);
    const yr = fc(x + d);
    return !Number.isFinite(yl) || !Number.isFinite(yr) || Math.abs(yl) > 1e6 || Math.abs(yr) > 1e6;
};

/**
 * ∫ₐᵇ f dv. a, b: numbers, strings or nodes (inf / -inf allowed). opts: {steps}.
 * → {value: node | 'inf' | '-inf' | null, numeric: number | null, exact: boolean, approx: boolean,
 *    converges: boolean | null, improper: boolean, antiderivative: node | null, method, steps, tex}.
 * Exact values come from Newton–Leibniz: the interval is split at the points where f blows up or the
 * antiderivative jumps, and every end of a piece that is infinite or singular is a one-sided limit of F
 * (an infinite limit means the integral diverges). The exact value is cross-checked numerically.
 * Otherwise a numeric value, marked ≈.
 */
// F(b′) − F(a′) against the quadrature on finite pieces [a′; b′] inside an improper interval (ends pulled in from
// infinity and away from poles): does the antiderivative really match f there?
function truncatedAgrees(F, fc, v, lo, hi, interior) {
    let Fc;
    try {
        Fc = compile(F, [v]);
    } catch {
        return false;
    }
    const ends = [lo, ...interior.filter((p) => p.pole), hi];
    for (let i = 0; i + 1 < ends.length; i++) {
        const a0 = ends[i].x,
            b0 = ends[i + 1].x;
        const tries = [];
        for (const far of [1e2, 1e4]) {
            const a = Number.isFinite(a0) ? a0 + (poleAt(fc, a0) ? 1e-3 * Math.max(1, Math.abs(a0)) : 0) : (Number.isFinite(b0) ? b0 : 0) - far;
            const b = Number.isFinite(b0) ? b0 - (poleAt(fc, b0) ? 1e-3 * Math.max(1, Math.abs(b0)) : 0) : (Number.isFinite(a0) ? a0 : 0) + far;
            if (!(b > a)) continue;
            let q;
            try {
                q = numIntegrate(fc, a, b, { tol: 1e-12 });
            } catch {
                q = NaN;
            }
            const e = Fc(b) - Fc(a);
            if (!Number.isFinite(q) || !Number.isFinite(e)) return false;
            tries.push(Math.abs(q - e) <= 1e-7 * Math.max(1, Math.abs(e)));
        }
        if (!tries.length || !tries.every(Boolean)) return false;
    }
    return true;
}

export function integrateDefinite(node, v = 'x', a = 0, b = 1, opts = {}) {
    node = asNode(node);
    checkExpr(node);
    const f = simp(node);
    const A = boundValue(boundNode(a));
    const B = boundValue(boundNode(b));
    const steps = [];
    const wantSteps = !!opts.steps;
    const head = (L) => `\\int_{${boundTex(A, L)}}^{${boundTex(B, L)}} ${f.type === 'add' ? paren(calcTex(node, L)) : calcTex(node, L)}\\,d${v}`;
    if (wantSteps) {
        steps.push(
            step({
                title: msg('calculus.integral.definite.what_we_compute'),
                tex: eachLanguage(head),
                text: msg('calculus.integral.definite.find_antiderivative_f_and_use_newton'),
                rule: 'start',
            }),
        );
    }
    const out = (o) => ({
        value: null,
        numeric: null,
        exact: false,
        approx: false,
        converges: null,
        improper: false,
        antiderivative: null,
        method: null,
        steps,
        tex: null,
        ...o,
    });
    if (A.x === B.x) {
        return out({ value: N0, numeric: 0, exact: true, converges: true, method: 'equal-limits', tex: eachLanguage((L) => `${head(L)} = 0`) });
    }
    const flip = A.x > B.x;
    const lo = flip ? B : A;
    const hi = flip ? A : B;
    const others = freeVars(f).filter((w) => w !== v);
    if (others.length)
        throw new MathError(msg('calculus.integral.definite.definite_integral_needs_numeric_values_for', { p: others.join(', ') }), null, null, 'unbound');
    const fc = compile(f, [v]);
    // domain: f must be defined almost everywhere on the interval
    const pa = Number.isFinite(lo.x) ? lo.x : Math.min(-1, hi.x - 1000);
    const pb = Number.isFinite(hi.x) ? hi.x : Math.max(1, lo.x + 1000);
    let nan = 0;
    for (let i = 1; i < 200; i++) if (Number.isNaN(fc(pa + ((pb - pa) * i) / 200))) nan++;
    if (nan > 4) {
        return out({
            method: 'undefined',
            steps: wantSteps
                ? [
                      step({
                          title: msg('calculus.integral.definite.function_is_not_defined'),
                          text: msg('calculus.integral.definite.integrand_is_undefined_on_part_of'),
                          rule: 'fail',
                      }),
                  ]
                : [],
        });
    }
    const inside = (x) => x > lo.x + 1e-9 * Math.max(1, Math.abs(lo.x)) && x < hi.x - 1e-9 * Math.max(1, Math.abs(hi.x));
    const fPoles = singularCandidates(f, v, lo.x, hi.x).filter((p) => inside(p.x) && poleAt(fc, p.x));
    let improper =
        !Number.isFinite(lo.x) ||
        !Number.isFinite(hi.x) ||
        !Number.isFinite(fc(lo.x)) ||
        !Number.isFinite(fc(hi.x)) ||
        poleAt(fc, lo.x) ||
        poleAt(fc, hi.x) ||
        fPoles.length > 0;
    const anti = integrate(node, v, { steps: wantSteps });
    let exactNode = null;
    let diverges = null;
    let unknown = false;
    let interior = fPoles;
    const parts = [];
    if (anti.result) {
        const F = anti.result;
        const Fs = trySimp(F) ?? F;
        let Fc;
        try {
            Fc = compile(Fs, [v]);
        } catch {
            Fc = null;
        }
        let cand = [...fPoles, ...singularCandidates(Fs, v, lo.x, hi.x).filter((p) => inside(p.x))];
        if (Fc) {
            const l = Number.isFinite(lo.x) ? lo.x : Math.min(hi.x, 0) - 100;
            const h = Number.isFinite(hi.x) ? hi.x : Math.max(lo.x, 0) + 100;
            cand.push(...jumpsOf(Fc, fc, l, h).filter((p) => inside(p.x)));
        }
        cand = mergePoints(cand);
        // keep the points where F is not continuous (or f blows up); a point needs an exact position
        interior = [];
        for (const p of cand) {
            const d = 1e-7 * Math.max(1, Math.abs(p.x));
            const yl = Fc ? Fc(p.x - d) : NaN;
            const yr = Fc ? Fc(p.x + d) : NaN;
            const smooth = Number.isFinite(yl) && Number.isFinite(yr) && Math.abs(yl - yr) < 1e-5 * Math.max(1, Math.abs(yl)) && !poleAt(fc, p.x);
            if (smooth) continue;
            const nodeX = p.node ?? exactPoint(p.x);
            if (!nodeX) {
                unknown = true;
                break;
            }
            interior.push({ x: p.x, node: nodeX, pole: poleAt(fc, p.x) });
        }
        if (!unknown) {
            const pts = [lo, ...interior, hi];
            for (let i = 0; i + 1 < pts.length; i++) {
                const p = pts[i];
                const r = pts[i + 1];
                const forceTop = i + 1 < pts.length - 1 || !Number.isFinite(fc(r.x)) || poleAt(fc, r.x);
                const forceBot = i > 0 || !Number.isFinite(fc(p.x)) || poleAt(fc, p.x);
                const top = endValue(F, v, r, 'left', forceTop);
                const bot = endValue(F, v, p, 'right', forceBot);
                parts.push({ p, r, top, bot });
                if (['inf', '-inf'].includes(top.kind) || ['inf', '-inf'].includes(bot.kind)) diverges = diverges ?? { p, r, top, bot };
                if (top.kind === 'unknown' || bot.kind === 'unknown') unknown = true;
            }
            if (!diverges && !unknown) {
                exactNode = trySimp(add(parts.map((x) => add(x.top.node, neg(x.bot.node)))));
                if (exactNode && flip) exactNode = trySimp(neg(exactNode));
            }
        }
        if (interior.some((p) => p.pole)) improper = true;
        if (wantSteps && (exactNode || diverges)) {
            steps.push(
                step({
                    title: msg('calculus.integral.definite.antiderivative'),
                    tex: eachLanguage((L) => `F(${v}) = ${calcTex(F, L)}`),
                    rule: 'antiderivative',
                    sub: anti.steps.filter((s) => s.rule !== 'answer' && s.rule !== 'start'),
                }),
            );
            if (flip) {
                steps.push(
                    step({
                        title: msg('calculus.integral.definite.swap_limits'),
                        tex: eachLanguage((L) => `\\int_{${boundTex(A, L)}}^{${boundTex(B, L)}} = -\\int_{${boundTex(B, L)}}^{${boundTex(A, L)}}`),
                        text: msg('calculus.integral.definite.lower_limit_is_larger_than_upper'),
                        rule: 'swap',
                    }),
                );
            }
            if (interior.length) {
                const poles = interior.some((p) => p.pole);
                steps.push(
                    step({
                        title: poles
                            ? msg('calculus.integral.definite.singular_points_inside_interval')
                            : msg('calculus.integral.definite.jump_of_antiderivative'),
                        tex: eachLanguage((L) => `${v} = ${interior.map((p) => calcTex(p.node, L)).join(notation(L).listTex)}`),
                        text: poles
                            ? msg('calculus.integral.definite.function_blows_up_inside_interval_newton')
                            : msg('calculus.integral.definite.antiderivative_jumps_inside_interval_this_happens'),
                        rule: 'split',
                    }),
                );
            }
            for (const x of parts) {
                const lim = (e, pt, sideSign, L) =>
                    e.how === 'limit'
                        ? `\\lim_{${v} \\to ${Number.isFinite(pt.x) ? `{${calcTex(pt.node, L)}}^{${sideSign}}` : boundTex(pt, L)}} F(${v})`
                        : null;
                const val = (e) => (e.kind === 'fin' ? null : e.kind === 'inf' ? '+\\infty' : e.kind === '-inf' ? '-\\infty' : '?');
                const isLim = x.top.how === 'limit' || x.bot.how === 'limit';
                steps.push(
                    step({
                        title: isLim ? msg('calculus.integral.definite.improper_integral_limits') : msg('calculus.integral.definite.newton_leibniz_formula'),
                        tex: eachLanguage((L) => {
                            const upper = x.top.kind === 'fin' ? calcTex(x.top.node, L) : val(x.top);
                            const lower = x.bot.kind === 'fin' ? calcTex(x.bot.node, L) : val(x.bot);
                            const lu = lim(x.top, x.r, '-', L) ?? `F\\left(${boundTex(x.r, L)}\\right)`;
                            const ll = lim(x.bot, x.p, '+', L) ?? `F\\left(${boundTex(x.p, L)}\\right)`;
                            const both = x.top.kind === 'fin' && x.bot.kind === 'fin' ? trySimp(add(x.top.node, neg(x.bot.node))) : null;
                            return `\\int_{${boundTex(x.p, L)}}^{${boundTex(x.r, L)}} f\\,d${v} = ${lu} - ${ll} = ${upper} - ${/^-/.test(lower) ? `\\left(${lower}\\right)` : lower}${both ? ` = ${calcTex(niceForm(both), L)}` : ''}`;
                        }),
                        text: isLim
                            ? msg('calculus.integral.definite.at_infinite_limit_at_point_where')
                            : msg('calculus.integral.definite.antiderivative_is_continuous_on_interval_so'),
                        rule: 'newton-leibniz',
                    }),
                );
            }
        }
    }
    if (diverges) {
        const signOf = (k) => (k === 'inf' ? 1 : k === '-inf' ? -1 : 0);
        const contributions = parts.map((x) => signOf(x.top.kind) - signOf(x.bot.kind)).filter((c) => c !== 0);
        const same = contributions.length && contributions.every((c) => Math.sign(c) === Math.sign(contributions[0]));
        const val = same ? ((flip ? -1 : 1) * Math.sign(contributions[0]) > 0 ? 'inf' : '-inf') : null;
        const tex = eachLanguage((L) => `${head(L)}\\ ${msg('calculus.integral.definite.diverges').in(L)}`);
        if (wantSteps) {
            const s = step({ title: msg('calculus.integral.definite.integral_diverges'), tex: tex, rule: 'answer', final: true });
            s.text = msg('calculus.integral.definite.limit_of_antiderivative_is_infinite_so');
            steps.push(s);
        }
        return out({ value: val, converges: false, improper: true, antiderivative: anti.result, method: 'improper', tex });
    }
    // numeric value: for the cross-check, or as the answer
    const cuts = [lo, ...mergePoints([...interior, ...fPoles]).filter((p) => inside(p.x)), hi];
    let numeric = 0;
    let numOk = true;
    let checked = true; // every piece passed the numeric convergence check
    let numDiverges = null; // a piece the check calls divergent
    for (let i = 0; i + 1 < cuts.length; i++) {
        const piece = checkedValue(fc, cuts[i].x, cuts[i + 1].x);
        if (piece?.divergent) numDiverges = numDiverges ?? piece;
        if (!piece?.ok) checked = false;
        const res = piece && Number.isFinite(piece.value) ? piece : numericValue(fc, cuts[i].x, cuts[i + 1].x);
        if (!res) {
            numOk = false;
            break;
        }
        numeric += res.value;
    }
    if (flip) numeric = -numeric;
    if (improper && !exactNode && numDiverges) {
        // no exact verdict (the limit of F does not exist, or there is no F), but the tail visibly does not settle
        const s = numDiverges.value === Infinity ? 1 : numDiverges.value === -Infinity ? -1 : 0;
        const val = s ? ((flip ? -s : s) > 0 ? 'inf' : '-inf') : null;
        const tex = eachLanguage((L) => `${head(L)}\\ ${msg('calculus.integral.definite.diverges').in(L)}`);
        if (wantSteps) {
            const st = step({ title: msg('calculus.integral.definite.integral_diverges'), tex: tex, rule: 'answer', final: true });
            st.text =
                numDiverges.reason === 'pole'
                    ? msg('calculus.integral.definite.function_grows_so_fast_near_singular')
                    : s
                      ? msg('calculus.integral.definite.function_does_not_decay_fast_enough')
                      : msg('calculus.integral.definite.integrals_over_longer_and_longer_intervals');
            steps.push(st);
        }
        return out({ value: val, converges: false, improper: true, antiderivative: anti.result, method: 'improper-numeric', tex });
    }
    if (exactNode) {
        const ex = evaluate(exactNode);
        const tol = improper ? 1e-4 : 1e-6;
        // A slowly decaying tail (1/(x ln²x) on [e; ∞)) fools the quadrature: then check the antiderivative on a long
        // finite piece, where the numbers are reliable, instead of letting a bad number veto a verified answer.
        const agrees =
            Number.isFinite(ex) &&
            (!numOk || Math.abs(ex - numeric) <= tol * Math.max(1, Math.abs(ex)) || (improper && truncatedAgrees(anti.result, fc, v, lo, hi, interior)));
        if (agrees) {
            const value = niceForm(exactNode);
            const tex = eachLanguage(
                (L) =>
                    `${head(L)} = ${calcTex(value, L)}${isNum(trySimp(value) ?? value) && (trySimp(value) ?? value).value.isInt() ? '' : ` \\approx ${fmtNum(ex, L)}`}`,
            );
            if (wantSteps) steps.push(step({ title: msg('calculus.integral.definite.answer'), tex: tex, rule: 'answer', final: true }));
            return out({
                value,
                numeric: ex,
                exact: true,
                converges: true,
                improper,
                antiderivative: anti.result,
                method: improper ? 'improper' : interior.length ? 'newton-leibniz-pieces' : 'newton-leibniz',
                tex,
            });
        }
    }
    const poles = fPoles.length > 0;
    const tailOk = !improper || exactNode || checked || improperSettles(fc, lo.x, hi.x);
    if (!numOk || !Number.isFinite(numeric) || (poles && !exactNode) || !tailOk) {
        if (wantSteps) {
            steps.push(
                step({
                    title: msg('calculus.integral.definite.not_found'),
                    text:
                        poles || !tailOk
                            ? msg('calculus.integral.definite.integral_is_improper_and_its_convergence')
                            : msg('calculus.integral.definite.this_integral_could_not_be_computed'),
                    rule: 'fail',
                }),
            );
        }
        return out({ improper, antiderivative: anti.result, method: 'failed' });
    }
    const tex = eachLanguage((L) => `${head(L)} \\approx ${fmtNum(numeric, L)}`);
    if (wantSteps) {
        if (!anti.result && anti.reason)
            steps.push(step({ title: msg('calculus.integral.definite.antiderivative'), text: anti.reason, rule: 'antiderivative' }));
        steps.push(
            step({
                title: msg('calculus.integral.definite.numerical_integration'),
                text: !anti.result
                    ? msg('calculus.integral.definite.no_elementary_antiderivative_was_found_so')
                    : msg('calculus.integral.definite.exact_value_could_not_be_confirmed'),
                rule: 'numeric',
            }),
        );
        steps.push(step({ title: msg('calculus.integral.definite.answer_approximate'), tex: tex, rule: 'answer', final: true }));
    }
    return out({ numeric, approx: true, converges: true, improper, antiderivative: anti.result, method: 'numeric', tex });
}

function fmtNum(x, L) {
    let s = x.toFixed(6);
    if (s.includes('.')) s = s.replace(/\.?0+$/, '');
    if (s === '-0') s = '0';
    return decimalIn(s, L);
}

/**
 * Area between y = f and y = g for v in [a, b] (∫|f − g|). a, b optional: then the outermost intersection
 * points are used. → {value: node | null, numeric, exact, approx, points: [nodes], pieces, steps, tex}.
 */
export function areaBetween(f, g, v = 'x', a = null, b = null, opts = {}) {
    f = asNode(f);
    g = asNode(g);
    const d = simp(add(f, neg(g)));
    const dc = compile(d, [v]);
    let lo;
    let hi;
    const cross = [];
    const P = Poly.fromNode(d, v);
    const exactRoots = P && P.degree >= 1 ? P.rationalRoots().map((r) => r.root) : null;
    if (a === null || b === null) {
        let roots;
        if (P && exactRoots && exactRoots.length >= 2) roots = exactRoots.map((r) => ({ node: num(r), x: r.toNumber() }));
        else
            roots = numFindRoots(dc, -50, 50)
                .filter((r) => r.kind !== 'interval')
                .map((r) => ({ node: exactPoint(r.x) ?? num(Q.of(r.x.toFixed(10))), x: r.x }));
        if (roots.length < 2) throw new MathError(msg('calculus.integral.definite.graphs_meet_at_fewer_than_two'), null, null, 'no-bounds');
        lo = roots[0];
        hi = roots[roots.length - 1];
    } else {
        lo = boundValue(boundNode(a));
        hi = boundValue(boundNode(b));
        if (lo.x > hi.x) [lo, hi] = [hi, lo];
    }
    for (const r of numFindRoots(dc, lo.x, hi.x)) {
        if (r.kind === 'interval' || r.x <= lo.x + 1e-9 || r.x >= hi.x - 1e-9) continue;
        const ex = exactRoots?.find((z) => Math.abs(z.toNumber() - r.x) < 1e-8);
        cross.push({ node: ex ? num(ex) : (exactPoint(r.x) ?? num(Q.of(r.x.toFixed(12)))), x: r.x });
    }
    const pts = [lo, ...cross, hi];
    const pieces = [];
    let total = null;
    let numeric = 0;
    let exact = true;
    const steps = [];
    for (let i = 0; i + 1 < pts.length; i++) {
        const p = pts[i];
        const r = pts[i + 1];
        const mid = dc((p.x + r.x) / 2);
        const upper = mid >= 0 ? d : simp(neg(d));
        const res = integrateDefinite(upper, v, p.node, r.node, { steps: false });
        pieces.push({ from: p.node, to: r.node, upper: mid >= 0 ? 'f' : 'g', value: res.value, numeric: res.numeric });
        if (!res.exact) exact = false;
        numeric += res.numeric ?? NaN;
        if (res.exact && total !== null) total = add(total, res.value);
        else if (res.exact && i === 0) total = res.value;
        else total = null;
    }
    const value = exact && total ? niceForm(total) : null;
    const tex = eachLanguage(
        (L) =>
            `S = \\int_{${calcTex(lo.node, L)}}^{${calcTex(hi.node, L)}} \\left|${calcTex(prettyForm(d), L)}\\right|\\,d${v} ${value ? '= ' + calcTex(value, L) : '\\approx ' + fmtNum(numeric, L)}`,
    );
    if (opts.steps) {
        steps.push(
            step({
                title: msg('calculus.integral.definite.difference_of_functions'),
                tex: eachLanguage((L) => `f(${v}) - g(${v}) = ${calcTex(prettyForm(d), L)}`),
                text: msg('calculus.integral.definite.area_between_graphs_is_integral_of'),
                rule: 'difference',
            }),
        );
        if (cross.length || a === null) {
            steps.push(
                step({
                    title: msg('calculus.integral.definite.intersection_points'),
                    tex: eachLanguage((L) => `${v} = ${pts.map((p) => calcTex(p.node, L)).join(notation(L).listTex)}`),
                    text: msg('calculus.integral.definite.between_intersection_points_difference_keeps_its'),
                    rule: 'intersections',
                }),
            );
        }
        for (const pc of pieces) {
            steps.push(
                step({
                    title: msg('calculus.integral.definite.piece'),
                    tex: eachLanguage(
                        (L) =>
                            `\\int_{${calcTex(pc.from, L)}}^{${calcTex(pc.to, L)}} ${pc.upper === 'f' ? '(f - g)' : '(g - f)'}\\,d${v} = ${pc.value && typeof pc.value === 'object' ? calcTex(pc.value, L) : '\\approx ' + fmtNum(pc.numeric ?? NaN, L)}`,
                    ),
                    rule: 'piece',
                }),
            );
        }
        steps.push(step({ title: msg('calculus.integral.definite.area'), tex: tex, rule: 'answer', final: true }));
    }
    return { value, numeric, exact: !!value, approx: !value, points: pts.map((p) => p.node), pieces, steps, tex };
}
