// Greatest and least values of a function on a segment — the school method, with steps.
//
//   extremeOnSegment(f, v = 'x', a, b, {kind: 'max' | 'min' | 'both', steps = true})
//     → {kind, value (node), at (node), approx, max?, min?, candidates: [{x, y, approx, why}], steps, tex, text}
//   f: node or text; a, b: nodes, numbers or text ('pi/2', '-3pi/2').
//
// A continuous function on a segment takes its greatest and least values at critical points inside the segment
// (f′ = 0 or f′ undefined) or at the ends. Critical points are found exactly when the equation solver can do it,
// else numerically with an exact form recognised when there is one (rational, a rational multiple of π, √).
import { MathError, Q } from '../core/rational.js';
import { num, rel, substitute, freeVars, numValue } from '../core/ast.js';
import { parse } from '../core/parse.js';
import { compile } from '../core/evaluate.js';
import { toTex, toText } from '../core/print.js';
import { derivative } from './derivative/index.js';
import { solveEquation } from '../solve/index.js';
import { numFindRoots } from '../numbers/numeric/index.js';
import { L, step } from '../core/steps.js';
import { trySimplify, approx } from '../core/safe.js';
import { msg, notation } from '../i18n/index.js';

const asNode = (x) => (typeof x === 'string' ? parse(x) : typeof x === 'number' ? num(x) : x);
const texOf = (n, l) => toTex(n, { lang: l });
const both = (fn) => ({ ru: fn('ru'), en: fn('en') });
const sepL = (l) => (notation(l).listTex);
const fmt = (x, l) => { const s = String(+x.toPrecision(6)); return l === 'ru' ? s.replace('.', '{,}') : s; };

// A float → an exact node when it is a simple number: p/q, (p/q)·π, ±√n/q, else null.
export function exactGuess(x) {
    if (!Number.isFinite(x)) return null;
    for (let d = 1; d <= 24; d++) {
        const n = Math.round(x * d);
        if (Math.abs(x - n / d) < 1e-10 * Math.max(1, Math.abs(x))) return num(new Q(BigInt(n), BigInt(d)));
    }
    for (let d = 1; d <= 12; d++) {
        const n = Math.round((x / Math.PI) * d);
        if (n !== 0 && Math.abs(x - (n * Math.PI) / d) < 1e-10 * Math.max(1, Math.abs(x))) return trySimplify(parse(`${n}pi/${d}`));
    }
    for (let d = 1; d <= 12; d++) {
        const s = (x * d) ** 2;
        const r = Math.round(s);
        if (r > 1 && Math.abs(s - r) < 1e-8 * Math.max(1, s)) return trySimplify(parse(`${x < 0 ? '-' : ''}sqrt(${r})/${d}`));
    }
    const e = Math.log(Math.abs(x));
    for (let d = 1; d <= 6; d++) {
        const n = Math.round(e * d);
        if (x > 0 && n !== 0 && Math.abs(e - n / d) < 1e-10) return trySimplify(parse(`e^(${n}/${d})`));
    }
    const l = Math.exp(x);
    for (let d = 1; d <= 6; d++) {
        const r = Math.round(l ** d);
        if (r > 1 && Math.abs(l ** d - r) < 1e-8 * r) return trySimplify(parse(`ln(${r})/${d}`));
    }
    return null;
}

export function extremeOnSegment(fIn, v = 'x', aIn, bIn, opts = {}) {
    const kind = opts.kind || 'both';
    const wantSteps = opts.steps !== false;
    const f = trySimplify(asNode(fIn));
    const A = trySimplify(asNode(aIn)), B = trySimplify(asNode(bIn));
    const a = approx(A), b = approx(B);
    if (!(Number.isFinite(a) && Number.isFinite(b)) || !(a < b)) {
        throw new MathError(msg('calculus.extrema.segment_b_with_numeric_ends_b'), null, null, 'segment');
    }
    const others = freeVars(f).filter((x) => x !== v);
    if (others.length) throw new MathError(msg('calculus.extrema.function_has_letters_besides', { p: others.join(', '), v }), null, null, 'unbound');
    let fc;
    try { fc = compile(f, [v]); } catch { fc = null; }
    if (!fc) throw new MathError(msg('calculus.extrema.function_could_not_be_evaluated'), null, null, 'nan');
    // defined on the segment?
    let bad = 0;
    for (let i = 0; i <= 400; i++) if (!Number.isFinite(fc(a + ((b - a) * i) / 400))) bad++;
    if (bad > 0) {
        return { kind: 'unsupported', reason: msg('calculus.extrema.function_is_undefined_or_unbounded_on'), steps: [] };
    }
    const steps = [];
    const T = (ru, en) => L(ru, en);
    const x = v;

    if (wantSteps) {
        steps.push(step({
            title: msg('calculus.extrema.method'),
            text: msg('calculus.extrema.function_is_continuous_on_so_its', { A: (lng) => texOf(A, lng), B: (lng) => texOf(B, lng), x }),
        }));
    }

    // 1. the derivative
    const d = derivative(f, v, { steps: wantSteps });
    const df = d.result;
    if (wantSteps) steps.push(step({ title: msg('calculus.extrema.derivative'), tex: `f'(${x}) = ${texOf(df, 'ru')}`, sub: d.steps }));

    // 2. critical points inside
    const inside = (t) => t > a + 1e-12 * Math.max(1, Math.abs(a)) && t < b - 1e-12 * Math.max(1, Math.abs(b));
    const crit = [];
    let exactCrit = true;
    let solved;
    try {
        solved = solveEquation(rel('=', df, num(0)), v, { steps: wantSteps, interval: [A, B] });
    } catch { solved = null; }
    if (solved && solved.kind !== 'unsupported' && !solved.numeric) {
        const list = solved.families?.length && solved.inInterval ? solved.inInterval : (solved.roots || []);
        for (const r of list) {
            const t = typeof r.approx === 'number' ? r.approx : approx(r.node);
            if (inside(t)) crit.push({ x: r.node, t, why: T('f′ = 0', 'f′ = 0') });
        }
        if (solved.families?.length && !solved.inInterval) exactCrit = false;
    } else exactCrit = false;
    if (!exactCrit) {
        crit.length = 0;
        let dc;
        try { dc = compile(df, [v]); } catch { dc = null; }
        for (const r of dc ? numFindRoots(dc, a, b, { samples: 2000 }) : []) {
            if (r.kind === 'interval' || !inside(r.x)) continue;
            const g = exactGuess(r.x);
            crit.push({ x: g && Math.abs(approx(g) - r.x) < 1e-9 ? g : num(+r.x.toPrecision(12)), t: r.x, why: msg('calculus.extrema.f_0_numerically'), numeric: !g });
        }
    }
    // points where f′ does not exist (|x − 1|, ∛x): f finite, f′ not
    let dcomp;
    try { dcomp = compile(df, [v]); } catch { dcomp = null; }
    if (dcomp) {
        const N = 2000;
        for (let i = 1; i < N; i++) {
            const t0 = a + ((b - a) * (i - 0.5)) / N, t1 = a + ((b - a) * (i + 0.5)) / N;
            const y0 = dcomp(t0), y1 = dcomp(t1);
            // a jump of the derivative's sign with a huge or undefined derivative between: a corner or a cusp
            if (Number.isFinite(y0) && Number.isFinite(y1) && Math.sign(y0) !== Math.sign(y1) && Math.abs(y0 - y1) > 1e-6) {
                let lo = t0, hi = t1;
                for (let k = 0; k < 60; k++) { const m = (lo + hi) / 2; const ym = dcomp(m); if (Number.isFinite(ym) && Math.sign(ym) === Math.sign(y0)) lo = m; else hi = m; }
                const m = (lo + hi) / 2;
                const yl = dcomp(lo), yr = dcomp(hi);
                // a corner (|x|) or a cusp (∛x²): the sign flips but the derivative stays away from zero on both sides
                const jump = !Number.isFinite(yl) || !Number.isFinite(yr) || Math.min(Math.abs(yl), Math.abs(yr)) > 1e-7;
                if (jump) {
                    if (!crit.some((c) => Math.abs(c.t - m) < 1e-6) && inside(m)) {
                        const g = exactGuess(m);
                        crit.push({ x: g ?? num(+m.toPrecision(12)), t: m, why: msg('calculus.extrema.no_derivative') });
                    }
                }
            }
        }
    }
    crit.sort((p, q) => p.t - q.t);
    if (wantSteps) {
        steps.push(step({
            title: msg('calculus.extrema.critical_points_inside_segment'),
            tex: crit.length ? crit.map((c) => `${x} = ${texOf(c.x, 'ru')}`).join(sepL('ru')) : undefined,
            text: crit.length
                ? msg('calculus.extrema.solve_and_keep_roots_inside', { x, A: (lng) => texOf(A, lng), B: (lng) => texOf(B, lng) })
                : msg('calculus.extrema.inside_segment_derivative_has_no_zeros'),
            sub: solved?.steps?.length && exactCrit ? solved.steps : undefined,
        }));
    }

    // 3. values
    const cands = [
        { x: A, t: a, why: msg('calculus.extrema.left_end') },
        ...crit,
        { x: B, t: b, why: msg('calculus.extrema.right_end') },
    ].map((c) => {
        const y = trySimplify(substitute(f, { [v]: c.x }));
        let yv = approx(y);
        if (!Number.isFinite(yv)) yv = fc(c.t);
        return { ...c, y, approx: yv };
    }).filter((c) => Number.isFinite(c.approx));
    if (!cands.length) return { kind: 'unsupported', reason: msg('calculus.extrema.could_not_evaluate_function'), steps };
    const maxC = cands.reduce((p, q) => (q.approx > p.approx + 1e-12 ? q : p));
    const minC = cands.reduce((p, q) => (q.approx < p.approx - 1e-12 ? q : p));
    const nice = (c, l) => (numValue(c.y) !== null ? texOf(c.y, l) : `${texOf(c.y, l)} \\approx ${fmt(c.approx, l)}`);
    if (wantSteps) {
        steps.push(step({
            title: msg('calculus.extrema.values_at_these_points'),
            tex: both((l) => cands.map((c) => `f\\left(${texOf(c.x, l)}\\right) = ${nice(c, l)}`).join(' \\\\ ')),
            text: msg('calculus.extrema.compare_values_at_ends_and_at'),
        }));
    }
    const seg = (l) => `[${texOf(A, l)}${sepL(l)}${texOf(B, l)}]`;
    const line = (c, which, l) => `\\${which}_{${seg(l)}} f = ${texOf(c.y, l)}${msg('calculus.extrema.at').in(l)}${x} = ${texOf(c.x, l)}`;
    const texAns = both((l) => (kind === 'max' ? line(maxC, 'max', l) : kind === 'min' ? line(minC, 'min', l) : `${line(maxC, 'max', l)};\\quad ${line(minC, 'min', l)}`));
    if (wantSteps) steps.push(step({ title: msg('calculus.extrema.answer'), tex: texAns, rule: 'answer' }));
    const pick = kind === 'min' ? minC : maxC;
    const last = steps[steps.length - 1];
    if (last) last.final = true;
    return {
        kind,
        value: pick.y,
        at: pick.x,
        approx: pick.approx,
        max: { value: maxC.y, at: maxC.x, approx: maxC.approx },
        min: { value: minC.y, at: minC.x, approx: minC.approx },
        candidates: cands.map((c) => ({ x: c.x, y: c.y, approx: c.approx, why: c.why })),
        numeric: !exactCrit,
        steps,
        tex: texAns,
        text: both((l) => `${toText(pick.y, { lang: l })}`),
    };
}

// Points of local maximum and minimum on the whole domain (ЕГЭ: «найдите точку максимума»).
//   extremePoints(f, v = 'x', {steps = true, range = [-50, 50]})
//     → {max: [{x, y, approx}], min: [...], critical: [...], steps, tex}
// Critical points: f′ = 0 (exactly when possible) and points where f′ does not exist; the kind comes from the sign
// of f′ just left and right of each point (a sign change + → − is a maximum, − → + a minimum).
export function extremePoints(fIn, v = 'x', opts = {}) {
    const wantSteps = opts.steps !== false;
    const [lo, hi] = opts.range || [-50, 50];
    const f = trySimplify(asNode(fIn));
    const fc = compile(f, [v]);
    const d = derivative(f, v, { steps: wantSteps });
    const df = d.result;
    const dc = compile(df, [v]);
    const steps = [];
    const T = (ru, en) => L(ru, en);
    if (wantSteps) steps.push(step({ title: msg('calculus.extrema.derivative'), tex: `f'(${v}) = ${texOf(df, 'ru')}`, sub: d.steps }));
    let pts = [];
    let solved;
    try { solved = solveEquation(rel('=', df, num(0)), v, { steps: wantSteps }); } catch { solved = null; }
    if (solved && solved.kind === 'roots' && !solved.families?.length && !solved.numeric) {
        pts = solved.roots.map((r) => ({ x: r.node, t: typeof r.approx === 'number' ? r.approx : approx(r.node) }));
    } else {
        for (const r of numFindRoots(dc, lo, hi, { samples: 8000 })) {
            if (r.kind === 'interval') continue;
            const g = exactGuess(r.x);
            pts.push({ x: g && Math.abs(approx(g) - r.x) < 1e-9 ? g : num(+r.x.toPrecision(12)), t: r.x });
        }
    }
    pts = pts.filter((p) => Number.isFinite(p.t) && Number.isFinite(fc(p.t)) && (!opts.range || (p.t > lo && p.t < hi)));
    const out = { max: [], min: [], critical: [] };
    for (const p of pts) {
        const h = 1e-4 * Math.max(1, Math.abs(p.t));
        const l = dc(p.t - h), r = dc(p.t + h);
        const kindP = l > 0 && r < 0 ? 'max' : l < 0 && r > 0 ? 'min' : 'none';
        const y = trySimplify(substitute(f, { [v]: p.x }));
        const item = { x: p.x, y, approx: approx(y), kind: kindP };
        out.critical.push(item);
        if (kindP !== 'none') out[kindP].push(item);
    }
    if (wantSteps) {
        steps.push(step({
            title: msg('calculus.extrema.critical_points'),
            tex: out.critical.length ? out.critical.map((c) => `${v} = ${texOf(c.x, 'ru')}`).join(sepL('ru')) : undefined,
            text: out.critical.length ? msg('calculus.extrema.solve', { v }) : msg('calculus.extrema.derivative_is_never_zero_there_are'),
            sub: solved?.steps,
        }));
        steps.push(step({
            title: msg('calculus.extrema.signs_of_derivative'),
            tex: both((l) => out.critical.map((c) => `${v} = ${texOf(c.x, l)}:\\ ${c.kind === 'max' ? '+\\ \\to\\ -\\ (\\max)' : c.kind === 'min' ? '-\\ \\to\\ +\\ (\\min)' : msg('calculus.extrema.no_sign_change').in(l)}`).join(' \\\\ ')),
            text: msg('calculus.extrema.if_derivative_changes_sign_from_plus'),
        }));
        steps.push(step({
            title: msg('calculus.extrema.answer'),
            tex: both((l) => [out.max.length ? `x_{\\max} = ${out.max.map((c) => texOf(c.x, l)).join(sepL(l))}` : null, out.min.length ? `x_{\\min} = ${out.min.map((c) => texOf(c.x, l)).join(sepL(l))}` : null].filter(Boolean).join(';\\quad ') || (msg('calculus.extrema.no_extrema').in(l))),
            rule: 'answer', final: true,
        }));
    }
    return { ...out, steps, derivative: df };
}
