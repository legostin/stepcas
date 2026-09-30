// stepcas bench — one task through the engine's public API → {status, got, steps, exact, note}.
// status: 'correct' | 'wrong' | 'refused' (the engine said it can't) | 'noapi' (no function for this yet) | 'error'
import * as E from '../../src/index.js';
import { num, close, sameNumbers, familyRoots, sameFunction, isAntiderivative, sameInterval } from './check.mjs';

const text = (n) => { try { return E.toText(n, { lang: 'en' }); } catch { return String(n); } };
const stepsOf = (r) => (Array.isArray(r?.steps) ? r.steps.length : 0);
const P = (s) => E.parse(String(s), { lang: 'en' });

function rootsCheck(r, t) {
    const a = t.answer;
    if (a.none) return r.kind === 'none' || (r.kind === 'roots' && !r.roots.length) ? 'correct' : 'wrong';
    if (a.families) {
        if (!r.families?.length) {
            // finitely many roots are fine when the task asks only for those on an interval
            return 'wrong';
        }
        const got = familyRoots(r.families.map((f) => [f.base, f.period]));
        return sameNumbers(got, familyRoots(a.families)) ? 'correct' : 'wrong';
    }
    if (a.set) return r.kind === 'set' && sameInterval(r.set, a.set) ? 'correct' : 'wrong';
    if (a.roots) {
        let got = (r.roots || []).map((x) => (typeof x.approx === 'number' ? x.approx : num(x.node)));
        if (t.interval && r.families?.length) got = familyRoots(r.families.map((f) => [f.base, f.period]), num(t.interval[0]), num(t.interval[1]));
        else if (t.interval) got = got.filter((x) => x >= num(t.interval[0]) - 1e-9 && x <= num(t.interval[1]) + 1e-9);
        return sameNumbers(got, a.roots.map(num)) ? 'correct' : 'wrong';
    }
    return 'wrong';
}

const ask = (t, vals) => {
    // ЕГЭ-style: «в ответ запишите наименьший корень / сумму корней»
    if (!t.ask || t.ask === 'roots') return null;
    const v = vals.slice().sort((a, b) => a - b);
    return t.ask === 'min' ? v[0] : t.ask === 'max' ? v[v.length - 1] : t.ask === 'sum' ? v.reduce((a, b) => a + b, 0) : t.ask === 'count' ? v.length : null;
};

export function runTask(t) {
    const v = t.v || 'x';
    switch (t.op) {
        case 'solve': {
            const r = E.solveEquation(t.task, v, { steps: true, interval: t.interval ? `[${t.interval[0]}; ${t.interval[1]}]` : undefined });
            if (r.kind === 'unsupported') return { status: 'refused', note: r.reason?.en };
            if (t.ask && t.ask !== 'roots') {
                let vals = (r.roots || []).map((x) => (typeof x.approx === 'number' ? x.approx : num(x.node)));
                if (t.interval && r.families?.length) vals = familyRoots(r.families.map((f) => [f.base, f.period]), num(t.interval[0]), num(t.interval[1]));
                else if (t.interval) vals = vals.filter((x) => x >= num(t.interval[0]) - 1e-9 && x <= num(t.interval[1]) + 1e-9);
                const got = ask(t, vals);
                return { status: close(got, num(t.answer.value)) ? 'correct' : 'wrong', got, steps: stepsOf(r), exact: !r.numeric };
            }
            return { status: rootsCheck(r, t), got: r.answer?.text?.en ?? r.answer?.text, steps: stepsOf(r), exact: !r.numeric };
        }
        case 'ineq': {
            const r = E.solveInequality(t.task, v, { steps: true });
            if (!r.set) return { status: 'refused', note: r.reason?.en };
            return { status: sameInterval(r.set, t.answer.set) ? 'correct' : 'wrong', got: r.answer?.text?.ru, steps: stepsOf(r), exact: !r.approx };
        }
        case 'system': {
            const rels = t.task.split(';').map((s) => s.trim());
            const vars = t.vars || ['x', 'y'];
            const linear = rels.every((s) => E.linearForm(P(s), vars));
            const r = linear ? E.solveLinearSystem(rels, vars, { steps: true }) : E.solveSystem2(rels, vars);
            if (r.kind === 'unsupported') return { status: 'refused', note: r.reason?.en };
            const sols = r.kind === 'unique' && r.solution ? [r.solution] : r.solutions || [];
            if (t.answer.none) return { status: r.kind === 'none' ? 'correct' : 'wrong', steps: stepsOf(r) };
            const want = t.answer.solutions.map((s) => s.map(num));
            const got = sols.map((s) => vars.map((k) => num(s[k])));
            const ok = want.length === got.length && want.every((w) => got.some((g) => g.every((x, i) => close(x, w[i]))));
            return { status: ok ? 'correct' : 'wrong', got: JSON.stringify(got), steps: stepsOf(r) };
        }
        case 'value': {
            const r = E.evaluateSteps(P(t.task));
            const x = num(r.value);
            // the answer step alone is not an explanation
            const explained = r.steps.filter((st) => st.rule === 'rule' || st.rule === 'arith').length;
            return { status: close(x, num(t.answer.value)) ? 'correct' : 'wrong', got: text(r.value), exact: r.exact, steps: explained };
        }
        case 'simplify': case 'expand': case 'factor': {
            // the school transformations with steps first, the plain engine calls as a fallback
            let r = null;
            try {
                r = t.op === 'expand' ? E.expandSteps(t.task) : t.op === 'factor' ? E.factorSteps(t.task) : E.simplifySteps(t.task);
            } catch {
                r = null;
            }
            const n = r?.result ?? (t.op === 'expand' ? E.expand(P(t.task)) : t.op === 'factor' ? factorNode(t.task, v) : E.simplify(P(t.task)));
            if (!n) return { status: 'refused' };
            const eq = sameFunction(n, t.answer.expr, E.freeVars(P(t.task)).length ? E.freeVars(P(t.task)) : [v]);
            return { status: eq ? 'correct' : 'wrong', got: text(n), steps: r ? r.steps.filter((st) => !st.final).length - 1 : 0 };
        }
        case 'diff': {
            const r = E.derivative(t.task, v, { steps: true });
            return { status: sameFunction(r.result, t.answer.expr, E.freeVars(P(t.task)).length > 1 ? E.freeVars(P(t.task)) : [v]) ? 'correct' : 'wrong', got: text(r.result), steps: stepsOf(r) };
        }
        case 'integrate': {
            const r = E.integrate(t.task, v, { steps: true });
            if (!r.result) return { status: 'refused', note: r.reason?.en };
            return { status: isAntiderivative(r.result, t.task, v) ? 'correct' : 'wrong', got: text(r.result), steps: stepsOf(r) };
        }
        case 'integral': {
            const [a, b] = t.bounds;
            const r = E.integrateDefinite(t.task, v, a, b, { steps: true });
            if (r.value == null && !Number.isFinite(r.numeric)) return { status: 'refused' };
            const got = r.value === 'inf' ? Infinity : r.value === '-inf' ? -Infinity : r.value ? num(r.value) : r.numeric;
            const want = t.answer.diverges ? (t.answer.value ?? Infinity) : num(t.answer.value);
            const ok = t.answer.diverges ? r.converges === false || !Number.isFinite(got) : close(got, want);
            return { status: ok ? 'correct' : 'wrong', got: r.value && typeof r.value === 'object' ? text(r.value) : got, steps: stepsOf(r), exact: !!r.exact };
        }
        case 'limit': {
            const r = E.limit(t.task, v, t.at, { steps: true, side: t.side || 'both' });
            if (r.value == null) return Number.isFinite(r.approx) ? { status: close(r.approx, num(t.answer.value)) ? 'correct' : 'wrong', got: r.approx, exact: false, steps: stepsOf(r) } : { status: 'refused' };
            const want = String(t.answer.value);
            if (r.value === 'dne' || want === 'dne') return { status: r.value === want ? 'correct' : 'wrong', got: r.value, steps: stepsOf(r) };
            const got = r.value === 'inf' ? Infinity : r.value === '-inf' ? -Infinity : num(r.value);
            return { status: close(got, num(want)) ? 'correct' : 'wrong', got: typeof r.value === 'object' ? text(r.value) : r.value, steps: stepsOf(r), exact: true };
        }
        case 'det': case 'inv': case 'rank': case 'eigen': case 'linsolve': {
            const M = E.Matrix.from(t.matrix);
            if (t.op === 'det') { const r = E.matDet(M, { steps: true }); return { status: close(num(r.value.toString()), num(t.answer.value)) ? 'correct' : 'wrong', got: r.value.toString(), steps: stepsOf(r) }; }
            if (t.op === 'rank') { const r = E.matRref(M, { steps: true }); return { status: r.rank === t.answer.value ? 'correct' : 'wrong', got: r.rank, steps: stepsOf(r) }; }
            if (t.op === 'inv') {
                const r = E.matInverse(M, { steps: true });
                if (!r.value) return { status: t.answer.none ? 'correct' : 'wrong', got: 'singular', steps: stepsOf(r) };
                const got = r.value.toArray().map((row) => row.map((q) => q.toNumber()));
                const ok = !t.answer.none && got.every((row, i) => row.every((x, j) => close(x, num(t.answer.matrix[i][j]))));
                return { status: ok ? 'correct' : 'wrong', got: JSON.stringify(got), steps: stepsOf(r) };
            }
            if (t.op === 'eigen') {
                const r = E.matEigen(M, { steps: true });
                const got = r.values.flatMap((ev) => Array(ev.multiplicity || 1).fill(ev.re)).filter((x, i, a) => true);
                const want = t.answer.values.map(num);
                const ok = sameNumbers([...new Set(got)], [...new Set(want)]);
                return { status: ok ? 'correct' : 'wrong', got: JSON.stringify(got), steps: stepsOf(r) };
            }
            const r = E.matSolve(M, t.b, { steps: true });
            if (t.answer.none) return { status: r.kind === 'none' ? 'correct' : 'wrong', steps: stepsOf(r) };
            const ok = r.kind === 'unique' && r.x.every((q, i) => close(q.toNumber(), num(t.answer.x[i])));
            return { status: ok ? 'correct' : 'wrong', got: r.kind, steps: stepsOf(r) };
        }
        case 'gcd': case 'lcm': {
            const r = t.op === 'gcd' ? E.ntGcdMany(t.args.map(BigInt), { steps: true }) : E.ntLcmMany(t.args.map(BigInt), { steps: true });
            const val = typeof r === 'bigint' ? r : r.value;
            return { status: String(val) === String(t.answer.value) ? 'correct' : 'wrong', got: String(val), steps: stepsOf(r) };
        }
        // not in the engine yet: these show what to build next
        case 'extremum': {
            if (typeof E.extremeOnSegment !== 'function') return { status: 'noapi' };
            const r = E.extremeOnSegment(t.task, v, t.segment[0], t.segment[1], { kind: t.kind, steps: true });
            if (r.kind === 'unsupported') return { status: 'refused', note: r.reason?.en };
            return { status: close(r.approx, num(t.answer.value)) ? 'correct' : 'wrong', got: text(r.value), steps: stepsOf(r), exact: !r.numeric };
        }
        case 'argext': {
            if (typeof E.extremePoints !== 'function') return { status: 'noapi' };
            const range = t.range ? t.range.map(num) : undefined;
            const r = E.extremePoints(t.task, v, { steps: true, range });
            let got = (r[t.kind] || []).map((c) => num(c.x));
            if (range) got = got.filter((q) => q > range[0] && q < range[1]);
            return { status: sameNumbers(got, t.answer.points.map(num)) ? 'correct' : 'wrong', got: JSON.stringify(got), steps: stepsOf(r) };
        }
        case 'param': return callIf('solveWithParameter', t);
        case 'ode': return callIf('solveOde', t);
        case 'series': return callIf('sumSeries', t);
        default:
            return { status: 'noapi', note: `op ${t.op}` };
    }
}

function factorNode(text0, v) {
    const p = E.Poly.fromNode(P(text0), v);
    if (!p) return null;
    const f = p.factor();
    const parts = [E.num(f.constant), ...f.factors.map(({ poly, mult }) => E.pow(poly.toNode(v), E.num(mult)))];
    return E.mul(parts);
}

function callIf(fn, t) {
    if (typeof E[fn] !== 'function') return { status: 'noapi', note: `no ${fn}()` };
    const r = E[fn](t);
    if (!r || r.kind === 'unsupported') return { status: 'refused', note: r?.reason?.en };
    const ok = t.answer.value != null ? close(num(r.value), num(t.answer.value)) : t.answer.set ? sameInterval(r.set, t.answer.set) : t.answer.expr ? sameFunction(r.expr, t.answer.expr, t.vars || ['x']) : false;
    return { status: ok ? 'correct' : 'wrong', got: r.text, steps: stepsOf(r) };
}
