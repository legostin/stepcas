// solve/equation — the dispatcher over the method families, the numeric fallback and solveEquation.

import { compile } from '../core/evaluate.js';
import { nodeSome, containsVar, add, neg, rel, freeVars, fn, nodeKey, nodeChildren } from '../core/ast.js';
import { numFindRoots } from '../numbers/numeric/index.js';
import { simplify } from '../core/simplify.js';
import { MathError } from '../core/rational.js';
import { Poly } from '../core/poly.js';
import { numDen } from '../core/fractions.js';
import { parse } from '../core/parse.js';
import { solveAbs } from './abs.js';
import { N0, approxNode, approxOf, close, exactZero, tex } from './common.js';
import { checkRel, collectConds, condTex, filterFamilies, odzInfo } from './domain.js';
import { solveExponential } from './exponential.js';
import { IntervalSet, intervalTex } from './intervals.js';
import { solveCommonExp, solveLogarithmic, solveTakeLog } from './logarithmic.js';
import { productSplit, solveLinearSchool, solvePolyEquation } from './polynomial.js';
import { hasRadical, solveRadical } from './radical.js';
import { solveNodePoly, solveRational } from './rational.js';
import { answerOf, hasI, rootsOnInterval, rootsTex, sameRoot, toIntervalOpt } from './roots.js';
import { TRIG_FN, trigCore } from './trig.js';
import { familiesToRoots, familyTex, mergeFamilies } from './families.js';
import { msg, notation, eachLanguage, inLanguage } from '../i18n/index.js';
import { step } from '../core/steps.js';

// ---------------------------------------------------------------- numeric fallback

const rangeTex = (a, b, lang) => `[${a}${notation(lang).intervalTex}${b}]`;

function solveNumeric(E, ctx) {
    const v = ctx.v;
    let f;
    try {
        f = compile(E, [v]);
    } catch {
        return { kind: 'unsupported', roots: [], steps: [], reason: msg('solve.equation.i_cannot_solve_this_kind_of') };
    }
    const trig = nodeSome(E, (n) => n.type === 'fn' && TRIG_FN.includes(n.name) && containsVar(n, v));
    let range = trig ? [-2 * Math.PI, 2 * Math.PI] : [-10, 10];
    let rangeT = trig ? eachLanguage((l) => rangeTex('-2\\pi', '2\\pi', l)) : eachLanguage((l) => rangeTex('-10', '10', l));
    let rs;
    try {
        rs = numFindRoots(f, range[0], range[1], { samples: 4000 });
    } catch {
        rs = [];
    }
    if (!rs.length && !trig) {
        try {
            rs = numFindRoots(f, -100, 100, { samples: 20000 });
            range = [-100, 100];
            rangeT = eachLanguage((l) => rangeTex('-100', '100', l));
        } catch {
            rs = [];
        }
    }
    let run = 0;
    let maxRun = 0;
    for (let k = 0; k <= 800; k++) {
        const y = f(range[0] + ((range[1] - range[0]) * k) / 800);
        run = Number.isFinite(y) && Math.abs(y) < 1e-12 ? run + 1 : 0;
        maxRun = Math.max(maxRun, run);
    }
    if (maxRun >= 3) {
        return UNSUP(msg('solve.equation.equality_seems_to_hold_on_whole'));
    }
    const roots = rs.filter((r) => Number.isFinite(r.x)).map((r) => ({ node: approxNode(r.x), approx: r.x, mult: r.multiplicity ?? 1, approxOnly: true }));
    const steps = [
        step({
            title: msg('solve.equation.no_exact_method_applies_here_so'),
            text: msg('solve.equation.we_take_left_side_right_side', {
                v,
                rangeT: (lng) => inLanguage(rangeT, lng),
                p: (lng) => (trig ? msg('solve.equation.equation_is_periodic_so_there_may').in(lng) : ''),
            }),
            tex: roots.length ? eachLanguage((l) => rootsTex(roots, v, l)) : undefined,
        }),
    ];
    if (!roots.length) {
        return {
            kind: 'unsupported',
            roots: [],
            steps,
            numeric: true,
            range,
            rangeTex: rangeT,
            reason: msg('solve.equation.there_is_no_exact_method_and', { rangeT: (lng) => inLanguage(rangeT, lng) }),
        };
    }
    return { kind: 'roots', roots, steps, numeric: true, range, rangeTex: rangeT, type: 'numeric' };
}

// ---------------------------------------------------------------- dispatcher

const UNSUP = (reason, steps = []) => ({ kind: 'unsupported', roots: [], steps, reason });

/**
 * Solve lhs = rhs in ctx: {v, domain: 'real' | 'complex', depth, rejected?: []}. A method solves the equations it
 * makes with ctx.solve(lhs, rhs) — the dispatcher hands itself down, so the methods never import it.
 */
export function solveCore(lhs, rhs, ctx) {
    ctx = { ...ctx, solve: (l, r) => solveCore(l, r, { ...ctx, depth: ctx.depth + 1 }) };
    const v = ctx.v;
    if (ctx.depth > 8) return UNSUP(msg('solve.equation.too_many_nested_transformations'));
    let E;
    try {
        E = simplify(add(lhs, neg(rhs)));
    } catch (e) {
        return UNSUP(e instanceof MathError ? e.msg : msg('solve.equation.could_not_simplify_equation'));
    }
    if (!containsVar(E, v)) {
        const A = containsVar(lhs, v) || containsVar(rhs, v) ? Poly.fromNode(lhs, v) : null;
        const B = A && Poly.fromNode(rhs, v);
        if (A && B && Math.max(A.degree, B.degree) >= 1) return solveLinearSchool(lhs, rhs, A, B, ctx);
        const z = exactZero(E) ?? Math.abs(approxOf(E)) < 1e-12;
        if (z) {
            return {
                kind: 'all',
                roots: [],
                type: 'identity',
                steps: [
                    step({
                        title: msg('solve.equation.variable_cancels_and_true_equality_remains'),
                        tex: eachLanguage((l) => `${tex(E, l)} = 0`),
                        text: msg('solve.equation.equality_holds_for_every_admissible_value'),
                    }),
                ],
            };
        }
        return {
            kind: 'none',
            roots: [],
            type: 'identity',
            steps: [
                step({
                    title: msg('solve.equation.variable_cancels_and_false_equality_remains'),
                    tex: eachLanguage((l) => `${tex(E, l)} = 0`),
                    text: msg('solve.equation.there_are_no_roots'),
                }),
            ],
        };
    }
    try {
        const ps = productSplit(lhs, rhs, ctx);
        if (ps) return ps;
        const P = Poly.fromNode(rel('=', lhs, rhs), v);
        if (P && P.degree >= 1) {
            if (P.degree === 1) {
                const A = Poly.fromNode(lhs, v);
                const B = Poly.fromNode(rhs, v);
                if (A && B) return solveLinearSchool(lhs, rhs, A, B, ctx);
            }
            return solvePolyEquation(lhs, rhs, P, ctx);
        }
        const tries = [
            () => solveRational(lhs, rhs, E, ctx),
            () => (nodeSome(E, (n) => n.type === 'fn' && n.name === 'abs') ? solveAbs(lhs, rhs, E, ctx) : null),
            () => {
                const r = trigCore(E, ctx);
                if (!r) return null;
                const fams = mergeFamilies(r.families);
                return { kind: fams.length ? 'roots' : 'none', roots: familiesToRoots(fams), families: fams, steps: r.steps, type: 'trig', periodic: true };
            },
            () => (hasRadical(E, v) ? solveRadical(lhs, rhs, E, ctx) : null),
            () => solveCommonExp(lhs, rhs, E, ctx),
            () => solveExponential(lhs, rhs, E, ctx),
            () => solveLogarithmic(lhs, rhs, E, ctx),
            () => solveTakeLog(lhs, rhs, E, ctx),
            () => solveNodePoly(E, ctx),
            () => solveFractionZero(E, ctx),
        ];
        for (const t of tries) {
            const r = t();
            if (r) return r;
        }
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
    }
    return solveNumeric(E, ctx);
}

/** A fraction with a non-polynomial denominator equals zero: (x² − 1)/√x = 0, 1/ln x − 1 = 0 → the numerator is zero. */
function solveFractionZero(E, ctx) {
    const v = ctx.v;
    let nd;
    try {
        nd = numDen(E);
    } catch {
        return null;
    }
    if (!nd || !containsVar(nd.den, v) || !containsVar(nd.num, v)) return null;
    const r = solveCore(nd.num, N0, { ...ctx, depth: ctx.depth + 1 });
    if (!r || (r.kind !== 'roots' && r.kind !== 'none') || r.families?.length || r.roots?.some((x) => x.approxOnly)) return null;
    const dropped = [];
    const roots = (r.roots ?? []).filter((x) => {
        const d = approxOf(nd.den, { [v]: x.approx ?? approxOf(x.node) });
        const ok = !(Math.abs(d) <= 1e-12); // NaN (outside the domain) is left to the domain check
        if (!ok) dropped.push(x);
        return ok;
    });
    const steps = [
        step({
            title: msg('solve.equation.fraction_is_zero_when_its_numerator'),
            tex: eachLanguage((l) => `${tex(nd.num, l)} = 0,\\qquad ${tex(nd.den, l)} \\ne 0`),
        }),
        ...r.steps,
    ];
    if (dropped.length)
        steps.push(
            step({
                title: msg('solve.equation.drop_roots_where_denominator_is_zero'),
                tex: eachLanguage((l) => dropped.map((x) => `${v} = ${tex(x.node, l)}`).join(',\\ ')),
            }),
        );
    return { kind: roots.length ? 'roots' : 'none', roots, steps, type: r.type ?? 'fraction' };
}

// ---------------------------------------------------------------- solveEquation

function relOf(input, v) {
    let node = typeof input === 'string' ? parse(input, { vars: v && v.length > 1 ? [v] : [] }) : input;
    if (!node || typeof node.type !== 'string') throw new TypeError('solveEquation: expected a string or a node');
    if (node.type !== 'rel' && node.type !== 'chain' && node.type !== 'list') node = rel('=', node, N0);
    return node;
}

export function pickVar(node, v) {
    const vars = freeVars(node);
    if (vars.includes(v) || !vars.length) return v;
    if (vars.length === 1) return vars[0];
    return v;
}

/**
 * Solve an equation in one variable with steps.
 * input: text or a rel node ('='); an expression means "= 0". opts: {steps: true, domain: 'real'|'complex',
 * interval: "[0; 2pi]" | [a, b] | IntervalSet — list the roots of a trig equation there, lang: 'ru' (for reading
 * the interval)}.
 * → {kind: 'roots'|'none'|'all'|'set'|'unsupported', roots: [{node, approx, mult, approxOnly?, family?}],
 *    steps, check: [{root, ok, reason, tex, text}], odz?: {tex, text, set}, answer: {tex, text}, type,
 *    families?, inInterval?, complexRoots?, set?, numeric?, range?, reason?}
 */
export function solveEquation(input, v = 'x', opts = {}) {
    const node = relOf(input, v);
    const withSteps = opts.steps !== false;
    if (node.type === 'list') return finish({ ...UNSUP(msg('solve.equation.this_is_system_of_equations_it')) }, v, withSteps);
    if (node.type === 'chain' || node.op !== '=') return finish({ ...UNSUP(msg('solve.equation.this_is_inequality_not_equation')) }, v, withSteps);
    v = pickVar(node, v);
    const others = freeVars(node).filter((x) => x !== v);
    if (others.length) {
        return finish(UNSUP(msg('solve.equation.besides_equation_has_other_letters_equations', { v, p: others.join(', ') })), v, withSteps);
    }
    if (opts.onlyTrig && !nodeSome(node, (n) => n.type === 'fn' && TRIG_FN.includes(n.name))) {
        return finish(UNSUP(msg('solve.equation.there_are_no_trigonometric_functions_in')), v, withSteps);
    }
    const ctx = { v, domain: opts.domain === 'complex' ? 'complex' : 'real', depth: 0, rejected: [] };
    const steps = [];
    const conds = collectConds(node, v);
    let odz = null;
    if (conds.length) {
        odz = odzInfo(conds, v);
        steps.push(odz.step);
        if (odz.set && odz.set.isEmpty()) {
            steps.push(step({ title: msg('solve.equation.domain_is_empty_equation_makes_no') }));
            return finish({ kind: 'none', roots: [], steps, odz, type: 'domain' }, v, withSteps);
        }
    }
    // simplify applies the reduction formulas (sin(x + π/2) → cos x) silently: say so before solving
    const red = reductionStep(node);
    if (red) steps.push(red);
    let core;
    try {
        core = solveCore(node.lhs, node.rhs, ctx);
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        core = UNSUP(e.msg);
    }
    steps.push(...core.steps);
    const res = { ...core, steps, odz, check: [] };
    if (core.kind === 'roots' && core.periodic) {
        const f = filterFamilies(core.families, node, v, conds);
        res.check = f.checks.map((c) => ({ root: approxNode(c.x), approx: c.x, n: c.n, ok: c.ok }));
        if (f.dropped.length) {
            steps.push(
                step({
                    title: msg('solve.equation.drop_series_outside_domain'),
                    tex: eachLanguage((l) => f.dropped.map((x) => familyTex(x, v, l)).join(';\\quad ')),
                    text: msg('solve.equation.at_these_points_side_of_equation'),
                }),
            );
        }
        const fams = mergeFamilies(f.kept);
        res.families = fams;
        res.roots = familiesToRoots(fams);
        if (!fams.length) res.kind = 'none';
        else {
            steps.push(
                step({
                    title: msg('solve.equation.check'),
                    text: f.checks.every((c) => c.ok || f.dropped.includes(c.family))
                        ? msg('solve.equation.we_substituted_several_values_from_each')
                        : msg('solve.equation.some_values_did_not_fit_and'),
                }),
            );
        }
        const iv = toIntervalOpt(opts.interval, opts.lang);
        if (iv && fams.length) {
            const sel = rootsOnInterval(fams, iv);
            if (sel) {
                res.inInterval = sel;
                steps.push(
                    step({
                        title: eachLanguage((l) => msg('solve.equation.pick_roots_in', { iv: intervalTex(iv, l) }).in(l)),
                        tex: eachLanguage((l) => (sel.length ? sel.map((r) => tex(r.node, l)).join(notation(l).listTex) : '\\varnothing')),
                        text: msg('solve.equation.we_go_through_integers_that_put'),
                    }),
                );
            }
        }
    } else if (core.kind === 'roots') {
        const kept = [];
        const bad = [];
        const sub = [];
        for (const r of core.roots) {
            const complex = typeof r.approx !== 'number' || (!r.approxOnly && !!r.node && hasI(r.node)) || (ctx.domain === 'complex' && hasI(node));
            const ch = checkRel(node, v, r, { conds: complex ? [] : conds, complex });
            res.check.push({ root: r.node, approx: r.approx, ok: ch.ok, reason: ch.reason, tex: ch.tex, text: ch.text });
            sub.push(...ch.steps);
            if (ch.ok) kept.push(r);
            else bad.push({ r, ch });
        }
        const needCheck = !['linear', 'quadratic', 'polynomial'].includes(core.type) || bad.length || conds.length;
        if (sub.length) {
            steps.push(
                step({
                    title: msg('solve.equation.check_by_substitution'),
                    sub,
                    text: bad.length
                        ? msg('solve.equation.extraneous_roots', {
                              p: (lng) => bad.map(({ r }) => tex(r.node, lng)).join(notation(lng).listTex),
                              p2: (lng) =>
                                  bad.some((b) => b.ch.reason === 'odz' || b.ch.reason === 'undefined')
                                      ? msg('solve.equation.outside_domain_or_not_satisfying_equation').in(lng)
                                      : msg('solve.equation.they_do_not_satisfy_original_equation').in(lng),
                          })
                        : needCheck
                          ? msg('solve.equation.all_roots_found_fit')
                          : msg('solve.equation.roots_fit'),
                }),
            );
        }
        res.roots = kept;
        res.extraneous = [...ctx.rejected, ...bad.map(({ r, ch }) => ({ node: r.node, approx: r.approx, reason: ch.reason }))]
            .filter((x, k, all) => typeof x.approx !== 'number' || all.findIndex((y) => typeof y.approx === 'number' && close(y.approx, x.approx, 1e-9)) === k)
            .filter((x) => !kept.some((r) => sameRoot(r, x)))
            .sort((a, b) => (typeof a.approx === 'number' && typeof b.approx === 'number' ? a.approx - b.approx : 0));
        if (!kept.length) res.kind = 'none';
    } else if (core.kind === 'all' || core.kind === 'set') {
        let set = core.set ?? IntervalSet.all();
        if (odz?.set) set = set.intersect(odz.set);
        res.set = set;
        res.odzPartial = !!odz?.partial;
        if (set.isEmpty()) res.kind = 'none';
    }
    return finish(res, v, withSteps);
}

function finish(res, v, withSteps) {
    const out = { roots: [], steps: [], check: [], ...res, v };
    out.answer = answerOf(out, v);
    if (out.kind !== 'unsupported' && out.kind !== undefined) {
        out.steps.push(step({ title: msg('solve.equation.answer'), tex: out.answer.tex, final: true }));
    } else if (out.reason) {
        out.steps.push(step({ title: msg('solve.equation.could_not_solve_exactly'), text: out.reason, final: true }));
    }
    if (out.odz)
        out.odz = {
            tex: out.odz.tex,
            text: out.odz.text,
            set: out.odz.set,
            conditions: out.odz.conds.map((c) => ({ kind: c.kind, expr: c.expr, tex: eachLanguage((l) => condTex(c, l)) })),
        };
    if (!withSteps) out.steps = [];
    return out;
}

// The reduction formulas simplify applies to what was typed: sin(π − x) = sin x, cos(x + π/2) = −sin x, …
function reductionStep(node) {
    const pairs = [];
    const seen = new Set();
    const walk = (n) => {
        if (n.type === 'fn' && ['sin', 'cos', 'tan', 'cot', 'sec', 'csc'].includes(n.name)) {
            try {
                const a = simplify(n.args[0]);
                const shifted =
                    a.type === 'add' &&
                    a.args.some(
                        (t) =>
                            (t.type === 'sym' && t.name === 'pi' && !t.var) ||
                            (t.type === 'mul' &&
                                t.args.length === 2 &&
                                t.args[0].type === 'num' &&
                                t.args[1].type === 'sym' &&
                                t.args[1].name === 'pi' &&
                                !t.args[1].var),
                    );
                if (shifted) {
                    const canon = fn(n.name, a);
                    const after = simplify(canon);
                    const k = nodeKey(canon);
                    if (nodeKey(after) !== k && !seen.has(k)) {
                        seen.add(k);
                        pairs.push([n, after]); // as typed: cos(π/2 − x) = sin x
                    }
                }
            } catch {
                /* left for the solver to report */
            }
        }
        for (const c of nodeChildren(n)) walk(c);
    };
    walk(node);
    if (!pairs.length) return null;
    return step({
        title: msg('solve.equation.reduction_formulas'),
        tex: eachLanguage((l) => pairs.map(([b, a]) => `${tex(b, l)} = ${tex(a, l)}`).join(',\\quad ')),
        text: msg('solve.equation.shift_of_argument_by_multiple_of'),
        rule: 'reduction',
    });
}

/**
 * Trigonometric equations: sin/cos/tg/ctg of a linear argument = a, polynomial in one function, homogeneous,
 * a·sin + b·cos = c, double angles. Same result shape as solveEquation (roots are families x = base + period·n,
 * `families` holds them, `answer` prints the school form); opts.interval lists the roots in [α; β].
 */
export function solveTrig(input, v = 'x', opts = {}) {
    return solveEquation(input, v, { ...opts, onlyTrig: true });
}
