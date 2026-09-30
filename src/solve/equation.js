// solve/equation — the dispatcher over the method families, the numeric fallback and solveEquation.

import { compile } from '../core/evaluate.js';
import { nodeSome, containsVar, add, neg, rel, freeVars, fn, nodeKey, nodeChildren } from '../core/ast.js';
import { numFindRoots } from '../numbers/numeric/index.js';
import { simplify } from '../core/simplify.js';
import { MathError } from '../core/rational.js';
import { Poly } from '../core/poly.js';
import { numDen } from '../core/expand.js';
import { parse } from '../core/parse.js';
import { solveAbs } from './abs.js';
import { N0, S, T, approxNode, approxOf, byLang, close, exactZero, pick, tex } from './common.js';
import { checkRel, collectConds, condTex, filterFamilies, odzInfo } from './domain.js';
import { solveExponential } from './exponential.js';
import { IntervalSet, intervalTex } from './intervals.js';
import { solveCommonExp, solveLogarithmic, solveTakeLog } from './logarithmic.js';
import { productSplit, solveLinearSchool, solvePolyEquation } from './polynomial.js';
import { hasRadical, solveRadical } from './radical.js';
import { solveNodePoly, solveRational } from './rational.js';
import { answerOf, hasI, rootsOnInterval, rootsTex, sameRoot, toIntervalOpt } from './roots.js';
import { TRIG_FN, familiesToRoots, familyTex, mergeFamilies, trigCore } from './trig.js';

// ---------------------------------------------------------------- numeric fallback

const rangeTex = (a, b, lang) => `[${a};${lang === 'ru' ? '\\,' : '\\ '}${b}]`.replace(';\\ ', ',\\ ');

function solveNumeric(E, ctx) {
    const v = ctx.v;
    let f;
    try {
        f = compile(E, [v]);
    } catch {
        return { kind: 'unsupported', roots: [], steps: [], reason: T('Не умею решать такое уравнение.', 'I cannot solve this kind of equation.') };
    }
    const trig = nodeSome(E, (n) => n.type === 'fn' && TRIG_FN.includes(n.name) && containsVar(n, v));
    let range = trig ? [-2 * Math.PI, 2 * Math.PI] : [-10, 10];
    let rangeT = trig ? byLang((l) => rangeTex('-2\\pi', '2\\pi', l)) : byLang((l) => rangeTex('-10', '10', l));
    let rs = [];
    try {
        rs = numFindRoots(f, range[0], range[1], { samples: 4000 });
    } catch {
        rs = [];
    }
    if (!rs.length && !trig) {
        try {
            rs = numFindRoots(f, -100, 100, { samples: 20000 });
            range = [-100, 100];
            rangeT = byLang((l) => rangeTex('-100', '100', l));
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
        return UNSUP(T('Похоже, равенство выполняется на целых промежутках — точным методом такое уравнение здесь не решается.', 'The equality seems to hold on whole intervals; this equation is not solved exactly here.'));
    }
    const roots = rs.filter((r) => Number.isFinite(r.x)).map((r) => ({ node: approxNode(r.x), approx: r.x, mult: r.multiplicity ?? 1, approxOnly: true }));
    const steps = [S(T('Точного метода для такого уравнения нет — ищем корни численно', 'No exact method applies here, so we look for the roots numerically'), {
        text: T(`Рассматриваем $f(${v})$ = левая часть − правая часть на отрезке $${pick(rangeT, 'ru')}$: ищем, где $f$ меняет знак или касается нуля, и уточняем корни. Ответ приближённый${trig ? '; уравнение периодическое, поэтому корни за пределами отрезка тоже могут быть' : ''}.`,
            `We take $f(${v})$ = left side − right side on $${pick(rangeT, 'en')}$, look for sign changes and touching points, and refine the roots. The answer is approximate${trig ? '; the equation is periodic, so there may be roots outside the interval too' : ''}.`),
        tex: roots.length ? byLang((l) => rootsTex(roots, v, l)) : undefined,
    })];
    if (!roots.length) {
        return {
            kind: 'unsupported',
            roots: [],
            steps,
            numeric: true,
            range,
            rangeTex: rangeT,
            reason: T(`Точного метода нет, а на отрезке $${pick(rangeT, 'ru')}$ корней не нашлось.`, `There is no exact method, and no roots were found on $${pick(rangeT, 'en')}$.`),
        };
    }
    return { kind: 'roots', roots, steps, numeric: true, range, rangeTex: rangeT, type: 'numeric' };
}

// ---------------------------------------------------------------- dispatcher

const UNSUP = (reason, steps = []) => ({ kind: 'unsupported', roots: [], steps, reason });

export function solveCore(lhs, rhs, ctx) {
    const v = ctx.v;
    if (ctx.depth > 8) return UNSUP(T('Слишком много вложенных преобразований.', 'Too many nested transformations.'));
    let E;
    try {
        E = simplify(add(lhs, neg(rhs)));
    } catch (e) {
        return UNSUP(e instanceof MathError ? e.msg : T('Не удалось упростить уравнение.', 'Could not simplify the equation.'));
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
                steps: [S(T('Переменная сокращается, получается верное равенство', 'The variable cancels and a true equality remains'), {
                    tex: byLang((l) => `${tex(E, l)} = 0`),
                    text: T('Равенство верно при любом допустимом значении переменной.', 'The equality holds for every admissible value.'),
                })],
            };
        }
        return {
            kind: 'none',
            roots: [],
            type: 'identity',
            steps: [S(T('Переменная сокращается, получается неверное равенство', 'The variable cancels and a false equality remains'), {
                tex: byLang((l) => `${tex(E, l)} = 0`),
                text: T('Корней нет.', 'There are no roots.'),
            })],
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
    const steps = [S(T('Дробь равна нулю, когда числитель равен нулю, а знаменатель — нет', 'A fraction is zero when its numerator is zero and its denominator is not'), {
        tex: byLang((l) => `${tex(nd.num, l)} = 0,\\qquad ${tex(nd.den, l)} \\ne 0`),
    }), ...r.steps];
    if (dropped.length) steps.push(S(T('Отбрасываем корни, где знаменатель равен нулю', 'Drop the roots where the denominator is zero'), { tex: byLang((l) => dropped.map((x) => `${v} = ${tex(x.node, l)}`).join(',\\ ')) }));
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
    let node = relOf(input, v);
    const withSteps = opts.steps !== false;
    if (node.type === 'list') return finish({ ...UNSUP(T('Это система уравнений — для неё есть отдельный решатель.', 'This is a system of equations: it has its own solver.')) }, v, withSteps);
    if (node.type === 'chain' || node.op !== '=') return finish({ ...UNSUP(T('Это неравенство, а не уравнение.', 'This is an inequality, not an equation.')) }, v, withSteps);
    v = pickVar(node, v);
    const others = freeVars(node).filter((x) => x !== v);
    if (others.length) {
        return finish(UNSUP(T(`Кроме $${v}$ в уравнении есть другие буквы (${others.join(', ')}) — уравнения с параметрами решатель пока не решает.`, `Besides $${v}$ the equation has other letters (${others.join(', ')}); equations with parameters are not supported yet.`)), v, withSteps);
    }
    if (opts.onlyTrig && !nodeSome(node, (n) => n.type === 'fn' && TRIG_FN.includes(n.name))) {
        return finish(UNSUP(T('В уравнении нет тригонометрических функций.', 'There are no trigonometric functions in the equation.')), v, withSteps);
    }
    const ctx = { v, domain: opts.domain === 'complex' ? 'complex' : 'real', depth: 0, rejected: [] };
    const steps = [];
    const conds = collectConds(node, v);
    let odz = null;
    if (conds.length) {
        odz = odzInfo(conds, v);
        steps.push(odz.step);
        if (odz.set && odz.set.isEmpty()) {
            steps.push(S(T('ОДЗ пустая — уравнение не имеет смысла ни при каком значении', 'The domain is empty: the equation makes no sense for any value')));
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
            steps.push(S(T('Отбрасываем серии, не входящие в ОДЗ', 'Drop the series outside the domain'), {
                tex: byLang((l) => f.dropped.map((x) => familyTex(x, v, l)).join(';\\quad ')),
                text: T('В этих точках одна из частей уравнения не определена.', 'At these points a side of the equation is not defined.'),
            }));
        }
        const fams = mergeFamilies(f.kept);
        res.families = fams;
        res.roots = familiesToRoots(fams);
        if (!fams.length) res.kind = 'none';
        else {
            steps.push(S(T('Проверка', 'Check'), {
                text: f.checks.every((c) => c.ok || f.dropped.includes(c.family))
                    ? T('Подставили в уравнение несколько значений из каждой серии ($n = -2, \\ldots, 2$) — равенство выполняется.', 'We substituted several values from each series ($n = -2, \\ldots, 2$): the equality holds.')
                    : T('Некоторые значения не подошли и были исключены.', 'Some values did not fit and were excluded.'),
            }));
        }
        const iv = toIntervalOpt(opts.interval, opts.lang);
        if (iv && fams.length) {
            const sel = rootsOnInterval(fams, iv);
            if (sel) {
                res.inInterval = sel;
                steps.push(S(byLang((l) => (l === 'ru' ? `Отбираем корни на промежутке $${intervalTex(iv, l)}$` : `Pick the roots in $${intervalTex(iv, l)}$`)), {
                    tex: byLang((l) => (sel.length ? sel.map((r) => tex(r.node, l)).join(l === 'ru' ? ';\\ ' : ',\\ ') : '\\varnothing')),
                    text: T('Перебираем целые $n$, при которых значение попадает в промежуток.', 'We go through the integers $n$ that put the value into the interval.'),
                }));
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
            steps.push(S(T('Проверка подстановкой', 'Check by substitution'), {
                sub,
                text: bad.length
                    ? T(`Посторонние корни: $${bad.map(({ r }) => tex(r.node)).join(';\\ ')}$ — ${bad.some((b) => b.ch.reason === 'odz' || b.ch.reason === 'undefined') ? 'не входят в ОДЗ или не удовлетворяют уравнению' : 'не удовлетворяют исходному уравнению'}.`,
                        `Extraneous roots: $${bad.map(({ r }) => tex(r.node, 'en')).join(',\\ ')}$: ${bad.some((b) => b.ch.reason === 'odz' || b.ch.reason === 'undefined') ? 'outside the domain or not satisfying the equation' : 'they do not satisfy the original equation'}.`)
                    : needCheck ? T('Все найденные корни подходят.', 'All the roots found fit.') : T('Корни подходят.', 'The roots fit.'),
            }));
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
        out.steps.push(S(T('Ответ', 'Answer'), { tex: out.answer.tex, final: true }));
    } else if (out.reason) {
        out.steps.push(S(T('Не удалось решить точно', 'Could not solve exactly'), { text: out.reason, final: true }));
    }
    if (out.odz) out.odz = { tex: out.odz.tex, text: out.odz.text, set: out.odz.set, conditions: out.odz.conds.map((c) => ({ kind: c.kind, expr: c.expr, tex: byLang((l) => condTex(c, l)) })) };
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
                const shifted = a.type === 'add' && a.args.some((t) => (t.type === 'sym' && t.name === 'pi' && !t.var) || (t.type === 'mul' && t.args.length === 2 && t.args[0].type === 'num' && t.args[1].type === 'sym' && t.args[1].name === 'pi' && !t.args[1].var));
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
    return S(T('Формулы приведения', 'Reduction formulas'), {
        tex: byLang((l) => pairs.map(([b, a]) => `${tex(b, l)} = ${tex(a, l)}`).join(',\\quad ')),
        text: T('Сдвиг аргумента на целое число полуоборотов π или четвертей π/2 убираем по формулам приведения: функция меняется на кофункцию при сдвиге на нечётное число π/2, знак — как у исходной функции в той четверти.',
            'A shift of the argument by a multiple of π/2 is removed by the reduction formulas: an odd multiple of π/2 turns the function into its cofunction, and the sign is that of the original function in that quadrant.'),
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

/** Remember roots dropped by a sub-solver (they are reported as extraneous with the reason). */
export function reject(ctx, roots, reason) {
    if (!ctx.rejected) return;
    for (const r of roots) if (!ctx.rejected.some((x) => sameRoot(x, r))) ctx.rejected.push({ node: r.node, approx: r.approx, reason });
}

export function subSolve(lhs, rhs, ctx) {
    return solveCore(lhs, rhs, { ...ctx, depth: ctx.depth + 1 });
}
