// api — the public face of the solvers: one contract for every function that explains its answer.
//
//   const r = solveEquation('x^2 = 4');
//   r.ok       true when there is an answer
//   r.kind     what the answer is — 'roots', 'none', 'all', 'set', 'value', 'antiderivative', 'expression', … —
//              or 'invalid' (the input does not parse) or 'unsupported' (the solver cannot do it yet)
//   r.answer   {tex, text}: messages or per-language values, read with .ru / .en / .in(lang) or localize(r, lang)
//   r.steps    the explanation — built unless the options say {steps: false}
//   r.reason   why there is no answer (a message); r.pos and r.len point into the input for an input error
//   …          the solver's own fields: roots, set, value, result, expr, method, …
//
// Nothing here throws on what a person types: a parse error comes back as {ok: false, kind: 'invalid'}. A thrown error
// is a bug. Inside the engine the modules call each other directly; this layer is only for callers from outside.
// Calculators (ntGcd, matDet, numIntegrate, …) keep their own convention: a bare value, or {value, steps} with
// {steps: true}.
import { MathError } from './core/rational.js';
import { toText } from './core/print.js';
import { texBoth } from './core/steps.js';
import { msg, eachLanguage } from './i18n/index.js';
import {
    solveEquation as solveEquation0,
    solveTrig as solveTrig0,
    solveInequality as solveInequality0,
    solveLinearSystem as solveLinearSystem0,
    solveSystem2 as solveSystem20,
    checkRoot as checkRoot0,
} from './solve/index.js';
import { solveWithParameter as solveWithParameter0 } from './problems/parameter.js';
import {
    derivative as derivative0,
    partialDerivative as partialDerivative0,
    derivativeN as derivativeN0,
    gradientOf as gradientOf0,
    tangentLine as tangentLine0,
} from './calculus/derivative/index.js';
import { integrate as integrate0, integrateDefinite as integrateDefinite0, areaBetween as areaBetween0 } from './calculus/integral/index.js';
import { limit as limit0, taylorPolynomial as taylorPolynomial0 } from './calculus/limit/index.js';
import { extremeOnSegment as extremeOnSegment0, extremePoints as extremePoints0 } from './calculus/extrema.js';
import { solveOde as solveOde0 } from './calculus/ode.js';
import { sumSeries as sumSeries0 } from './calculus/series.js';
import { evaluateSteps as evaluateSteps0 } from './algebra/values.js';
import { factorSteps as factorSteps0, expandSteps as expandSteps0, simplifySteps as simplifySteps0 } from './algebra/transform.js';

/**
 * @import { Node } from './core/ast.js'
 * @import { Step } from './core/steps.js'
 * @import { Text } from './i18n/index.js'
 * @import { IntervalSet } from './solve/index.js'
 */
/**
 * @typedef {string | Node} Input  an expression as text (parsed) or as a node
 * @typedef {{steps?: boolean, lang?: string, [option: string]: unknown}} Options
 * @typedef {{tex: Text, text: Text}} Answer
 */
/**
 * A solver's answer: `kind` says what it is, the solver's own fields come along.
 * @template {string} K
 * @template [X={}]
 * @typedef {{ok: true, kind: K, answer: Answer, steps: Step[]} & X & Record<string, any>} Solved
 */
/**
 * No answer: the input does not parse ('invalid', with pos and len) or the solver cannot do it ('unsupported').
 * @typedef {{ok: false, kind: 'invalid' | 'unsupported', reason: Text, steps: Step[], pos?: number, len?: number, code?: string}} Failed
 */
/**
 * @template {string} K
 * @template [X={}]
 * @typedef {Solved<K, X> | Failed} Result
 */
/**
 * @typedef {{node: Node, approx: number | {re: number, im: number}, mult: number, approxOnly?: boolean, family?: {base: Node, period: Node, param: string}}} Root
 */

const INPUT_ERRORS = new Set(['syntax', 'brackets', 'empty', 'no-arg', 'arity', 'unknown-fn', 'not-expr', 'too-big']);

// a node as text in every language (the plain text people type back)
const textOf = (node) => eachLanguage((lang) => toText(node, { lang }));
const answerOf = (node) => ({ tex: texBoth(node), text: textOf(node) });

/**
 * Wrap a solver in the contract. spec: {opts: index of the options argument, ok(r), kind(r) (default r.kind),
 * answer(r) (default r.answer), extra(r) (fields to add), rename: {field: newName} (fields whose names the contract
 * uses for something else)}.
 */
function solver(fn, spec) {
    return function (...args) {
        while (args.length < spec.opts) args.push(undefined);
        args[spec.opts] = { steps: true, ...(args[spec.opts] ?? {}) };
        let r;
        try {
            r = fn(...args);
        } catch (e) {
            if (!(e instanceof MathError)) throw e;
            return { ok: false, kind: INPUT_ERRORS.has(e.code) ? 'invalid' : 'unsupported', reason: e.msg, pos: e.pos, len: e.len, code: e.code, steps: [] };
        }
        if (r == null) return { ok: false, kind: 'unsupported', reason: msg('api.unsupported'), steps: [] };
        const ok = !!spec.ok(r);
        const out = { ...r, ...(spec.extra ? spec.extra(r) : {}) };
        for (const [from, to] of Object.entries(spec.rename ?? {})) {
            out[to] = r[from];
            delete out[from];
        }
        out.ok = ok;
        out.steps = r.steps ?? [];
        if (ok) {
            out.kind = spec.kind ? spec.kind(r) : r.kind;
            out.answer = spec.answer ? spec.answer(r) : r.answer;
        } else {
            out.kind = r.kind === 'invalid' ? 'invalid' : 'unsupported';
            out.reason = r.reason ?? msg('api.unsupported');
            delete out.answer;
        }
        return out;
    };
}

const notUnsupported = (r) => r.kind !== 'unsupported';

/* ------------------------------------------------------------------ equations, inequalities, systems */

/**
 * Solve an equation in one unknown: solveEquation('x^2 = 4', 'x', {domain, interval}).
 * @type {(input: Input, v?: string | null, opts?: Options & {domain?: 'real' | 'complex', interval?: unknown}) => Result<'roots' | 'none' | 'all' | 'set', {roots: Root[], set?: IntervalSet, type: string}>}
 */
export const solveEquation = solver(solveEquation0, { opts: 2, ok: notUnsupported });
/**
 * A trigonometric equation: families of roots, selection on a segment.
 * @type {(input: Input, v?: string | null, opts?: Options & {interval?: unknown}) => Result<'roots' | 'none' | 'all' | 'set', {roots: Root[], families?: unknown[]}>}
 */
export const solveTrig = solver(solveTrig0, { opts: 2, ok: notUnsupported });
/**
 * An inequality (also a double one): the answer is a set.
 * @type {(input: Input, v?: string | null, opts?: Options) => Result<'set', {set: IntervalSet}>}
 */
export const solveInequality = solver(solveInequality0, { opts: 2, ok: (r) => !!r.set, kind: () => 'set' });
/**
 * A linear system: unique, none or infinite (parametric) solutions.
 * @type {(rels: Input | Input[], vars?: string[] | null, opts?: Options & {method?: 'substitution' | 'addition' | 'cramer' | 'gauss'}) => Result<'unique' | 'none' | 'infinite', {solution?: Record<string, Node>, general?: Record<string, Node>, params?: string[]}>}
 */
export const solveLinearSystem = solver(solveLinearSystem0, { opts: 2, ok: notUnsupported });
/**
 * Two equations, a linear and a quadratic one, by substitution.
 * @type {(rels: Input | Input[], vars?: string[] | null, opts?: Options) => Result<'solutions' | 'none', {solutions: Record<string, Node>[]}>}
 */
export const solveSystem2 = solver(solveSystem20, { opts: 2, ok: notUnsupported });
/**
 * Is value a root? Substitution with steps; the verdict is isRoot, and why says what failed ('mismatch', 'odz', …).
 * @type {(rel: Input, v: string, value: Input | number, opts?: Options & {complex?: boolean}) => Result<'root' | 'not-root', {isRoot: boolean, why: string | null}>}
 */
export const checkRoot = solver(checkRoot0, {
    opts: 3,
    ok: () => true,
    kind: (r) => (r.ok ? 'root' : 'not-root'),
    rename: { ok: 'isRoot', reason: 'why' },
    answer: (r) => ({ tex: r.tex, text: r.text }),
});
/**
 * For which values of a parameter does an equation have the wanted number of roots?
 * @type {(input: Input | {task: Input, param?: string, want?: unknown}, opts?: Options & {param?: string, v?: string, want?: 'two-roots' | 'one-root' | 'has-roots' | 'no-roots' | number}) => Result<'set', {set: IntervalSet}>}
 */
export const solveWithParameter = solver(solveWithParameter0, { opts: 1, ok: notUnsupported });

/* ------------------------------------------------------------------ calculus */

const derivativeSpec = (opts) => ({ opts, ok: (r) => !!r.result, kind: () => 'derivative', answer: (r) => ({ tex: r.tex, text: textOf(r.result) }) });
/**
 * The derivative with a step tree that mirrors the expression.
 * @type {(f: Input, v?: string, opts?: Options & {simplify?: boolean}) => Result<'derivative', {result: Node}>}
 */
export const derivative = solver(derivative0, derivativeSpec(2));
/**
 * A partial derivative.
 * @type {(f: Input, v?: string, opts?: Options) => Result<'derivative', {result: Node}>}
 */
export const partialDerivative = solver(partialDerivative0, derivativeSpec(2));
/**
 * The n-th derivative.
 * @type {(f: Input, v?: string, n?: number, opts?: Options) => Result<'derivative', {result: Node, list: Node[]}>}
 */
export const derivativeN = solver(derivativeN0, derivativeSpec(3));
/**
 * The gradient of a function of several variables.
 * @type {(f: Input, vars?: string[] | null, opts?: Options) => Result<'gradient', {result: Node, components: Node[]}>}
 */
export const gradientOf = solver(gradientOf0, {
    opts: 2,
    ok: (r) => !!r.components,
    kind: () => 'gradient',
    answer: (r) => ({ tex: r.tex, text: eachLanguage((lang) => `(${toText(r.result, { lang })})`) }),
});
/**
 * The tangent line at a point.
 * @type {(f: Input, v?: string, a?: Input | number, opts?: Options) => Result<'line', {line: Node, k: Node, b: Node}>}
 */
export const tangentLine = solver(tangentLine0, { opts: 3, ok: (r) => !!r.line, kind: () => 'line', answer: (r) => ({ tex: r.tex, text: textOf(r.line) }) });
/**
 * An antiderivative, with the method that found it.
 * @type {(f: Input, v?: string, opts?: Options) => Result<'antiderivative', {result: Node, method: string}>}
 */
export const integrate = solver(integrate0, {
    opts: 2,
    ok: (r) => !!r.result,
    kind: () => 'antiderivative',
    answer: (r) => ({ tex: r.tex, text: eachLanguage((lang) => `${toText(r.result, { lang })} + C`) }),
});

const definiteKind = (r) => (r.converges === false ? 'diverges' : r.value != null && typeof r.value === 'object' ? 'value' : 'approx');
const definiteText = (r) =>
    r.converges === false ? msg('api.diverges') : r.value != null && typeof r.value === 'object' ? textOf(r.value) : String(r.numeric);
/**
 * A definite (also improper) integral: exact, numeric or divergent.
 * @type {(f: Input, v?: string, a?: Input | number, b?: Input | number, opts?: Options) => Result<'value' | 'approx' | 'diverges', {value: Node | 'inf' | '-inf' | null, numeric: number}>}
 */
export const integrateDefinite = solver(integrateDefinite0, {
    opts: 4,
    ok: (r) => (r.value != null && typeof r.value === 'object') || Number.isFinite(r.numeric) || r.converges === false,
    kind: definiteKind,
    answer: (r) => ({ tex: r.tex, text: definiteText(r) }),
});
/**
 * The area between two curves.
 * @type {(f: Input, g: Input, v?: string, a?: Input | number, b?: Input | number, opts?: Options) => Result<'value' | 'approx', {value: Node | null, numeric: number}>}
 */
export const areaBetween = solver(areaBetween0, {
    opts: 5,
    ok: (r) => (r.value != null && typeof r.value === 'object') || Number.isFinite(r.numeric),
    kind: definiteKind,
    answer: (r) => ({ tex: r.tex, text: definiteText(r) }),
});

const limitKind = (r) =>
    r.value === 'dne' ? 'dne' : r.value === 'inf' || r.value === '-inf' ? 'infinite' : r.value && typeof r.value === 'object' ? 'value' : 'approx';
const limitText = (r) =>
    r.value === 'dne'
        ? msg('api.does_not_exist')
        : r.value === 'inf'
          ? '+∞'
          : r.value === '-inf'
            ? '-∞'
            : r.value && typeof r.value === 'object'
              ? textOf(r.value)
              : `≈ ${r.approx}`;
/**
 * A limit at a point or at ±∞, with the method and a table of values.
 * @type {(f: Input, v?: string, a?: Input | number, opts?: Options & {side?: 'both' | 'left' | 'right'}) => Result<'value' | 'infinite' | 'dne' | 'approx', {value: Node | 'inf' | '-inf' | 'dne' | null, approx?: number}>}
 */
export const limit = solver(limit0, {
    opts: 3,
    ok: (r) => r.value != null || Number.isFinite(r.approx),
    kind: limitKind,
    answer: (r) => ({ tex: r.tex, text: limitText(r) }),
});
/**
 * A Taylor polynomial with exact coefficients.
 * @type {(f: Input, v?: string, a?: Input | number, n?: number, opts?: Options) => Result<'polynomial', {poly: Node, coeffs: Node[]}>}
 */
export const taylorPolynomial = solver(taylorPolynomial0, {
    opts: 4,
    ok: (r) => !!r.poly,
    kind: () => 'polynomial',
    answer: (r) => ({ tex: r.tex, text: textOf(r.poly) }),
});
/**
 * The greatest or least value on a segment; the kind asked for stays in `extremum`.
 * @type {(f: Input, v: string, a: Input | number, b: Input | number, opts?: Options & {kind?: 'max' | 'min'}) => Result<'value', {value: Node, at: Node, extremum: string}>}
 */
export const extremeOnSegment = solver(extremeOnSegment0, {
    opts: 4,
    ok: notUnsupported,
    kind: () => 'value',
    extra: (r) => ({ extremum: r.kind }),
    answer: (r) => ({ tex: r.tex, text: r.value ? textOf(r.value) : r.text }),
});
/**
 * Points of extremum by the sign of the derivative.
 * @type {(f: Input, v?: string, opts?: Options) => Result<'points', {max: {x: Node}[], min: {x: Node}[], critical: unknown[]}>}
 */
export const extremePoints = solver(extremePoints0, {
    opts: 2,
    ok: (r) => Array.isArray(r.critical),
    kind: () => 'points',
    answer: (r) => ({
        tex: eachLanguage(
            (lang) =>
                [
                    r.max.length ? `x_{\\max} = ${r.max.map((c) => toText(c.x, { lang })).join(', ')}` : null,
                    r.min.length ? `x_{\\min} = ${r.min.map((c) => toText(c.x, { lang })).join(', ')}` : null,
                ]
                    .filter(Boolean)
                    .join(',\\quad ') || '\\varnothing',
        ),
        text: eachLanguage(
            (lang) => `max: ${r.max.map((c) => toText(c.x, { lang })).join(', ') || '—'}; min: ${r.min.map((c) => toText(c.x, { lang })).join(', ') || '—'}`,
        ),
    }),
});
/**
 * An ordinary differential equation with initial conditions after «;».
 * @type {(input: string, opts?: Options) => Result<'solution' | 'general', {expr: Node, general: Node, type: string}>}
 */
export const solveOde = solver(solveOde0, { opts: 1, ok: notUnsupported, answer: (r) => ({ tex: r.tex, text: r.text }) });
/**
 * The sum of a series: sum(term, k, start, end).
 * @type {(input: string, opts?: Options) => Result<'value' | 'diverges' | 'approx', {value?: Node, approx?: number, type: string}>}
 */
export const sumSeries = solver(sumSeries0, {
    opts: 1,
    ok: notUnsupported,
    answer: (r) =>
        r.kind === 'value'
            ? answerOf(r.value)
            : r.kind === 'diverges'
              ? { tex: msg('api.diverges_tex'), text: msg('api.diverges') }
              : { tex: `S \\approx ${r.approx}`, text: r.text },
});

/* ------------------------------------------------------------------ algebra */

/**
 * The value of a numeric expression step by step.
 * @type {(input: Input, opts?: Options & {maxSteps?: number}) => Result<'value', {value: Node, approx: number, exact: boolean}>}
 */
export const evaluateSteps = solver(evaluateSteps0, { opts: 1, ok: (r) => r.value != null, kind: () => 'value', answer: (r) => answerOf(r.value) });
const expressionSpec = { opts: 1, ok: (r) => !!r.result, kind: () => 'expression', answer: (r) => answerOf(r.result) };
/**
 * Factor a polynomial with the school formulas.
 * @type {(input: Input, opts?: Options) => Result<'expression', {result: Node}>}
 */
export const factorSteps = solver(factorSteps0, expressionSpec);
/**
 * Open the brackets and collect like terms.
 * @type {(input: Input, opts?: Options) => Result<'expression', {result: Node}>}
 */
export const expandSteps = solver(expandSteps0, expressionSpec);
/**
 * Reduce a fraction (with its excluded values) or expand a polynomial.
 * @type {(input: Input, opts?: Options) => Result<'expression', {result: Node}>}
 */
export const simplifySteps = solver(simplifySteps0, expressionSpec);
