// solve — equations, inequalities and systems with school-style steps («что делаем и почему»).
//
//   solveEquation(input, v = 'x', {steps, domain: 'real'|'complex', interval})  → roots, steps, check, ОДЗ
//   solveTrig(input, v, opts)                  → the same shape, trigonometric equations only
//   solveInequality(input, v, {steps})         → {set: IntervalSet, steps, signChart}
//   solveLinearSystem(rels, vars, {method})    → unique / none / infinite (parametric)
//   solveSystem2(rels, vars)                   → a linear and a quadratic equation, by substitution
//   checkRoot(rel, v, value)                   → substitution with steps
//   domainSet(f, v)                            → where a function is defined
//   IntervalSet, intervalTex, intervalText, parseIntervalSet, intervalEquals — answers as sets
//
// Correctness first: every root found by a transformation that may add roots (squaring, multiplying by an
// expression, combining logarithms, substitution) is checked by substitution into the original equation and
// against the ОДЗ; roots that fail are listed as extraneous with the reason. When no exact method applies the
// solver says so and, where it makes sense, gives numeric roots marked «≈» together with the search range.
//
// Layout: common (helpers), intervals (IntervalSet), domain (ОДЗ), roots (answers), polynomial, rational, abs,
// radical, exponential, logarithmic, trig — one method family each; equation (the dispatcher and solveEquation),
// signs (the method of intervals), inequality, systems.
export { IntervalSet, intervalEquals, intervalTex, intervalText, parseIntervalSet } from './intervals.js';
export { checkRoot } from './domain.js';
export { solveEquation, solveTrig } from './equation.js';
export { domainSet, solveInequality } from './inequality.js';
export { solveLinearSystem, solveSystem2 } from './systems.js';
