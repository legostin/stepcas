// stepcas — a computer algebra system that shows its work. Pure ES modules, no DOM; runs in the browser and in node.
//
// Layers, each using only the ones above it:
//   i18n      messages in catalogs, languages, notation
//   core      numbers (Q), expressions (AST), parse, print, simplify, polynomials, steps
//   domains   numbers (theory, numerics) · linalg · algebra · solve · calculus · generate
//   api       the solvers with one contract: {ok, kind, answer, steps, reason, …}
// Every exported name is unique (a test checks), so the star re-exports never collide.

// languages
export * from './i18n/index.js';

// building blocks
export * from './core/rational.js';
export * from './core/ast.js';
export * from './core/parse.js';
export * from './core/print.js';
export * from './core/simplify.js';
export * from './core/expand.js';
export * from './core/poly.js';
export * from './core/equiv.js';
export * from './core/evaluate.js';
export * from './core/complex.js';
export * from './core/random.js';
export * from './core/steps.js';

// calculators: a bare value, or {value, steps} with {steps: true}
export * from './numbers/theory/index.js';
export * from './numbers/numeric/index.js';
export * from './linalg/index.js';

// helpers of the domains (sets of answers, display forms)
export { IntervalSet, intervalTex, intervalText, parseIntervalSet, intervalEquals, domainSet } from './solve/index.js';
export { calcTex, calcTexBoth, prettyForm, niceForm, quickDerivative, ratFunctionOf } from './calculus/derivative/index.js';
export { taylorRemainderBound } from './calculus/limit/index.js';
export { exactGuess } from './calculus/extrema.js';

// task generators
export * from './generate/tasks.js';

// the solvers
export * from './api.js';
