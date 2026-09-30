// «Царица наук» — the maths engine. Pure ES modules, no DOM; runs in the browser and in node.
// Every module exports uniquely named symbols (a test checks), so star re-exports never collide.
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
export * from './numbers/theory/index.js';
export * from './numbers/numeric/index.js';
export * from './linalg/index.js';
export * from './calculus/derivative/index.js';
export * from './calculus/integral/index.js';
export * from './calculus/limit/index.js';
export * from './solve/index.js';
export * from './calculus/extrema.js';
export * from './algebra/values.js';
export * from './calculus/ode.js';
export * from './calculus/series.js';
export * from './solve/parameter.js';
export * from './algebra/transform.js';
export * from './generate/tasks.js';
