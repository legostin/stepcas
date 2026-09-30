// calculus/derivative — symbolic derivatives with a step tree that mirrors the expression («что делаем и почему»),
// higher and partial derivatives, the gradient and the tangent line.
//
// derivative(f, 'x', {steps}) walks the tree as the person typed it (sum → sum rule, product → product
// rule, f(g(x)) → chain rule with the inner function named, …); every node shows (…)' = rule = assembled =
// clean. The clean form is picked among equivalent candidates (canonical, one fraction, common factor
// taken out, sin/cos → tg/ctg) by the length of its TeX, and every result is checked numerically
// (against an independent fast derivative and against central differences of f).
// Also exported for the other calculus modules: quickDerivative (fast canonical derivative), niceForm (tidy
// equivalent form), derivativeOf (the simplified derivative without steps). The display form and TeX of calculus
// answers live in calculus/display.js.
//
// Layout: quick (the fast canonical derivative), clean (the clean form), steps (the step tree and its lines),
// derivative (the numeric check and the public API).
export { quickDerivative } from './quick.js';
export { niceForm, ratFunctionOf } from './clean.js';
export { derivative, derivativeN, derivativeOf, gradientOf, partialDerivative, tangentLine } from './derivative.js';
