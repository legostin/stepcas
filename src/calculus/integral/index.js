// calculus/integral — antiderivatives with steps: a cascade of methods, each one explaining why it applies; definite integrals
// (Newton–Leibniz, improper integrals as limits, a numeric value marked ≈ otherwise) and the area between curves.
//
// Cascade (on the canonical form of simplify.js): constant → table → linearity → linear substitution f(kx + b) →
// rational functions (division, partial fractions over Q, completing the square) → expand → trigonometric forms
// (odd powers, power reduction, t = tg x, product to sum) → u-substitution g(h(x))·h′(x) → quadratics under a root →
// rationalising substitution t = ⁿ√(ax + b) → integration by parts (LIATE, repeated, cyclic eᵃˣ·sin bx) → universal
// substitution t = tg(x/2). Every candidate antiderivative is checked by differentiating it back and comparing with
// the integrand at sample points of its domain; an answer that fails the check is never shown.
//
// Layout: common (helpers, positivity, the check), engine (the recursive integrator and the cascade), basic, rational,
// trig, substitution, radicals, parts — the method families; integrate (the public entry, non-elementary hints),
// definite (definite and improper integrals, areas).
export { integrate } from './integrate.js';
export { areaBetween, integrateDefinite } from './definite.js';
