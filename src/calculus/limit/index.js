// calculus/limit — limits with steps in the style of a Russian university course: substitution, «limit
// arithmetic» with infinities, and for indeterminate forms: factor and cancel (rational functions),
// divide by the highest power (x → ±∞), the conjugate for differences of roots, equivalent infinitesimals
// (sin u ~ u, 1 − cos u ~ u²/2, eᵘ − 1 ~ u, ln(1 + u) ~ u, (1 + u)ᵃ − 1 ~ au, …), the second remarkable
// limit for 1^∞, e^(lim v·ln u) for 0⁰ and ∞⁰, and L'Hôpital's rule (at most 5 rounds, only for 0/0 and ∞/∞).
// Every answer comes with a table of values approaching the point and is cross-checked against it; when
// the symbolic methods fail, the numeric estimate is returned and clearly marked ≈.
// Also: taylorPolynomial (exact coefficients f⁽ᵏ⁾(a)/k!) and taylorRemainderBound (Lagrange form, numeric M).
//
// Layout: common (the point, limit values), evaluator (limit arithmetic on the tree), forms (indeterminate forms and
// their methods), table (the numeric table and check), limit (the public API), taylor.
export { limit } from './limit.js';
export { taylorPolynomial, taylorRemainderBound } from './taylor.js';
