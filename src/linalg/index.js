// linalg — exact linear algebra over Q with step-by-step explanations, plus a float toolkit for widgets.
//
//   const A = Matrix.from([[2, 1], [1, 2]]);        entries: numbers, strings ('1/2', '0,5'), BigInt or Q
//   matRref(A, {steps: true}) → {matrix, pivots, rank, ops, steps}
//   matEigen(A) → {charPoly, values: [{kind: 'rational', value: Q, vectors, …}, …]}
//
// Convention as in the rest of the engine: a function returns its bare value; {steps: true} returns
// {value, steps, …} (functions whose result is already an object just gain `steps`). Rows and columns
// are 0-based in data (i, j) and 1-based in explanations (R₁, R₂; x₁, x₂). RU uses E for the identity
// matrix, EN uses I.
//
// Layout: common (helpers), core (the Matrix class), reduce (row reduction), det (determinants), systems (inverse, linear systems,
// Cramer), qpoly (polynomials over Q), eigen (characteristic polynomial, eigenvalues, diagonalisation), orthogonal
// (Gram–Schmidt, projections, least squares), float (the float toolkit for widgets).
export { Matrix } from './core.js';
export { matNullspace, matRank, matRref } from './reduce.js';
export { matDet } from './det.js';
export { matInverse, matSolve, matSolveCramer } from './systems.js';
export { matCharPoly, matDiagonalize, matEigen, matPower } from './eigen.js';
export { matGramSchmidt, matLeastSquares, matProjection } from './orthogonal.js';
export { fmatEigSym, fmatInv, fmatLowRank, fmatMul, fmatQr, fmatSolve, fmatSvd, fmatSvdTruncated, fmatTranspose } from './float.js';
