// numbers/numeric — floating-point numerical methods for widgets, simulators, plots and checks.
//
// Everything works on doubles. Root finders return {root, iterations, converged, …}; integrals
// and derivatives return a number (pass {info: true} for {value, error, …}). Invalid input throws
// MathError with a message. docs/API.md has the full contract.
//
// Layout: common, roots (root finders, optimisation), calculus (derivatives, integrals), ode, sampling (plots),
// signals (DFT/FFT, Fourier), statistics (with special functions and probability), interpolation.
export { numLinspace } from './common.js';
export { numBisect, numBrent, numExtrema, numFindRoots, numGoldenMin, numNewton } from './roots.js';
export { numDerivative, numIntegrate, numIntegrateInfo, numRiemann } from './calculus.js';
export { numEuler, numOdeAdaptive, numRk4, odeLorenz, odeLotkaVolterra, odePendulum, odeSir } from './ode.js';
export { sampleFunction } from './sampling.js';
export { numDft, numFft, numFourierCoefficients, numFourierEval, numIfft } from './signals.js';
export {
    numGamma,
    numLogGamma,
    probArrangements,
    probBetaRegularized,
    probBinomialCdf,
    probBinomialPmf,
    probChiSquareCdf,
    probChoose,
    probErf,
    probErfc,
    probFactorial,
    probGammaRegularized,
    probGeometricCdf,
    probGeometricPmf,
    probNormalCdf,
    probNormalInv,
    probNormalPdf,
    probPoissonCdf,
    probPoissonPmf,
    probStudentTCdf,
    probStudentTInv,
    statCorrelation,
    statLinearRegression,
    statMean,
    statMedian,
    statMode,
    statPolyFit,
    statQuantile,
    statStd,
    statVariance,
} from './statistics.js';
export { numLagrange, numPolyRoots } from './interpolation.js';
