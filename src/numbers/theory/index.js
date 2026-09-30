// numbers/theory — number theory on BigInt with step-by-step explanations.
//
// Inputs: BigInt, integer numbers, digit strings ("600 851 475 143"), and — where a fraction makes
// sense — Q, "a/b", "0,1", "0.(3)". Outputs: BigInt (or arrays/objects of BigInt).
// Convention: a function returns its bare value; called with {steps: true} it returns
// {value, steps, ...extra}. Functions whose natural result is already an object (ntEgcd,
// ntDiophantine, ntSolveCongruence, ntCrt, ntMillerRabin, ntContinuedFraction, ntRsaKey,
// ntDivisibilityRule) just gain a `steps` field. Steps have the shape of core/steps.js.
//
// Layout: common, gcd (gcd, lcm, extended Euclid, Diophantine), primes (primality, factorisation, primes, φ, τ, σ),
// modular, bases, fractions (continued fractions, Egyptian fractions), divisibility (rules).
export { ntDiophantine, ntEgcd, ntGcd, ntGcdMany, ntLcm, ntLcmMany } from './gcd.js';
export {
    ntDigitSum,
    ntDivisors,
    ntFactor,
    ntFactorTex,
    ntIsCarmichael,
    ntIsPerfectSquare,
    ntIsPrime,
    ntMillerRabin,
    ntMobius,
    ntNextPrime,
    ntPhi,
    ntPrevPrime,
    ntPrimePi,
    ntPrimesUpTo,
    ntSieve,
    ntSigma,
    ntTau,
} from './primes.js';
export { ntCrt, ntModInv, ntModPow, ntOrder, ntPrimitiveRoot, ntRsaKey, ntSolveCongruence } from './modular.js';
export { ntFromBase, ntToBase } from './bases.js';
export { ntBestApprox, ntContinuedFraction, ntConvergents, ntEgyptian } from './fractions.js';
export { ntDivisibilityRule } from './divisibility.js';
