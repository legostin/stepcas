// integral/engine — the recursive integrator: tries the cascade of methods, memoises, keeps only checked answers.

import { nodeKey } from '../../core/ast.js';
import { MathError } from '../../core/rational.js';
import { mConst, mDerivPattern, mExpand, mLinearSub, mLinearity, mTable } from './basic.js';
import { checkAnti, simp } from './common.js';
import { mParts, mPolyTimes } from './parts.js';
import { mQuadRoot, mRadicalPoly } from './radicals.js';
import { mBiquadratic, mRational } from './rational.js';
import { mRationalizing, mUSub } from './substitution.js';
import { mCyclic, mTrig, mTrigLower, mTrigSub, mWeierstrass } from './trig.js';

// ---------------------------------------------------------------- the recursive integrator

/**
 * I(f, ctx) → {F, step, method} | null for a canonical integrand f. ctx: {v (the variable), depth, budget: {calls,
 * max, memo}, parts? (integrations by parts so far)}; a method gets ctx.integrate as well.
 * Each method returns a candidate; a candidate that fails checkAnti is dropped and the next method tried.
 */
export function I(f, ctx) {
    const b = ctx.budget;
    if (++b.calls > b.max || ctx.depth > 14) return null;
    const key = ctx.v + '|' + nodeKey(f);
    if (b.memo.has(key)) return b.memo.get(key);
    b.memo.set(key, null); // in progress: a cycle ends here
    let res = null;
    // a method integrates the parts it makes with ctx.integrate(g, overrides) — the engine hands itself down, so the
    // methods never import it
    const inner = { ...ctx, depth: ctx.depth + 1 };
    inner.integrate = (g, overrides) => I(g, overrides ? { ...inner, ...overrides } : inner);
    for (const m of METHODS) {
        let r;
        try {
            r = m(f, inner);
        } catch (e) {
            if (!(e instanceof MathError)) throw e;
            r = null;
        }
        if (!r) continue;
        let F;
        try {
            F = simp(r.F);
        } catch {
            continue;
        }
        const ok = checkAnti(F, f, ctx.v);
        if (ok === false) continue;
        if (ok === null && ctx.depth === 0 && !r.trust) continue;
        res = { ...r, F };
        break;
    }
    b.memo.set(key, res);
    return res;
}

// the cascade, in order
const METHODS = [
    mConst,
    mTable,
    mLinearity,
    mLinearSub,
    mDerivPattern,
    mRational,
    mBiquadratic,
    mCyclic,
    mTrig,
    mExpand,
    mUSub,
    mQuadRoot,
    mRadicalPoly,
    mRationalizing,
    mPolyTimes,
    mParts,
    mTrigLower,
    mTrigSub,
    mWeierstrass,
];
