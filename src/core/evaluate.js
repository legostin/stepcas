// evaluate — numeric value of an AST (real doubles or Complex), and compile() for fast plotting.
//
// Real mode: every undefined real result is NaN (√−1, ln 0, 1/0, tan at π/2 is just a huge number),
// inf evaluates to Infinity, the constant i to NaN. Odd roots of negatives are real: (−8)^(1/3) = −2
// when the exponent is a literal rational (1/3, root(x, 3), ∛x). Angles are always radians.
// Complex mode (opts.complex): principal branches (so (−8)^(1/3) is 1 + 1.732i there).

import { Q, MathError } from './rational.js';
import { isConst, numValue, nodeChildren } from './ast.js';
import { Complex } from './complex.js';
import { msg } from '../i18n/index.js';

const unknownVar = (name) => new MathError(msg('core.evaluate.no_value_for_variable', { name }), null, null, 'unbound');

function envNumber(v, name) {
    if (typeof v === 'number') return v;
    if (typeof v === 'bigint') return Number(v);
    if (v instanceof Q) return v.toNumber();
    if (v instanceof Complex) return v.im === 0 ? v.re : NaN;
    if (typeof v === 'string' && v.trim() !== '' && Number.isFinite(Number(v))) return Number(v);
    throw unknownVar(name);
}

// Lanczos approximation of Γ(x)
const LG = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059,
    12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
function gamma(x) {
    if (x < 0.5) return Math.PI / (Math.sin(Math.PI * x) * gamma(1 - x));
    x -= 1;
    let a = LG[0];
    const t = x + 7.5;
    for (let i = 1; i < 9; i++) a += LG[i] / (x + i);
    return Math.sqrt(2 * Math.PI) * Math.pow(t, x + 0.5) * Math.exp(-t) * a;
}

function factorial(x) {
    if (Number.isNaN(x)) return NaN;
    if (Number.isInteger(x)) {
        if (x < 0) return NaN;
        if (x > 170) return Infinity;
        let r = 1;
        for (let k = 2; k <= x; k++) r *= k;
        return r;
    }
    if (x < 0 && Number.isInteger(x)) return NaN;
    return gamma(x + 1);
}

/** Real power with an exact rational exponent: odd roots of negatives are real. */
function powQ(b, q) {
    if (q.isInt()) {
        const e = q.toNumber();
        if (b === 0 && e < 0) return NaN;
        return Math.pow(b, e);
    }
    const p = Number(q.n);
    const d = Number(q.d);
    if (b === 0) return q.isNeg() ? NaN : 0;
    if (b < 0) {
        if (d % 2 === 0) return NaN;
        const r = Math.pow(-b, Math.abs(p) / d);
        const v = p % 2 === 0 ? r : -r;
        return p < 0 ? 1 / v : v;
    }
    return Math.pow(b, p / d);
}

function realPow(b, e) {
    if (b === 0 && e < 0) return NaN;
    if (b < 0 && !Number.isInteger(e)) return NaN;
    return Math.pow(b, e);
}

function rootN(x, n) {
    if (!Number.isFinite(n) || n === 0) return NaN;
    if (Number.isInteger(n)) {
        if (x < 0) return n % 2 === 0 ? NaN : -Math.pow(-x, 1 / n);
        return Math.pow(x, 1 / n);
    }
    return x < 0 ? NaN : Math.pow(x, 1 / n);
}

const REAL_FN = {
    sin: Math.sin,
    cos: Math.cos,
    tan: Math.tan,
    cot: (x) => {
        const s = Math.sin(x);
        return s === 0 ? NaN : Math.cos(x) / s;
    },
    sec: (x) => {
        const c = Math.cos(x);
        return c === 0 ? NaN : 1 / c;
    },
    csc: (x) => {
        const s = Math.sin(x);
        return s === 0 ? NaN : 1 / s;
    },
    asin: Math.asin,
    acos: Math.acos,
    atan: Math.atan,
    acot: (x) => (x === 0 ? Math.PI / 2 : Math.atan(1 / x) + (x < 0 ? Math.PI : 0)),
    sinh: Math.sinh,
    cosh: Math.cosh,
    tanh: Math.tanh,
    coth: (x) => (x === 0 ? NaN : 1 / Math.tanh(x)),
    asinh: Math.asinh,
    acosh: Math.acosh,
    atanh: (x) => (Math.abs(x) >= 1 ? NaN : Math.atanh(x)),
    ln: (x) => (x > 0 ? Math.log(x) : NaN),
    lg: (x) => (x > 0 ? Math.log10(x) : NaN),
    exp: Math.exp,
    sqrt: (x) => (x >= 0 ? Math.sqrt(x) : NaN),
    abs: Math.abs,
    sign: Math.sign,
    floor: Math.floor,
    ceil: Math.ceil,
    fact: factorial,
};

function logBase(b, x) {
    if (!(b > 0) || b === 1 || !(x > 0)) return NaN;
    if (b === 10) return Math.log10(x);
    if (b === 2) return Math.log2(x);
    return Math.log(x) / Math.log(b);
}

function evalReal(n, env) {
    switch (n.type) {
        case 'num':
            return n.value.toNumber();
        case 'sym': {
            if (isConst(n)) {
                switch (n.name) {
                    case 'pi':
                        return Math.PI;
                    case 'e':
                        return Math.E;
                    case 'inf':
                        return Infinity;
                    default:
                        return NaN; // i in real mode
                }
            }
            if (!(n.name in env)) throw unknownVar(n.name);
            return envNumber(env[n.name], n.name);
        }
        case 'add': {
            let s = 0;
            for (const a of n.args) s += evalReal(a, env);
            return s;
        }
        case 'mul': {
            let p = 1;
            for (const a of n.args) p *= evalReal(a, env);
            return p;
        }
        case 'div': {
            const b = evalReal(n.den, env);
            return b === 0 ? NaN : evalReal(n.num, env) / b;
        }
        case 'neg':
            return -evalReal(n.arg, env);
        case 'pow': {
            const q = numValue(n.exp);
            if (isConst(n.base) && n.base.name === 'e') return Math.exp(q ? q.toNumber() : evalReal(n.exp, env));
            const b = evalReal(n.base, env);
            if (q) return powQ(b, q);
            return realPow(b, evalReal(n.exp, env));
        }
        case 'fn': {
            if (n.name === 'log') return logBase(evalReal(n.args[0], env), evalReal(n.args[1], env));
            if (n.name === 'root') {
                const k = numValue(n.args[1]);
                const x = evalReal(n.args[0], env);
                return k && k.isInt() ? rootN(x, k.toNumber()) : rootN(x, evalReal(n.args[1], env));
            }
            const f = REAL_FN[n.name];
            if (!f) throw new MathError(msg('core.evaluate.cannot_evaluate', { name: n.name }), null, null, 'unsupported');
            return f(evalReal(n.args[0], env));
        }
        case 'rel':
            return relHolds(n.op, evalReal(n.lhs, env), evalReal(n.rhs, env));
        case 'chain':
            return n.ops.every((op, k) => relHolds(op, evalReal(n.items[k], env), evalReal(n.items[k + 1], env)));
        case 'list':
            return n.items.map((x) => evalReal(x, env));
        default:
            throw new TypeError(`evaluate: unknown node ${n?.type}`);
    }
}

function relHolds(op, a, b) {
    const tol = 1e-9 * Math.max(1, Math.abs(a), Math.abs(b));
    switch (op) {
        case '=':
            return Math.abs(a - b) <= tol;
        case '!=':
            return Math.abs(a - b) > tol;
        case '<':
            return a < b - tol;
        case '<=':
            return a <= b + tol;
        case '>':
            return a > b + tol;
        case '>=':
            return a >= b - tol;
        default:
            return false;
    }
}

const C_NAN = new Complex(NaN, NaN);

function envComplex(v, name) {
    if (v instanceof Complex) return v;
    if (typeof v === 'number' || typeof v === 'bigint' || v instanceof Q) return Complex.of(v);
    if (v && typeof v === 'object' && 're' in v) return Complex.of(v);
    if (typeof v === 'string' && Number.isFinite(Number(v))) return new Complex(Number(v), 0);
    throw unknownVar(name);
}

function evalComplex(n, env) {
    switch (n.type) {
        case 'num':
            return new Complex(n.value.toNumber(), 0);
        case 'sym': {
            if (isConst(n)) {
                switch (n.name) {
                    case 'pi':
                        return new Complex(Math.PI, 0);
                    case 'e':
                        return new Complex(Math.E, 0);
                    case 'i':
                        return Complex.I;
                    default:
                        return new Complex(Infinity, 0);
                }
            }
            if (!(n.name in env)) throw unknownVar(n.name);
            return envComplex(env[n.name], n.name);
        }
        case 'add': {
            let s = Complex.ZERO;
            for (const a of n.args) s = s.add(evalComplex(a, env));
            return s;
        }
        case 'mul': {
            let p = Complex.ONE;
            for (const a of n.args) p = p.mul(evalComplex(a, env));
            return p;
        }
        case 'div':
            return evalComplex(n.num, env).div(evalComplex(n.den, env));
        case 'neg':
            return evalComplex(n.arg, env).neg();
        case 'pow': {
            if (isConst(n.base) && n.base.name === 'e') return evalComplex(n.exp, env).exp();
            return evalComplex(n.base, env).pow(evalComplex(n.exp, env));
        }
        case 'fn': {
            const a = n.args.map((x) => evalComplex(x, env));
            const z = a[0];
            switch (n.name) {
                case 'ln':
                    return z.isZero() ? C_NAN : z.log();
                case 'lg':
                    return z.isZero() ? C_NAN : z.log().div(Math.LN10);
                case 'log':
                    return a[1].isZero() ? C_NAN : a[1].log().div(a[0].log());
                case 'exp':
                    return z.exp();
                case 'sqrt':
                    return z.sqrt();
                case 'root':
                    return a[0].pow(Complex.ONE.div(a[1]));
                case 'abs':
                    return new Complex(z.abs(), 0);
                case 'sign':
                    return z.isZero() ? Complex.ZERO : z.div(z.abs());
                case 'floor':
                case 'ceil':
                case 'fact':
                    return z.isReal() ? new Complex(REAL_FN[n.name](z.re), 0) : C_NAN;
                default: {
                    const m = z[n.name];
                    if (typeof m !== 'function') throw new MathError(msg('core.evaluate.cannot_evaluate', { name: n.name }), null, null, 'unsupported');
                    return m.call(z);
                }
            }
        }
        case 'rel': {
            const a = evalComplex(n.lhs, env);
            const b = evalComplex(n.rhs, env);
            if (n.op === '=') return a.equals(b, 1e-9);
            if (n.op === '!=') return !a.equals(b, 1e-9);
            if (!a.isReal(1e-9) || !b.isReal(1e-9)) return false;
            return relHolds(n.op, a.re, b.re);
        }
        case 'chain':
            return n.ops.every((op, k) => evalComplex({ type: 'rel', op, lhs: n.items[k], rhs: n.items[k + 1] }, env));
        case 'list':
            return n.items.map((x) => evalComplex(x, env));
        default:
            throw new TypeError(`evaluate: unknown node ${n?.type}`);
    }
}

/**
 * Numeric value. env maps variable names to numbers (or Q, bigint, Complex in complex mode).
 * Real mode returns a number (NaN when undefined); {complex: true} returns a Complex.
 * Relations return booleans (with a 1e-9 tolerance for =), lists return arrays.
 * Throws MathError (code 'unbound') for a variable missing from env.
 */
export function evaluate(node, env = {}, opts = {}) {
    return opts.complex ? evalComplex(node, env) : evalReal(node, env);
}

/** Exact rational value of a constant expression that simplifies to a number, else null (no simplification here). */
export function exactNumber(node) {
    return numValue(node);
}

// ---------------------------------------------------------------- compile

function hasVars(n, vars) {
    if (n.type === 'sym') return vars.includes(n.name) && !isConst(n);
    return nodeChildren(n).some((c) => hasVars(c, vars));
}

/**
 * Compile to a fast closure for plotting: compile(node, ['x']) → (x) => number.
 * No eval/new Function; constant subtrees are folded once. Real semantics as evaluate().
 * Throws MathError at compile time for variables that are not listed.
 */
export function compile(node, vars = ['x']) {
    if (typeof vars === 'string') vars = [vars];
    const idx = new Map(vars.map((v, k) => [v, k]));

    const comp = (n) => {
        if (!hasVars(n, vars)) {
            const v = evalReal(n, {});
            return () => v;
        }
        switch (n.type) {
            case 'sym': {
                const k = idx.get(n.name);
                return (a) => a[k];
            }
            case 'add': {
                const fs = n.args.map(comp);
                if (fs.length === 2) {
                    const [f, g] = fs;
                    return (a) => f(a) + g(a);
                }
                return (a) => {
                    let s = 0;
                    for (let k = 0; k < fs.length; k++) s += fs[k](a);
                    return s;
                };
            }
            case 'mul': {
                const fs = n.args.map(comp);
                if (fs.length === 2) {
                    const [f, g] = fs;
                    return (a) => f(a) * g(a);
                }
                return (a) => {
                    let p = 1;
                    for (let k = 0; k < fs.length; k++) p *= fs[k](a);
                    return p;
                };
            }
            case 'div': {
                const f = comp(n.num);
                const g = comp(n.den);
                return (a) => {
                    const d = g(a);
                    return d === 0 ? NaN : f(a) / d;
                };
            }
            case 'neg': {
                const f = comp(n.arg);
                return (a) => -f(a);
            }
            case 'pow': {
                const q = numValue(n.exp);
                if (isConst(n.base) && n.base.name === 'e') {
                    const g = comp(n.exp);
                    return (a) => Math.exp(g(a));
                }
                const f = comp(n.base);
                if (q) {
                    if (q.eq(2)) return (a) => {
                        const b = f(a);
                        return b * b;
                    };
                    if (q.eq(Q.HALF)) return (a) => {
                        const b = f(a);
                        return b >= 0 ? Math.sqrt(b) : NaN;
                    };
                    return (a) => powQ(f(a), q);
                }
                const g = comp(n.exp);
                return (a) => realPow(f(a), g(a));
            }
            case 'fn': {
                if (n.name === 'log') {
                    const b = comp(n.args[0]);
                    const x = comp(n.args[1]);
                    return (a) => logBase(b(a), x(a));
                }
                if (n.name === 'root') {
                    const x = comp(n.args[0]);
                    const k = comp(n.args[1]);
                    return (a) => rootN(x(a), k(a));
                }
                const f = REAL_FN[n.name];
                if (!f) throw new MathError(msg('core.evaluate.cannot_evaluate', { name: n.name }), null, null, 'unsupported');
                const g = comp(n.args[0]);
                return (a) => f(g(a));
            }
            case 'rel':
            case 'chain':
            case 'list':
                throw new MathError(msg('core.evaluate.formula_is_needed_not_equation_or'), null, null, 'not-expr');
            default:
                throw new TypeError(`compile: unknown node ${n?.type}`);
        }
    };

    // unlisted free variables → MathError now, not NaN later
    const check = (n) => {
        if (n.type === 'sym' && !isConst(n) && !idx.has(n.name)) throw unknownVar(n.name);
        nodeChildren(n).forEach(check);
    };
    check(node);
    const f = comp(node);
    if (vars.length === 1) return (x) => f([x]);
    return (...values) => f(values);
}
