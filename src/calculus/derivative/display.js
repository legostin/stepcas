// derivative/display — input, the display form and TeX of calculus answers (prettyForm, calcTex), numeric sampling.

import { num, sym, toNode, pow, add, nodeSome, freeVars, mul, div, withChildren, nodeChildren, isConst, neg } from '../../core/ast.js';
import { Q, MathError, bigLcm } from '../../core/rational.js';
import { parse } from '../../core/parse.js';
import { canonContext } from '../../core/simplify.js';
import { toTex, toText } from '../../core/print.js';
import { rng } from '../../core/random.js';
import { evaluate } from '../../core/evaluate.js';

export const N0 = num(0);
export const N1 = num(1);
export const NM1 = num(-1);
export const N2 = num(2);
export const HALF = num(Q.HALF);
export const E_ = sym('e');

export const isNum = (n) => n.type === 'num';
export const isZero = (n) => isNum(n) && n.value.isZero();
export const isOne = (n) => isNum(n) && n.value.isOne();
export const T_ = (ru, en) => ({ ru, en });

// ---------------------------------------------------------------- input

export function asNode(x) {
    if (x && typeof x === 'object' && typeof x.type === 'string') return x;
    if (typeof x === 'string') return parse(x);
    return toNode(x);
}

export function checkExpr(node) {
    if (node.type === 'rel' || node.type === 'chain' || node.type === 'list') {
        throw new MathError({ ru: 'Нужна формула функции, а не уравнение или список', en: 'A formula is needed, not an equation or a list' }, null, null, 'not-expr');
    }
}

// ---------------------------------------------------------------- display form and TeX

export function negLeading(n) {
    if (isNum(n)) return n.value.isNeg();
    if (n.type === 'neg') return true;
    if (n.type === 'mul') return n.args.length > 0 && negLeading(n.args[0]);
    return false;
}

const isRadicalPow = (f) => f.type === 'pow' && isNum(f.exp) && !f.exp.value.isInt() && f.exp.value.n !== 1n && f.exp.value.n !== -1n;

/** Readable pieces of B^(p/q), p/q > 0: [x, √x] for x^(3/2), [∛(x²)] for x^(2/3), [√((x²+1)³)] for a sum. */
function splitRadical(base, e) {
    const P = e.n;
    const q = e.d;
    if (base.type === 'sym' || isNum(base)) {
        const k = P / q;
        const r = P % q;
        const out = [];
        if (k > 0n) out.push(k === 1n ? base : pow(base, num(k)));
        out.push(pow(r === 1n ? base : pow(base, num(r)), num(new Q(1n, q))));
        return out;
    }
    return [pow(pow(base, num(P)), num(new Q(1n, q)))];
}

function invertPiece(p) {
    if (p.type === 'pow' && isNum(p.exp)) return pow(p.base, num(p.exp.value.neg()));
    return pow(p, NM1);
}

/**
 * Display tweaks that keep the value: 1 − x² (not −x² + 1), x√x, ∛(x²), √((x²+1)³), (x + 1)ln(x + 1).
 * opts.fnFirst: in sums, terms with functions go first (x ln²x − 2x ln x + 2x) — used for antiderivatives.
 */
export function prettyForm(node, opts = {}) {
    const P = (n) => {
        switch (n.type) {
            case 'add': {
                const args = n.args.map(P);
                if (args.length === 2 && negLeading(args[0]) && !negLeading(args[1])) return add(args[1], args[0]);
                // 1 + 2/x rather than 2/x + 1: a positive constant goes first when the rest are reciprocals
                const last = args[args.length - 1];
                if (args.length >= 2 && isNum(last) && last.value.isPos() && args.slice(0, -1).every((t) => nodeSome(t, (m) => m.type === 'pow' && isNum(m.exp) && m.exp.value.isNeg() && freeVars(m.base).length > 0) && !negLeading(t) === !negLeading(args[0]))) {
                    return add([last, ...args.slice(0, -1)]);
                }
                const hasFnT = (t) => nodeSome(t, (m) => m.type === 'fn');
                if (args.length > 2 && negLeading(args[0]) && args.some(hasFnT)) {
                    // not a polynomial: start with a positive term (x cos²x − x sin²x + …)
                    const k = args.findIndex((t) => !negLeading(t));
                    if (k > 0) return add([args[k], ...args.slice(0, k), ...args.slice(k + 1)]);
                }
                if (opts.fnFirst && args.length > 1 && args.some(hasFnT) && !args.every(hasFnT)) {
                    // terms with functions first when they are not of lower degree: x ln²x − 2x ln x + 2x rather than
                    // 2x + x ln²x − 2x ln x (but x/2 + sin 2x/4 stays as it is)
                    const dmax = Math.max(...args.filter((t) => !hasFnT(t)).map(termDegree));
                    const front = args.filter((t) => hasFnT(t) && termDegree(t) >= dmax);
                    if (front.length) {
                        const re = [...front, ...args.filter((t) => !front.includes(t))];
                        if (!negLeading(re[0]) || negLeading(args[0])) return add(re);
                    }
                }
                return add(args);
            }
            case 'mul': {
                if (!n.args.some(isRadicalPow)) return mul(sumsBeforeFns(n.args.map(P)));
                const out = [];
                for (const f of n.args) {
                    if (!isRadicalPow(f)) {
                        out.push(P(f));
                        continue;
                    }
                    const e = f.exp.value;
                    const parts = splitRadical(P(f.base), e.abs());
                    out.push(...(e.isNeg() ? parts.map(invertPiece) : parts));
                }
                return mul(sumsBeforeFns(out));
            }
            case 'pow': {
                if (isRadicalPow(n)) {
                    const e = n.exp.value;
                    const parts = splitRadical(P(n.base), e.abs());
                    const body = parts.length === 1 ? parts[0] : mul(parts);
                    return e.isNeg() ? div(N1, body) : body;
                }
                return pow(P(n.base), P(n.exp));
            }
            case 'num':
            case 'sym':
                return n;
            case 'fn':
                return withChildren(n, n.args.map((a) => tidyArg(P(a))));
            default: {
                const kids = nodeChildren(n);
                return kids.length ? withChildren(n, kids.map(P)) : n;
            }
        }
    };
    return groupRadicalCoef(P(node));
}

/** Degree of a term in its non-function factors (x·ln x → 1, √(x² + 1) → 1, sin 2x → 0). */
function termDegree(t) {
    const fs = t.type === 'mul' ? t.args : t.type === 'neg' ? [t.arg] : [t];
    let d = 0;
    for (const f of fs) {
        if (f.type === 'sym' && !isConst(f)) d += 1;
        else if (f.type === 'pow' && isNum(f.exp) && freeVars(f.base).length && f.base.type !== 'fn') {
            const bd = f.base.type === 'sym' ? 1 : f.base.type === 'add' ? Math.max(...f.base.args.map(termDegree)) : termDegree(f.base);
            d += bd * f.exp.value.toNumber();
        } else if (f.type === 'div') d += termDegree(f.num) - termDegree(f.den);
    }
    return d;
}

/** In a product, bracketed sums go before function applications: (x + 1)·ln(x + 1), not ln(x + 1)(x + 1). */
function sumsBeforeFns(fs) {
    const isSum = (f) => f.type === 'add' || (f.type === 'pow' && f.base.type === 'add' && isNum(f.exp) && f.exp.value.isInt() && f.exp.value.isPos());
    const k = fs.findIndex((f) => f.type === 'fn' || (f.type === 'pow' && f.base.type === 'fn'));
    if (k < 0 || !fs.slice(k).some(isSum)) return fs;
    return [...fs.slice(0, k), ...fs.slice(k).filter(isSum), ...fs.slice(k).filter((f) => !isSum(f))];
}

const isNumRadical = (f) => f.type === 'pow' && isNum(f.base) && f.base.value.isInt() && f.base.value.gt(1) && isNum(f.exp) && f.exp.value.n === 1n && f.exp.value.d > 1n;

/** ⅔·√3·arctg(…) → (2√3/3)·arctg(…): a rational coefficient with a numeric radical reads as one fraction. */
function groupRadicalCoef(n) {
    if (n.type === 'add') return add(n.args.map(groupRadicalCoef));
    if (n.type === 'neg') return neg(groupRadicalCoef(n.arg));
    if (n.type !== 'mul' || n.args.length < 3 || !isNum(n.args[0]) || n.args[0].value.isInt()) return n;
    const rads = n.args.filter(isNumRadical);
    const rest = n.args.slice(1).filter((f) => !isNumRadical(f));
    if (!rads.length || !rest.some((f) => f.type === 'fn' || f.type === 'add' || (f.type === 'pow' && f.base.type !== 'sym'))) return n;
    const c = n.args[0].value;
    const an = c.n < 0n ? -c.n : c.n;
    const top = an === 1n ? (rads.length === 1 ? rads[0] : mul(rads)) : mul([num(an), ...rads]);
    const frac = div(top, num(c.d));
    const body = mul([frac, ...rest]);
    return c.isNeg() ? neg(body) : body;
}

/** Function arguments: x/2 + 1/2 → (x + 1)/2, (1/3)·√3·(2x − 1) → (2x − 1)/√3. */
function tidyArg(a) {
    const coefOf = (t) => (isNum(t) ? t.value : t.type === 'mul' && isNum(t.args[0]) ? t.args[0].value : Q.ONE);
    if (a.type === 'add' && a.args.every((t) => t.type !== 'add' && !nodeSome(t, (m) => isConst(m) || m.type === 'fn'))) {
        let l = 1n;
        for (const t of a.args) l = bigLcm(l, coefOf(t).d);
        if (l > 1n && l < 1000n) {
            const C = canonContext();
            const scaled = a.args.map((t) => C.mul([num(l), t]));
            return div(prettyForm(add(scaled)), num(l));
        }
        return a;
    }
    if (a.type === 'mul' && isNum(a.args[0]) && a.args.length >= 3 && isNumRadical(a.args[1]) && a.args[1].exp.value.d === 2n) {
        const c = a.args[0].value;
        const k = c.mul(a.args[1].base.value);
        if (k.isInt()) {
            const rest = a.args.slice(2);
            const top = k.isOne() ? (rest.length === 1 ? rest[0] : mul(rest)) : mul([num(k), ...rest]);
            return div(top, a.args[1]);
        }
    }
    return a;
}

// \ln\left(\left|u\right|\right) → \ln\left|u\right| (also \lg, \log_{a})
function fixAbsInLog(s) {
    const OPEN = '\\left(\\left|';
    const CLOSE = '\\right|\\right)';
    let from = 0;
    for (let guard = 0; guard < 500; guard++) {
        const at = s.indexOf(OPEN, from);
        if (at < 0) break;
        const before = s.slice(0, at);
        if (!/(\\ln|\\lg|\\log_\{[^{}]*\})$/.test(before)) {
            from = at + OPEN.length;
            continue;
        }
        let depth = 2;
        let k = at + OPEN.length;
        let closeAbs = -1;
        while (k < s.length) {
            if (s.startsWith('\\left', k)) {
                depth++;
                k += 5;
                continue;
            }
            if (s.startsWith('\\right', k)) {
                depth--;
                if (depth === 1) {
                    closeAbs = k;
                    break;
                }
                k += 6;
                continue;
            }
            k++;
        }
        if (closeAbs < 0 || !s.startsWith(CLOSE, closeAbs)) {
            from = at + OPEN.length;
            continue;
        }
        const inner = s.slice(at + OPEN.length, closeAbs);
        s = before + '\\left|' + inner + '\\right|' + s.slice(closeAbs + CLOSE.length);
        from = at + 1;
    }
    return s;
}

/**
 * TeX of a node in the calculus style (prettyForm, and \ln|u| instead of \ln(|u|)). Fractional powers print
 * as roots (toTex {roots: true}) — the same shapes prettyForm builds for the plain-text step lines.
 */
export function calcTex(node, lang = 'ru') {
    return fixAbsInLog(toTex(prettyForm(node), { lang, roots: true }));
}

/** calcTex in both languages: a string when they agree, else {ru, en}. */
export function calcTexBoth(node) {
    const ru = calcTex(node, 'ru');
    const en = calcTex(node, 'en');
    return ru === en ? ru : { ru, en };
}

export function bt(f) {
    const ru = f('ru');
    const en = f('en');
    return ru === en ? ru : { ru, en };
}

const tall = (s) => /\\frac|\\sqrt|\\left|\\dfrac|\^\{/.test(s);
export const paren = (s) => (tall(s) ? `\\left(${s}\\right)` : `(${s})`);

const SUP = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹', '-': '⁻' };
const supDigits = (d) => [...d].map((c) => SUP[c]).join('');

/** Plain-text formula for step texts: x^2 → x², * → ·, sqrt( → √(. */
export function plain(node, lang) {
    let s = toText(prettyForm(node), { lang });
    s = s.replace(/\^\((-?\d+)\)/g, (m, d) => supDigits(d));
    s = s.replace(/\^(\d+)(?![\d/.,(])/g, (m, d) => supDigits(d));
    s = s.replace(/\*/g, '·').replace(/sqrt\(/g, '√(');
    return s;
}

// ---------------------------------------------------------------- numeric sampling

const RANGES = [[0.2, 1.8], [-1.8, -0.2], [2, 6], [-6, -2], [0.05, 0.95], [-0.95, -0.05], [6, 20], [-20, -6]];

export function randomEnv(vars, r) {
    const env = {};
    for (const w of vars) env[w] = r.real(0.6, 1.9);
    return env;
}

/** Numeric comparison of two expressions of v (other letters random positive): {ok: true|false|null, usable}. */
export function agree(a, b, v, opts = {}) {
    const r = rng(opts.seed ?? 7919);
    const vars = [...new Set([...freeVars(a), ...freeVars(b)])].filter((w) => w !== v);
    const ranges = opts.ranges ?? RANGES;
    let usable = 0;
    const N = opts.points ?? 24;
    const tol = opts.tol ?? 1e-7;
    for (let k = 0; k < N; k++) {
        const env = randomEnv(vars, r);
        const [lo, hi] = ranges[k % ranges.length];
        env[v] = r.real(lo, hi);
        let x;
        let y;
        try {
            x = evaluate(a, env);
            y = evaluate(b, env);
        } catch {
            return { ok: null, usable };
        }
        if (typeof x !== 'number' || typeof y !== 'number') return { ok: null, usable };
        if (!Number.isFinite(x) || !Number.isFinite(y) || Math.abs(x) > 1e12 || Math.abs(y) > 1e12) continue;
        usable++;
        if (Math.abs(x - y) > tol * Math.max(1, Math.abs(x), Math.abs(y))) return { ok: false, usable };
    }
    return { ok: usable >= (opts.min ?? 4) ? true : null, usable };
}
