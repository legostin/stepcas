// diff — symbolic derivatives with a step tree that mirrors the expression («что делаем и почему»),
// higher and partial derivatives, the gradient and the tangent line.
//
// derivative(f, 'x', {steps}) walks the tree as the person typed it (sum → sum rule, product → product
// rule, f(g(x)) → chain rule with the inner function named, …); every node shows (…)' = rule = assembled =
// clean. The clean form is picked among equivalent candidates (canonical, one fraction, common factor
// taken out, sin/cos → tg/ctg) by the length of its TeX, and every result is checked numerically
// (against an independent fast derivative and against central differences of f).
// Also exported for the other calculus modules: quickDerivative (fast canonical derivative), niceForm
// (tidy equivalent form), prettyForm (display tweaks: 1 − x² rather than −x² + 1, ∛(x²) rather than x^(2/3)),
// calcTex / calcTexBoth (TeX with |…| after ln instead of ln(|…|)).

import { Q, MathError, bigGcd, bigLcm } from '../core/rational.js';
import { num, sym, add, mul, div, neg, pow, fn, isConst, containsVar, freeVars, nodeKey, substitute, mapNode, toNode, nodeChildren, withChildren, nodeSome } from '../core/ast.js';
import { parse } from '../core/parse.js';
import { simplify, canonContext, splitCoeff } from '../core/simplify.js';
import { combineFractions, expand } from '../core/expand.js';
import { toTex, toText } from '../core/print.js';
import { evaluate } from '../core/evaluate.js';
import { step } from '../core/steps.js';
import { Poly } from '../core/poly.js';
import { rng } from '../core/random.js';

const N0 = num(0);
const N1 = num(1);
const NM1 = num(-1);
const N2 = num(2);
const HALF = num(Q.HALF);
const E_ = sym('e');

const isNum = (n) => n.type === 'num';
const isZero = (n) => isNum(n) && n.value.isZero();
const isOne = (n) => isNum(n) && n.value.isOne();
const T_ = (ru, en) => ({ ru, en });

// ---------------------------------------------------------------- input

function asNode(x) {
    if (x && typeof x === 'object' && typeof x.type === 'string') return x;
    if (typeof x === 'string') return parse(x);
    return toNode(x);
}

function checkExpr(node) {
    if (node.type === 'rel' || node.type === 'chain' || node.type === 'list') {
        throw new MathError({ ru: 'Нужна формула функции, а не уравнение или список', en: 'A formula is needed, not an equation or a list' }, null, null, 'not-expr');
    }
}

// ---------------------------------------------------------------- display form and TeX

function negLeading(n) {
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

function bt(f) {
    const ru = f('ru');
    const en = f('en');
    return ru === en ? ru : { ru, en };
}

const tall = (s) => /\\frac|\\sqrt|\\left|\\dfrac|\^\{/.test(s);
const paren = (s) => (tall(s) ? `\\left(${s}\\right)` : `(${s})`);

const SUP = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹', '-': '⁻' };
const supDigits = (d) => [...d].map((c) => SUP[c]).join('');

/** Plain-text formula for step texts: x^2 → x², * → ·, sqrt( → √(. */
function plain(node, lang) {
    let s = toText(prettyForm(node), { lang });
    s = s.replace(/\^\((-?\d+)\)/g, (m, d) => supDigits(d));
    s = s.replace(/\^(\d+)(?![\d/.,(])/g, (m, d) => supDigits(d));
    s = s.replace(/\*/g, '·').replace(/sqrt\(/g, '√(');
    return s;
}

// ---------------------------------------------------------------- numeric sampling

const RANGES = [[0.2, 1.8], [-1.8, -0.2], [2, 6], [-6, -2], [0.05, 0.95], [-0.95, -0.05], [6, 20], [-20, -6]];

function randomEnv(vars, r) {
    const env = {};
    for (const w of vars) env[w] = r.real(0.6, 1.9);
    return env;
}

/** Numeric comparison of two expressions of v (other letters random positive): {ok: true|false|null, usable}. */
function agree(a, b, v, opts = {}) {
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

// ---------------------------------------------------------------- fast canonical derivative

const lnOf = (b, C) => C.fn('ln', [b]);
const MHALF = num(new Q(-1n, 2n));

function outerCanon(name, u, C) {
    const u2 = C.pow(u, N2);
    switch (name) {
        case 'sin':
            return C.fn('cos', [u]);
        case 'cos':
            return C.mul([NM1, C.fn('sin', [u])]);
        case 'tan':
            return C.pow(C.fn('cos', [u]), num(-2));
        case 'cot':
            return C.mul([NM1, C.pow(C.fn('sin', [u]), num(-2))]);
        case 'sec':
            return C.mul([C.fn('sec', [u]), C.fn('tan', [u])]);
        case 'csc':
            return C.mul([NM1, C.fn('csc', [u]), C.fn('cot', [u])]);
        case 'asin':
            return C.pow(C.add([N1, C.mul([NM1, u2])]), MHALF);
        case 'acos':
            return C.mul([NM1, C.pow(C.add([N1, C.mul([NM1, u2])]), MHALF)]);
        case 'atan':
            return C.pow(C.add([u2, N1]), NM1);
        case 'acot':
            return C.mul([NM1, C.pow(C.add([u2, N1]), NM1)]);
        case 'sinh':
            return C.fn('cosh', [u]);
        case 'cosh':
            return C.fn('sinh', [u]);
        case 'tanh':
            return C.pow(C.fn('cosh', [u]), num(-2));
        case 'coth':
            return C.mul([NM1, C.pow(C.fn('sinh', [u]), num(-2))]);
        case 'asinh':
            return C.pow(C.add([u2, N1]), MHALF);
        case 'acosh':
            return C.pow(C.add([u2, NM1]), MHALF);
        case 'atanh':
            return C.pow(C.add([N1, C.mul([NM1, u2])]), NM1);
        case 'ln':
            return C.pow(u, NM1);
        case 'lg':
            return C.pow(C.mul([u, lnOf(num(10), C)]), NM1);
        case 'exp':
            return C.pow(E_, u);
        case 'sqrt':
            return C.mul([HALF, C.pow(u, MHALF)]);
        case 'abs':
            return C.mul([u, C.pow(C.fn('abs', [u]), NM1)]);
        case 'sign':
        case 'floor':
        case 'ceil':
            return N0;
        default:
            throw new MathError({ ru: `Не умею дифференцировать функцию ${name}`, en: `Cannot differentiate ${name}` }, null, null, 'unsupported');
    }
}

const FACT_ERR = () => new MathError({ ru: 'Факториал — функция натурального аргумента, производной у неё нет', en: 'The factorial is defined on whole numbers and has no derivative' }, null, null, 'unsupported');

function dCanon(n, v, C) {
    if (!containsVar(n, v)) return N0;
    switch (n.type) {
        case 'sym':
            return N1;
        case 'add':
            return C.add(n.args.map((a) => dCanon(a, v, C)));
        case 'mul': {
            const terms = [];
            n.args.forEach((f, i) => {
                if (!containsVar(f, v)) return;
                const df = dCanon(f, v, C);
                if (isZero(df)) return;
                terms.push(C.mul([...n.args.slice(0, i), df, ...n.args.slice(i + 1)]));
            });
            return C.add(terms);
        }
        case 'pow': {
            const b = n.base;
            const e = n.exp;
            const bv = containsVar(b, v);
            const ev = containsVar(e, v);
            if (!ev) return C.mul([e, C.pow(b, C.add([e, NM1])), dCanon(b, v, C)]);
            if (!bv) return C.mul([n, lnOf(b, C), dCanon(e, v, C)]);
            return C.mul([n, dCanon(C.mul([e, lnOf(b, C)]), v, C)]);
        }
        case 'fn': {
            if (n.name === 'log') {
                const [b, x] = n.args;
                if (containsVar(b, v)) return dCanon(C.mul([lnOf(x, C), C.pow(lnOf(b, C), NM1)]), v, C);
                return C.mul([C.pow(C.mul([x, lnOf(b, C)]), NM1), dCanon(x, v, C)]);
            }
            if (n.name === 'root') {
                const r = C.fn('root', n.args);
                if (r.type === 'fn' && r.name === 'root') throw new MathError({ ru: 'Не умею дифференцировать такой корень', en: 'Cannot differentiate this root' }, null, null, 'unsupported');
                return dCanon(r, v, C);
            }
            if (n.name === 'fact') throw FACT_ERR();
            const u = n.args[0];
            const outer = outerCanon(n.name, u, C);
            if (isZero(outer)) return N0;
            return C.mul([outer, dCanon(u, v, C)]);
        }
        default: {
            const s = C.simplify(n);
            if (s === n) throw new MathError({ ru: 'Не умею дифференцировать это выражение', en: 'Cannot differentiate this expression' }, null, null, 'unsupported');
            return dCanon(s, v, C);
        }
    }
}

/** Derivative in canonical form (simplify.js), fast and without steps — for checks, higher orders, L'Hôpital. */
export function quickDerivative(node, v = 'x') {
    node = asNode(node);
    checkExpr(node);
    const C = canonContext({ budget: 2000000 });
    return dCanon(C.simplify(node), v, C);
}

// ---------------------------------------------------------------- the clean form

function hasNegPow(n) {
    if (n.type === 'pow' && isNum(n.exp) && n.exp.value.isNeg()) return true;
    return nodeChildren(n).some(hasNegPow);
}

function factorsOf(t) {
    const { coef, rest } = splitCoeff(t);
    const fs = rest === null ? [] : rest.type === 'mul' ? rest.args : [rest];
    const m = new Map();
    for (const f of fs) {
        let base = f;
        let e = Q.ONE;
        if (f.type === 'pow' && isNum(f.exp)) {
            base = f.base;
            e = f.exp.value;
        }
        const k = nodeKey(base);
        const cur = m.get(k);
        if (cur) cur.e = cur.e.add(e);
        else m.set(k, { base, e });
    }
    return { coef, m };
}

/** a·F + b·F·G → F·(a + b·G) when the common factor F holds something other than bare letters. */
function factorCommon(S, opts = {}) {
    if (S.type !== 'add' || S.args.length < 2) return null;
    const terms = S.args.map(factorsOf);
    const common = [];
    for (const [k, { base, e }] of terms[0].m) {
        let pick = e;
        let ok = true;
        for (const t of terms.slice(1)) {
            const g = t.m.get(k);
            if (!g || g.e.isNeg() !== e.isNeg()) {
                ok = false;
                break;
            }
            // positive powers: the smallest; negative powers (denominators): the smallest in absolute value
            if (e.isNeg() ? g.e.gt(pick) : g.e.lt(pick)) pick = g.e;
        }
        if (ok) common.push({ k, base, e: pick });
    }
    if (!common.length) return null;
    if (!common.some((c) => c.base.type !== 'sym' || c.e.isNeg())) return null;
    if (opts.fnFractions === false) {
        // antiderivatives: take out exponentials and radicals, keep sums of trig/log powers expanded
        const expOrRoot = (c) => (c.base.type === 'pow' && !freeVars(c.base.base).length) || !c.e.isInt();
        if (!common.some(expOrRoot) || common.some((c) => c.base.type === 'fn')) return null;
    }
    let g = 0n;
    let l = 1n;
    for (const t of terms) {
        g = bigGcd(g, t.coef.n);
        l = bigLcm(l, t.coef.d);
    }
    let content = g === 0n ? Q.ONE : new Q(g, l);
    if (terms.every((t) => t.coef.isNeg())) content = content.neg();
    const C = canonContext();
    const restTerms = terms.map((t) => {
        const fs = [num(t.coef.div(content))];
        for (const [k, { base, e }] of t.m) {
            const c = common.find((x) => x.k === k);
            const left = c ? e.sub(c.e) : e;
            if (!left.isZero()) fs.push(C.pow(base, num(left)));
        }
        return C.mul(fs);
    });
    const restSum = C.add(restTerms);
    const outer = [];
    if (!content.isOne()) outer.push(num(content));
    for (const c of common) outer.push(C.pow(c.base, num(c.e)));
    if (isNum(restSum)) return C.mul([...outer, restSum]);
    return mul([...outer, restSum]);
}

/** sin u / cos u → tg u, cos u / sin u → ctg u inside products; 1/tgᵏu → ctgᵏu. */
function trigCombine(node) {
    const C = canonContext();
    const FLIP = { tan: 'cot', cot: 'tan' };
    return mapNode(node, (m) => {
        if (m.type === 'pow' && m.base.type === 'fn' && FLIP[m.base.name] && isNum(m.exp) && m.exp.value.isNeg()) {
            return C.pow(C.fn(FLIP[m.base.name], m.base.args), num(m.exp.value.neg()));
        }
        if (m.type !== 'mul') return undefined;
        const sins = new Map();
        const coss = new Map();
        m.args.forEach((f, i) => {
            const b = f.type === 'pow' ? f.base : f;
            const e = f.type === 'pow' ? f.exp : N1;
            if (b.type !== 'fn' || !isNum(e) || !e.value.isInt()) return;
            if (b.name === 'sin') sins.set(nodeKey(b.args[0]), { i, e: e.value, arg: b.args[0] });
            if (b.name === 'cos') coss.set(nodeKey(b.args[0]), { i, e: e.value, arg: b.args[0] });
        });
        const drop = new Set();
        const extra = [];
        for (const [k, s] of sins) {
            const c = coss.get(k);
            if (!c || !s.e.add(c.e).isZero()) continue;
            drop.add(s.i);
            drop.add(c.i);
            if (s.e.isPos()) extra.push(C.pow(C.fn('tan', [s.arg]), num(s.e)));
            else extra.push(C.pow(C.fn('cot', [s.arg]), num(c.e)));
        }
        if (!drop.size) return undefined;
        return C.mul([...m.args.filter((_, i) => !drop.has(i)), ...extra]);
    });
}

/** Polynomial coefficient in its shorter form: expanded or factored (3x² + 3x → 3x(x + 1)). */
function polyShort(P, v, mode = 'short') {
    const expanded = P.toNode(v);
    if (P.degree < 1) return [expanded];
    const { constant, factors } = P.factor();
    const X = sym(v);
    // (x − a)ᵏ(x + a)ᵏ → (x² − a²)ᵏ
    const fl = factors.map((f) => ({ ...f }));
    for (const f of fl) {
        if (f.done || f.poly.degree !== 1 || !f.poly.c[1].isOne() || f.poly.c[0].isZero()) continue;
        const partner = fl.find((g) => !g.done && g !== f && g.mult === f.mult && g.poly.degree === 1 && g.poly.c[1].isOne() && g.poly.c[0].eq(f.poly.c[0].neg()));
        if (partner) {
            partner.done = true;
            f.poly = new Poly([f.poly.c[0].mul(partner.poly.c[0]), Q.ZERO, Q.ONE]);
        }
    }
    const fs = [];
    if (!constant.isOne()) fs.push(num(constant));
    const monos = [];
    for (const { poly, mult, done } of fl) {
        if (done) continue;
        const isX = poly.degree === 1 && poly.c[0].isZero() && poly.c[1].isOne();
        const node = isX ? X : poly.toNode(v);
        (isX ? monos : fs).push(mult === 1 ? node : pow(node, num(mult)));
    }
    fs.splice(constant.isOne() ? 0 : 1, 0, ...monos);
    if (fs.length <= 1 || factors.length === 0) return [expanded];
    if (mode === 'factored') return fs;
    const factored = mul(fs);
    return score(factored) < score(expanded) ? fs : [expanded];
}

/** Collect the terms of a sum by their non-polynomial part: 3x³cos u + 3x²cos u → 3x²(x + 1)cos u. */
function collectFns(X, v) {
    if (X.type !== 'add' || !v) return null;
    const groups = new Map();
    for (const t of X.args) {
        const { coef, rest } = splitCoeff(t);
        const fs = rest === null ? [] : rest.type === 'mul' ? rest.args : [rest];
        let deg = 0;
        const others = [];
        for (const f of fs) {
            if (f.type === 'sym' && f.name === v && !isConst(f)) deg += 1;
            else if (f.type === 'pow' && f.base.type === 'sym' && f.base.name === v && !isConst(f.base) && isNum(f.exp) && f.exp.value.isInt() && f.exp.value.isPos() && f.exp.value.le(50)) deg += Number(f.exp.value.n);
            else others.push(f);
        }
        const key = others.map(nodeKey).join('*');
        let g = groups.get(key);
        if (!g) {
            g = { others, poly: new Poly([]), count: 0 };
            groups.set(key, g);
        }
        g.poly = g.poly.add(Poly.monomial(coef, deg));
        g.count++;
    }
    if (![...groups.values()].some((g) => g.others.length && g.count > 1)) return null;
    const terms = [];
    for (const g of groups.values()) {
        if (g.poly.isZero()) continue;
        const pf = g.others.length ? polyShort(g.poly, v) : [g.poly.toNode(v)];
        if (!g.others.length) {
            terms.push(pf.length === 1 ? pf[0] : mul(pf));
            continue;
        }
        // a coefficient polynomial with a negative leading term goes in with a minus: −(x⁵ − 20x³)·cos x
        if (pf.length === 1 && pf[0].type === 'add' && g.poly.lead.isNeg()) {
            const pos = polyShort(g.poly.neg(), v);
            const posLead = (pos.length === 1 && isNum(pos[0]) ? (pos[0].value.isOne() ? [] : [pos[0]]) : pos).flatMap((x) => (x.type === 'mul' ? x.args : [x]));
            terms.push(neg(mul([...posLead, ...g.others])));
            continue;
        }
        let lead = pf.length === 1 && isNum(pf[0]) ? (pf[0].value.isOne() ? [] : [pf[0]]) : pf;
        lead = lead.flatMap((x) => (x.type === 'mul' ? x.args : [x]));
        terms.push(mul([...lead, ...g.others]));
    }
    if (!terms.length) return N0;
    return terms.length === 1 ? terms[0] : add(terms);
}

function score(n) {
    return calcTex(n, 'ru').replace(/\\left|\\right|\\operatorname|\s+/g, '').length;
}

/** One fraction P/Q with a readable sign (−P/Q rather than (−P)/Q); variants of P: expanded, common factor out, collected, factored. */
function fractionForms(S, v) {
    let cf;
    try {
        cf = combineFractions(S);
    } catch {
        return [];
    }
    if (cf.type !== 'div') return [];
    let N = cf.num;
    const D = cf.den;
    const allNeg = N.type === 'add' ? N.args.every(negLeading) : negLeading(N);
    const C = canonContext();
    let sign = false;
    if (allNeg) {
        sign = true;
        N = C.mul([NM1, N]);
    }
    const tops = [N];
    if (N.type === 'add') {
        for (const c of [factorCommon(N), collectFns(N, v)]) if (c) tops.push(c);
        const P = Poly.fromNode(N, v);
        if (P && P.degree >= 2) {
            const fs = polyShort(P, v, 'factored');
            if (fs.length > 1) tops.push(mul(fs));
        }
    }
    return tops.map((top) => (sign ? neg(div(top, D)) : div(top, D)));
}

/** simplify() repeated to a fixed point (a single pass can leave x·x^(−2) after |x|^(−2) → x^(−2)). */
function simp(node) {
    let s = simplify(node);
    for (let i = 0; i < 3; i++) {
        const t = simplify(s);
        if (nodeKey(t) === nodeKey(s)) break;
        s = t;
    }
    return s;
}

/** −c·(a − b)·… → c·(b − a)·…: the minus goes into a sum factor (1 − x² rather than −(x² − 1)). */
function absorbSign(n) {
    if (n.type !== 'mul' || !isNum(n.args[0]) || !n.args[0].value.isNeg()) return null;
    const k = n.args.findIndex((f) => f.type === 'add');
    if (k < 0) return null;
    const C = canonContext();
    const flipped = C.add(n.args[k].args.map((t) => C.mul([NM1, t])));
    const c = n.args[0].value.neg();
    const rest = n.args.slice(1).map((f, i) => (i + 1 === k ? flipped : f));
    return c.isOne() ? (rest.length === 1 ? rest[0] : mul(rest)) : mul([num(c), ...rest]);
}

/**
 * The tidiest equivalent form for answers: canonical (simplify.js), expanded, one fraction, common factor
 * taken out, the minus moved into a bracket, sin/cos → tg/ctg — the shortest TeX wins, and every candidate
 * is checked numerically. Returns a display node (prettyForm). Throws MathError 'div0' for an explicit
 * division by zero.
 */
export function niceForm(node, v = null, opts = {}) {
    let S;
    try {
        S = simp(node);
    } catch (e) {
        if (e instanceof MathError && e.code === 'div0') throw e;
        return prettyForm(node);
    }
    const vv = v ?? freeVars(S)[0] ?? 'x';
    const cands = [S];
    const push = (c) => {
        if (!c) return;
        try {
            if (!cands.some((x) => nodeKey(x) === nodeKey(c))) cands.push(c);
        } catch {
            // malformed candidate — skip
        }
    };
    const tryPush = (f) => {
        try {
            push(f());
        } catch {
            // a candidate that fails to build is simply not offered
        }
    };
    // structural rewrites of the canonical form
    if (hasNegPow(S) && nodeChildren(S).some((c) => c.type !== 'num' && hasNestedFraction(c))) tryPush(() => deepCombine(S));
    tryPush(() => absFix(S));
    if (S.type === 'add' && S.args.some((t) => t.type === 'mul' && t.args.some((f) => f.type === 'add'))) {
        // a sum with bracketed products inside (u·V − ∫v du after integrating by parts): multiply out
        tryPush(() => {
            const X = simp(expand(S));
            return X.type !== 'add' || X.args.length <= 16 ? X : null;
        });
    }
    for (const c of [...cands]) {
        if (c.type === 'mul' && c.args.some((f) => f.type === 'add' || (f.type === 'pow' && f.base.type === 'add'))) {
            tryPush(() => {
                const X = simp(expand(c));
                return X.type !== 'add' || X.args.length <= 12 ? X : null;
            });
        }
    }
    try {
        for (const x of ratCandidates(S, vv)) push(x);
    } catch {
        // not a rational function
    }
    tryPush(() => logCombine(S));
    for (const c of [...cands]) {
        if (c.type !== 'add') continue;
        tryPush(() => factorCommon(c, opts));
        tryPush(() => collectFns(c, vv));
        if (hasNegPow(c)) for (const x of fractionForms(c, vv)) push(x);
    }
    // a fraction may cancel once it is canonical again ((cos x + 1)/(cos x + 1)² → 1/(cos x + 1))
    for (const c of [...cands]) if (c.type === 'div' || c.type === 'neg') tryPush(() => simp(c));
    for (const c of [...cands]) tryPush(() => absorbRadicals(c.type === 'div' || c.type === 'neg' ? simp(c) : c, vv));
    for (const c of [...cands]) tryPush(() => absorbSign(c));
    for (const c of [...cands]) {
        tryPush(() => {
            const t = trigCombine(c);
            return t !== c ? t : null;
        });
    }
    let best = S;
    let bestScore = score(S);
    for (const c of cands.slice(1)) {
        const sc = score(c) + penalty(c, opts);
        if (sc >= bestScore) continue;
        if (agree(c, S, vv, { tol: 1e-9 }).ok === false) continue;
        best = c;
        bestScore = sc;
    }
    return prettyForm(best, { fnFirst: opts.fnFractions === false });
}

// a fraction whose numerator holds a radical reads worse than the sum it came from; for antiderivatives
// (opts.fnFractions === false) the same goes for ln, arctg, … in a numerator
function penalty(c, opts = {}) {
    const top = c.type === 'neg' ? c.arg : c;
    if (top.type === 'div' && hasRadical(top.num)) return 12;
    if (opts.fnFractions === false) {
        if (top.type === 'div' && hasFn(top.num)) return 1000;
        if (top.type === 'mul' && top.args.some((f) => f.type === 'pow' && isNum(f.exp) && f.exp.value.isNeg()) && top.args.some((f) => f.type === 'add' && hasFn(f))) return 1000;
    }
    return 0;
}

function hasFn(n) {
    if (n.type === 'fn' && n.name !== 'sqrt' && n.name !== 'root' && n.name !== 'abs') return true;
    return nodeChildren(n).some(hasFn);
}

function hasRadical(n) {
    if (n.type === 'pow' && isNum(n.exp) && !n.exp.value.isInt()) return true;
    if (n.type === 'fn' && (n.name === 'sqrt' || n.name === 'root')) return true;
    return nodeChildren(n).some(hasRadical);
}

function hasNestedFraction(n) {
    if (n.type === 'add' && hasNegPow(n)) return true;
    return nodeChildren(n).some(hasNestedFraction);
}

/** Bring every inner sum with fractions to one fraction, bottom-up (so 1/(1/x² + 1) → x²/(x² + 1)). */
function deepCombine(S) {
    return simp(
        mapNode(S, (m) => {
            if (m.type !== 'add' || !hasNegPow(m)) return undefined;
            try {
                return simplify(combineFractions(m));
            } catch {
                return undefined;
            }
        }),
    );
}

/** u^(2k)·|u|^m → |u|^(2k+m): x²/|x| = |x|. */
function absFix(S) {
    const C = canonContext();
    const out = mapNode(S, (m) => {
        if (m.type !== 'mul') return undefined;
        const abs = new Map();
        m.args.forEach((f, i) => {
            const b = f.type === 'pow' ? f.base : f;
            const e = f.type === 'pow' ? f.exp : N1;
            if (b.type === 'fn' && b.name === 'abs' && isNum(e) && e.value.isInt()) abs.set(nodeKey(b.args[0]), { i, e: e.value, b });
        });
        if (!abs.size) return undefined;
        const drop = new Set();
        const extra = [];
        m.args.forEach((f, i) => {
            const b = f.type === 'pow' ? f.base : f;
            const e = f.type === 'pow' ? f.exp : N1;
            const a = abs.get(nodeKey(b));
            if (!a || drop.has(a.i) || !isNum(e) || !e.value.isInt() || e.value.n % 2n !== 0n) return;
            drop.add(i);
            drop.add(a.i);
            extra.push(C.pow(a.b, num(a.e.add(e.value))));
        });
        if (!drop.size) return undefined;
        return C.mul([...m.args.filter((_, i) => !drop.has(i)), ...extra]);
    });
    return out === S ? null : simp(out);
}

/** Polynomial factors that are multiples of a radical's base move under it: (2 − 2x²)/√(1 − x²) → 2√(1 − x²). */
function absorbRadicals(S, v) {
    const C = canonContext();
    const out = mapNode(S, (m) => {
        if (m.type !== 'mul') return undefined;
        const rads = [];
        const polys = [];
        m.args.forEach((f, i) => {
            if (f.type === 'pow' && isNum(f.exp) && !f.exp.value.isInt()) {
                const B = f.base.type === 'add' ? Poly.fromNode(f.base, v) : null;
                if (B && B.degree >= 1) rads.push({ i, B, base: f.base, e: f.exp.value });
                return;
            }
            const isP = f.type === 'pow' && isNum(f.exp) && f.exp.value.isInt() && f.exp.value.isPos() && f.exp.value.le(20);
            const base = isP ? f.base : f;
            if (base.type !== 'add') return;
            const P = Poly.fromNode(base, v);
            if (P && P.degree >= 1) polys.push({ i, P: isP ? P.pow(Number(f.exp.value.n)) : P });
        });
        if (!rads.length || !polys.length) return undefined;
        let changed = false;
        for (const p of polys) {
            for (const r of rads) {
                while (p.P.degree >= r.B.degree) {
                    const { q, r: rem } = p.P.divmod(r.B);
                    if (!rem.isZero()) break;
                    p.P = q;
                    r.e = r.e.add(Q.ONE);
                    changed = true;
                }
            }
        }
        if (!changed) return undefined;
        const skip = new Set([...rads.map((r) => r.i), ...polys.map((p) => p.i)]);
        return C.mul([...m.args.filter((_, i) => !skip.has(i)), ...rads.map((r) => C.pow(r.base, num(r.e))), ...polys.map((p) => p.P.toNode(v))]);
    });
    return out === S ? null : simp(out);
}

/** Prime factorisation of a positive integer (trial division; a big leftover counts as one factor). */
function primeFactors(n) {
    const out = new Map();
    let m = n;
    for (let p = 2n; p * p <= m && p < 100000n; p += p === 2n ? 1n : 2n) {
        while (m % p === 0n) {
            out.set(p, (out.get(p) ?? 0n) + 1n);
            m /= p;
        }
    }
    if (m > 1n) out.set(m, (out.get(m) ?? 0n) + 1n);
    return out;
}

/** A positive numeric constant (rationals and their rational powers) as prime → exponent (Q), else null. */
function numericPrimes(x) {
    const acc = new Map();
    const addQ = (q, e) => {
        if (!q.isPos()) return false;
        for (const [p, k] of primeFactors(q.n)) acc.set(p, (acc.get(p) ?? Q.ZERO).add(e.mul(new Q(k))));
        for (const [p, k] of primeFactors(q.d)) acc.set(p, (acc.get(p) ?? Q.ZERO).sub(e.mul(new Q(k))));
        return true;
    };
    const fs = x.type === 'mul' ? x.args : [x];
    for (const f of fs) {
        if (isNum(f)) {
            if (!addQ(f.value, Q.ONE)) return null;
        } else if (f.type === 'pow' && isNum(f.base) && isNum(f.exp)) {
            if (!addQ(f.base.value, f.exp.value)) return null;
        } else return null;
    }
    return acc;
}

/** c₁·ln r₁ + c₂·ln r₂ + … with numeric rᵢ → c·ln R (½ln 2 + ½ln 3 − ½ln 4 → ½·ln(3/2)). */
function logCombine(S) {
    const terms = S.type === 'add' ? S.args : [S];
    const rest = [];
    const primes = new Map();
    let used = 0;
    for (const t of terms) {
        const { coef, rest: r } = splitCoeff(t);
        if (r && r.type === 'fn' && r.name === 'ln') {
            const f = numericPrimes(r.args[0]);
            if (f) {
                for (const [p, e] of f) primes.set(p, (primes.get(p) ?? Q.ZERO).add(e.mul(coef)));
                used++;
                continue;
            }
        }
        rest.push(t);
    }
    if (!used) return null;
    const exps = [...primes].filter(([, e]) => !e.isZero());
    const C = canonContext();
    if (!exps.length) return rest.length ? C.add(rest) : N0;
    let g = 0n;
    let l = 1n;
    for (const [, e] of exps) {
        g = bigGcd(g, e.n);
        l = bigLcm(l, e.d);
    }
    let c = new Q(g, l);
    if (exps.filter(([, e]) => e.isNeg()).length > exps.length / 2) c = c.neg();
    let R = Q.ONE;
    for (const [p, e] of exps) R = R.mul(new Q(p).pow(e.div(c).n));
    const lnR = mkLn(num(R));
    return C.add([...rest, C.mul([num(c), lnR])]);
}

const mkLn = (x) => Object.freeze({ type: 'fn', name: 'ln', args: Object.freeze([x]) });

/**
 * The expression as a rational function of v with rational coefficients, reduced: {num: Poly, den: Poly}
 * (den primitive with a positive leading coefficient), or null when it is not one (other letters, roots,
 * functions). Works on any AST (it is simplified first).
 */
export function ratFunctionOf(node, v = 'x') {
    let S;
    try {
        S = simp(node);
    } catch {
        return null;
    }
    const r = ratRec(S, v);
    if (!r) return null;
    let { p, q } = r;
    if (q.isZero()) return null;
    const g = p.isZero() ? q : p.gcd(q);
    if (g.degree > 0) {
        p = p.divmod(g).q;
        q = q.divmod(g).q;
    }
    const c = q.content();
    p = p.scale(c.inv());
    q = q.scale(c.inv());
    return { num: p, den: q };
}

function ratRec(n, v) {
    switch (n.type) {
        case 'num':
            return { p: new Poly([n.value]), q: new Poly([Q.ONE]) };
        case 'sym':
            return n.name === v && !isConst(n) ? { p: new Poly([Q.ZERO, Q.ONE]), q: new Poly([Q.ONE]) } : null;
        case 'add': {
            let acc = { p: new Poly([]), q: new Poly([Q.ONE]) };
            for (const a of n.args) {
                const r = ratRec(a, v);
                if (!r) return null;
                acc = { p: acc.p.mul(r.q).add(r.p.mul(acc.q)), q: acc.q.mul(r.q) };
                if (acc.q.degree > 80 || acc.p.degree > 80) return null;
            }
            return acc;
        }
        case 'mul': {
            let acc = { p: new Poly([Q.ONE]), q: new Poly([Q.ONE]) };
            for (const a of n.args) {
                const r = ratRec(a, v);
                if (!r) return null;
                acc = { p: acc.p.mul(r.p), q: acc.q.mul(r.q) };
                if (acc.q.degree > 80 || acc.p.degree > 80) return null;
            }
            return acc;
        }
        case 'pow': {
            if (!isNum(n.exp) || !n.exp.value.isInt() || n.exp.value.abs().gt(40)) return null;
            const b = ratRec(n.base, v);
            if (!b) return null;
            const k = Number(n.exp.value.n);
            const P = b.p.pow(Math.abs(k));
            const R = b.q.pow(Math.abs(k));
            return k >= 0 ? { p: P, q: R } : { p: R, q: P };
        }
        default:
            return null;
    }
}

function ratCandidates(S, v) {
    if (!hasNegPow(S)) return [];
    const r = ratFunctionOf(S, v);
    if (!r) return [];
    if (r.den.degree < 1) return [simp(div(r.num.toNode(v), r.den.toNode(v)))];
    let p = r.num;
    let sign = false;
    if (p.lead.isNeg()) {
        sign = true;
        p = p.neg();
    }
    const out = [];
    const tops = [p.toNode(v), mul(polyShort(p, v, 'factored'))];
    const bots = [r.den.toNode(v), mul(polyShort(r.den, v, 'factored'))];
    for (const top of tops) {
        for (const bot of bots) {
            const t = top.type === 'mul' && top.args.length === 1 ? top.args[0] : top;
            const b = bot.type === 'mul' && bot.args.length === 1 ? bot.args[0] : bot;
            out.push(sign ? neg(div(t, b)) : div(t, b));
        }
    }
    return out;
}

// ---------------------------------------------------------------- tidy assembly (unsimplified answers and step lines)

function tAdd(terms) {
    const out = [];
    for (const t of terms) {
        if (isZero(t)) continue;
        if (t.type === 'add') out.push(...t.args);
        else out.push(t);
    }
    if (!out.length) return N0;
    return out.length === 1 ? out[0] : add(out);
}

function tMul(factors) {
    let c = Q.ONE;
    const rest = [];
    for (let f of factors) {
        if (f.type === 'neg') {
            c = c.neg();
            f = f.arg;
        }
        if (isNum(f)) {
            if (f.value.isZero()) return N0;
            c = c.mul(f.value);
            continue;
        }
        if (f.type === 'mul') {
            for (const g of f.args) {
                if (isNum(g)) c = c.mul(g.value);
                else rest.push(g);
            }
            continue;
        }
        rest.push(f);
    }
    if (!rest.length) return num(c);
    if (c.isOne()) return rest.length === 1 ? rest[0] : mul(rest);
    if (c.eq(-1)) return neg(rest.length === 1 ? rest[0] : mul(rest));
    return mul([num(c), ...rest]);
}

function tNeg(a) {
    if (isZero(a)) return a;
    if (a.type === 'neg') return a.arg;
    if (isNum(a)) return num(a.value.neg());
    return neg(a);
}

// ---------------------------------------------------------------- TeX pieces for the rule lines
// A piece is {t: lang → TeX, k: 'atom' | 'prod' | 'sum' | 'neg' | 'zero' | 'one'}.

function kindOf(node) {
    if (isZero(node)) return 'zero';
    if (isOne(node)) return 'one';
    if (node.type === 'add') return 'sum';
    if (negLeading(node)) return 'neg';
    if (node.type === 'mul') return 'prod';
    return 'atom';
}

const pNode = (node) => ({ t: (L) => calcTex(node, L), k: kindOf(node) });
const pPrime = (node) => ({ t: (L) => `${paren(calcTex(node, L))}'`, k: 'atom' });

function pProd(pieces, { dropOnes = false } = {}) {
    let ps = pieces;
    if (ps.some((p) => p.k === 'zero')) return { t: () => '0', k: 'zero' };
    if (dropOnes) ps = ps.filter((p) => p.k !== 'one');
    if (!ps.length) return { t: () => '1', k: 'one' };
    if (ps.length === 1) return ps[0];
    const t = (L) =>
        ps
            .map((p, i) => {
                const s = p.t(L);
                return p.k === 'sum' || (p.k === 'neg' && i > 0) ? paren(s) : s;
            })
            .join(' \\cdot ');
    return { t, k: ps[0].k === 'neg' ? 'neg' : 'prod' };
}

/** terms: [{p, minus}] */
function pSum(terms, { dropZeros = false } = {}) {
    let ts = terms;
    if (dropZeros) ts = ts.filter((x) => x.p.k !== 'zero');
    if (!ts.length) return { t: () => '0', k: 'zero' };
    if (ts.length === 1 && !ts[0].minus) return ts[0].p;
    const t = (L) =>
        ts
            .map((x, i) => {
                let s = x.p.t(L);
                if (x.minus) {
                    if (x.p.k === 'sum' || x.p.k === 'neg') s = paren(s);
                    return (i ? ' - ' : '-') + s;
                }
                if (i && x.p.k === 'neg') return ' - ' + s.replace(/^-\s*/, '');
                return (i ? ' + ' : '') + s;
            })
            .join('');
    return { t, k: ts.length === 1 ? 'neg' : 'sum' };
}

const pFrac = (a, b) => ({ t: (L) => `\\frac{${a.t(L)}}{${b.t(L)}}`, k: 'atom' });
const pNeg = (a) => ({ t: (L) => '-' + (a.k === 'sum' || a.k === 'neg' ? paren(a.t(L)) : a.t(L)), k: 'neg' });

/** "lhs = a = b = c" without repeating equal neighbours. */
function chainTex(parts) {
    return bt((L) => {
        const out = [];
        for (const p of parts) {
            if (!p) continue;
            const s = typeof p === 'function' ? p(L) : p.t(L);
            const norm = (x) => x.replace(/\\left|\\right|\\cdot|\s+/g, '');
            if (out.length && norm(out[out.length - 1]) === norm(s)) {
                out[out.length - 1] = s;
                continue;
            }
            out.push(s);
        }
        return out.join(' = ');
    });
}

// x^{-2}, x^{\frac{1}{2}} written as a power (the printer would turn them into fractions and roots)
function texPowRaw(base, e, L) {
    let b = calcTex(base, L);
    if (!(base.type === 'sym' || (isNum(base) && base.value.isInt() && !base.value.isNeg()))) b = paren(b);
    return `${b}^{${e.toTex(L)}}`;
}

// ---------------------------------------------------------------- names and table formulas for the texts

const FN_NAME = {
    sin: ['синус', 'sine'],
    cos: ['косинус', 'cosine'],
    tan: ['тангенс', 'tangent'],
    cot: ['котангенс', 'cotangent'],
    sec: ['секанс', 'secant'],
    csc: ['косеканс', 'cosecant'],
    asin: ['арксинус', 'arcsine'],
    acos: ['арккосинус', 'arccosine'],
    atan: ['арктангенс', 'arctangent'],
    acot: ['арккотангенс', 'arccotangent'],
    sinh: ['гиперболический синус', 'hyperbolic sine'],
    cosh: ['гиперболический косинус', 'hyperbolic cosine'],
    tanh: ['гиперболический тангенс', 'hyperbolic tangent'],
    coth: ['гиперболический котангенс', 'hyperbolic cotangent'],
    asinh: ['обратный гиперболический синус', 'inverse hyperbolic sine'],
    acosh: ['обратный гиперболический косинус', 'inverse hyperbolic cosine'],
    atanh: ['обратный гиперболический тангенс', 'inverse hyperbolic tangent'],
    ln: ['натуральный логарифм', 'natural logarithm'],
    lg: ['десятичный логарифм', 'common logarithm'],
    log: ['логарифм', 'logarithm'],
    sqrt: ['квадратный корень', 'square root'],
    abs: ['модуль', 'absolute value'],
};

const FORMULA = {
    sin: (u) => [`(sin ${u})′ = cos ${u}`],
    cos: (u) => [`(cos ${u})′ = −sin ${u}`],
    tan: (u) => [`(tg ${u})′ = 1/cos² ${u}`, `(tan ${u})′ = 1/cos² ${u}`],
    cot: (u) => [`(ctg ${u})′ = −1/sin² ${u}`, `(cot ${u})′ = −1/sin² ${u}`],
    sec: (u) => [`(sec ${u})′ = sec ${u}·tg ${u}`, `(sec ${u})′ = sec ${u}·tan ${u}`],
    csc: (u) => [`(cosec ${u})′ = −cosec ${u}·ctg ${u}`, `(csc ${u})′ = −csc ${u}·cot ${u}`],
    asin: (u) => [`(arcsin ${u})′ = 1/√(1 − ${u}²)`],
    acos: (u) => [`(arccos ${u})′ = −1/√(1 − ${u}²)`],
    atan: (u) => [`(arctg ${u})′ = 1/(1 + ${u}²)`, `(arctan ${u})′ = 1/(1 + ${u}²)`],
    acot: (u) => [`(arcctg ${u})′ = −1/(1 + ${u}²)`, `(arccot ${u})′ = −1/(1 + ${u}²)`],
    sinh: (u) => [`(sh ${u})′ = ch ${u}`, `(sinh ${u})′ = cosh ${u}`],
    cosh: (u) => [`(ch ${u})′ = sh ${u}`, `(cosh ${u})′ = sinh ${u}`],
    tanh: (u) => [`(th ${u})′ = 1/ch² ${u}`, `(tanh ${u})′ = 1/cosh² ${u}`],
    coth: (u) => [`(cth ${u})′ = −1/sh² ${u}`, `(coth ${u})′ = −1/sinh² ${u}`],
    asinh: (u) => [`(arsh ${u})′ = 1/√(${u}² + 1)`, `(arsinh ${u})′ = 1/√(${u}² + 1)`],
    acosh: (u) => [`(arch ${u})′ = 1/√(${u}² − 1)`, `(arcosh ${u})′ = 1/√(${u}² − 1)`],
    atanh: (u) => [`(arth ${u})′ = 1/(1 − ${u}²)`, `(artanh ${u})′ = 1/(1 − ${u}²)`],
    ln: (u) => [`(ln ${u})′ = 1/${u}`],
    lg: (u) => [`(lg ${u})′ = 1/(${u}·ln 10)`, `(log₁₀ ${u})′ = 1/(${u}·ln 10)`],
    sqrt: (u) => [`(√${u})′ = 1/(2√${u})`],
};

function formula(name, u) {
    const f = FORMULA[name];
    if (!f) return null;
    const [ru, en] = f(u);
    return { ru, en: en ?? ru };
}

/** f'(u) for the step lines (readable, not canonical). */
function outerReadable(name, u, args) {
    const u2 = pow(u, N2);
    switch (name) {
        case 'sin':
            return fn('cos', u);
        case 'cos':
            return neg(fn('sin', u));
        case 'tan':
            return div(N1, pow(fn('cos', u), N2));
        case 'cot':
            return neg(div(N1, pow(fn('sin', u), N2)));
        case 'sec':
            return mul(fn('sec', u), fn('tan', u));
        case 'csc':
            return neg(mul(fn('csc', u), fn('cot', u)));
        case 'asin':
            return div(N1, fn('sqrt', add(N1, neg(u2))));
        case 'acos':
            return neg(div(N1, fn('sqrt', add(N1, neg(u2)))));
        case 'atan':
            return div(N1, add(N1, u2));
        case 'acot':
            return neg(div(N1, add(N1, u2)));
        case 'sinh':
            return fn('cosh', u);
        case 'cosh':
            return fn('sinh', u);
        case 'tanh':
            return div(N1, pow(fn('cosh', u), N2));
        case 'coth':
            return neg(div(N1, pow(fn('sinh', u), N2)));
        case 'asinh':
            return div(N1, fn('sqrt', add(u2, N1)));
        case 'acosh':
            return div(N1, fn('sqrt', add(u2, NM1)));
        case 'atanh':
            return div(N1, add(N1, neg(u2)));
        case 'ln':
            return div(N1, u);
        case 'lg':
            return div(N1, mul(u, fn('ln', num(10))));
        case 'log':
            return div(N1, mul(u, fn('ln', args[0])));
        case 'sqrt':
            return div(N1, mul(N2, fn('sqrt', u)));
        case 'abs':
            return div(u, fn('abs', u));
        default:
            return null;
    }
}

// ---------------------------------------------------------------- the step tree

function splitSignTerm(t) {
    if (t.type === 'neg') return { minus: true, abs: t.arg };
    if (isNum(t) && t.value.isNeg()) return { minus: true, abs: num(t.value.neg()) };
    if (t.type === 'mul' && isNum(t.args[0]) && t.args[0].value.isNeg()) {
        const c = t.args[0].value.neg();
        const rest = t.args.slice(1);
        return { minus: true, abs: c.isOne() ? (rest.length === 1 ? rest[0] : mul(rest)) : mul([num(c), ...rest]) };
    }
    return { minus: false, abs: t };
}

function simplifyNum(node) {
    try {
        const s = simplify(node);
        return isNum(s) ? s.value : null;
    } catch {
        return null;
    }
}

/**
 * Differentiate n by ctx.v with steps → {raw, res, step, trivial?}: raw — the assembled derivative before
 * simplification, res — its clean form (display node), step — the Step of this node.
 */
function dS(n, ctx) {
    const { v } = ctx;
    if (!containsVar(n, v)) {
        const others = freeVars(n).filter((w) => w !== v);
        const st = step({
            title: T_('Производная постоянной', 'Derivative of a constant'),
            tex: bt((L) => `${paren(calcTex(n, L))}' = 0`),
            text: others.length
                ? T_(`От ${v} не зависит: ${others.join(', ')} при дифференцировании по ${v} считаем постоянными. Производная постоянной равна нулю.`,
                    `It does not depend on ${v}: when differentiating with respect to ${v} we treat ${others.join(', ')} as constants. The derivative of a constant is zero.`)
                : T_('Производная числа равна нулю: постоянная не меняется.', 'The derivative of a number is zero: a constant does not change.'),
            rule: 'const',
        });
        return { raw: N0, res: N0, step: st, trivial: true };
    }
    switch (n.type) {
        case 'sym':
            return { raw: N1, res: N1, trivial: true, step: step({ title: T_('Производная переменной', 'Derivative of the variable'), tex: `(${calcTex(n)})' = 1`, rule: 'var' }) };
        case 'add':
            return dSum(n, ctx);
        case 'neg':
            return dNeg(n, ctx);
        case 'mul':
            return dMul(n, ctx);
        case 'div':
            return dDiv(n, ctx);
        case 'pow':
            return dPow(n, ctx);
        case 'fn':
            return dFn(n, ctx);
        default:
            throw new MathError({ ru: 'Не умею дифференцировать это выражение', en: 'Cannot differentiate this expression' }, null, null, 'unsupported');
    }
}

const subSteps = (kids) => kids.filter((c) => c && c.step && !c.trivial).map((c) => c.step);

function finish(shown, ctx, { title, text, rule, ruleLine, assembled, asm, raw, kids, extraSub }) {
    const res = niceForm(asm, ctx.v);
    const tex = chainTex([(L) => `${paren(calcTex(shown, L))}'`, ruleLine, assembled, pNode(res)]);
    const sub = [...(extraSub ?? []), ...subSteps(kids ?? [])];
    return { raw, res, step: step({ title, tex, text, rule, sub }) };
}

function dSum(n, ctx) {
    const terms = n.args.map(splitSignTerm);
    const kids = terms.map((t) => dS(t.abs, ctx));
    return finish(n, ctx, {
        title: T_('Производная суммы', 'Derivative of a sum'),
        text: T_('Производная суммы равна сумме производных: дифференцируем каждое слагаемое отдельно.', 'The derivative of a sum is the sum of the derivatives: differentiate term by term.'),
        rule: 'sum',
        ruleLine: pSum(terms.map((t) => ({ p: pPrime(t.abs), minus: t.minus }))),
        assembled: pSum(terms.map((t, i) => ({ p: pNode(kids[i].res), minus: t.minus })), { dropZeros: true }),
        asm: tAdd(terms.map((t, i) => (t.minus ? tNeg(kids[i].res) : kids[i].res))),
        raw: tAdd(terms.map((t, i) => (t.minus ? tNeg(kids[i].raw) : kids[i].raw))),
        kids,
    });
}

function dNeg(n, ctx) {
    const k = dS(n.arg, ctx);
    return finish(n, ctx, {
        title: T_('Минус выносим', 'Take the minus out'),
        text: T_('Знак минус — это множитель −1, его выносим за знак производной.', 'The minus sign is a factor −1; it comes out of the derivative.'),
        rule: 'neg',
        ruleLine: pNeg(pPrime(n.arg)),
        assembled: pNeg(pNode(k.res)),
        asm: tNeg(k.res),
        raw: tNeg(k.raw),
        kids: [k],
    });
}

function dMul(n, ctx) {
    const { v } = ctx;
    const consts = n.args.filter((f) => !containsVar(f, v));
    const vars = n.args.filter((f) => containsVar(f, v));
    if (consts.length) {
        const c = consts.length === 1 ? consts[0] : mul(consts);
        const u = vars.length === 1 ? vars[0] : mul(vars);
        const k = dS(u, ctx);
        return finish(n, ctx, {
            title: T_('Постоянный множитель', 'Constant factor'),
            text: T_('Постоянный множитель выносим за знак производной: (c·u)′ = c·u′.', 'A constant factor comes out of the derivative: (c·u)′ = c·u′.'),
            rule: 'const-factor',
            ruleLine: pProd([pNode(c), pPrime(u)]),
            assembled: pProd([pNode(c), pNode(k.res)], { dropOnes: true }),
            asm: tMul([c, k.res]),
            raw: tMul([c, k.raw]),
            kids: [k],
        });
    }
    const kids = vars.map((f) => dS(f, ctx));
    const termOf = (i, d) => tMul(vars.map((g, j) => (i === j ? d : g)));
    const two = vars.length === 2;
    return finish(n, ctx, {
        title: T_('Правило произведения', 'Product rule'),
        text: two
            ? T_('По правилу произведения: производная первого множителя на второй плюс первый на производную второго, (uv)′ = u′v + uv′.',
                'By the product rule: the derivative of the first factor times the second plus the first times the derivative of the second, (uv)′ = u′v + uv′.')
            : T_('Правило произведения для нескольких множителей: по очереди дифференцируем один множитель, остальные оставляем как есть, и всё складываем.',
                'The product rule for several factors: differentiate one factor at a time, keep the others as they are, and add everything up.'),
        rule: 'product',
        ruleLine: pSum(vars.map((_, i) => ({ p: pProd(vars.map((g, j) => (i === j ? pPrime(g) : pNode(g)))) }))),
        assembled: pSum(vars.map((_, i) => ({ p: pProd(vars.map((g, j) => pNode(i === j ? kids[i].res : g)), { dropOnes: true }) })), { dropZeros: true }),
        asm: tAdd(vars.map((_, i) => termOf(i, kids[i].res))),
        raw: tAdd(vars.map((_, i) => termOf(i, kids[i].raw))),
        kids,
    });
}

/** w = v, v^k, √v, ⁿ√v → the exponent (Q), else null. */
function powerOfVar(w, v) {
    const isV = (x) => x.type === 'sym' && x.name === v && !isConst(x);
    if (isV(w)) return Q.ONE;
    if (w.type === 'pow' && isV(w.base)) return simplifyNum(w.exp);
    if (w.type === 'fn' && w.name === 'sqrt' && isV(w.args[0])) return Q.HALF;
    if (w.type === 'fn' && w.name === 'root' && isV(w.args[0])) {
        const k = simplifyNum(w.args[1]);
        return k && !k.isZero() ? k.inv() : null;
    }
    return null;
}

function dDiv(n, ctx) {
    const { v } = ctx;
    const u = n.num;
    const w = n.den;
    const uv = containsVar(u, v);
    const wv = containsVar(w, v);
    if (!wv) {
        const k = dS(u, ctx);
        return finish(n, ctx, {
            title: T_('Деление на постоянную', 'Division by a constant'),
            text: T_('Знаменатель от переменной не зависит — это постоянный множитель 1/c, его выносим за знак производной.', 'The denominator does not depend on the variable: it is a constant factor 1/c that comes out of the derivative.'),
            rule: 'const-factor',
            ruleLine: pFrac(pPrime(u), pNode(w)),
            assembled: pFrac(pNode(k.res), pNode(w)),
            asm: div(k.res, w),
            raw: div(k.raw, w),
            kids: [k],
        });
    }
    if (!uv) {
        const e = powerOfVar(w, v);
        if (e) {
            // c / x^k = c·x^(−k)
            const X = sym(v);
            const k = e.neg();
            const rewritten = isOne(u) ? pow(X, num(k)) : mul(u, pow(X, num(k)));
            const inner = dS(rewritten, ctx);
            const coefT = (L) => (isOne(u) ? '' : u.type === 'add' ? paren(calcTex(u, L)) : calcTex(u, L));
            const st = step({
                title: T_('Записываем как степень', 'Write it as a power'),
                tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, (L) => `${paren(coefT(L) + texPowRaw(X, k, L))}'`, pNode(inner.res)]),
                text: T_(`Переменная стоит только в знаменателе, поэтому удобно записать дробь как степень с отрицательным показателем: 1/${v}ᵏ = ${v}⁻ᵏ, и взять производную степени.`,
                    `The variable is only in the denominator, so write the fraction as a power with a negative exponent, 1/${v}ᵏ = ${v}⁻ᵏ, and use the power rule.`),
                rule: 'rewrite-power',
                sub: inner.step && !inner.trivial ? [inner.step] : [],
            });
            return { raw: inner.raw, res: inner.res, step: st };
        }
        const k = dS(w, ctx);
        const w2 = pow(w, N2);
        return finish(n, ctx, {
            title: T_('Постоянная, делённая на функцию', 'A constant over a function'),
            text: T_('Числитель постоянный, поэтому от правила частного остаётся одно слагаемое: (c/v)′ = −c·v′/v².', 'The numerator is constant, so only one term of the quotient rule is left: (c/v)′ = −c·v′/v².'),
            rule: 'quotient',
            ruleLine: pNeg(pFrac(pProd([pNode(u), pPrime(w)], { dropOnes: true }), pNode(w2))),
            assembled: pNeg(pFrac(pProd([pNode(u), pNode(k.res)], { dropOnes: true }), pNode(w2))),
            asm: tNeg(div(tMul([u, k.res]), w2)),
            raw: tNeg(div(tMul([u, k.raw]), w2)),
            kids: [k],
        });
    }
    const ku = dS(u, ctx);
    const kw = dS(w, ctx);
    const w2 = pow(w, N2);
    return finish(n, ctx, {
        title: T_('Правило частного', 'Quotient rule'),
        text: T_('Производная дроби: производная числителя на знаменатель минус числитель на производную знаменателя, и всё делим на квадрат знаменателя: (u/v)′ = (u′v − uv′)/v².',
            'The derivative of a fraction: the derivative of the numerator times the denominator minus the numerator times the derivative of the denominator, all over the denominator squared: (u/v)′ = (u′v − uv′)/v².'),
        rule: 'quotient',
        ruleLine: pFrac(pSum([{ p: pProd([pPrime(u), pNode(w)]) }, { p: pProd([pNode(u), pPrime(w)]), minus: true }]), pNode(w2)),
        assembled: pFrac(
            pSum([{ p: pProd([pNode(ku.res), pNode(w)], { dropOnes: true }) }, { p: pProd([pNode(u), pNode(kw.res)], { dropOnes: true }), minus: true }], { dropZeros: true }),
            pNode(w2),
        ),
        asm: div(tAdd([tMul([ku.res, w]), tNeg(tMul([u, kw.res]))]), w2),
        raw: div(tAdd([tMul([ku.raw, w]), tNeg(tMul([u, kw.raw]))]), w2),
        kids: [ku, kw],
    });
}

/** TeX of n·b^(n−1) for the power rule (b^{n−1} written as a power). */
function powerPiece(b, e, eq) {
    const t = (L) => {
        let coef;
        if (eq) coef = eq.isOne() ? '' : eq.eq(-1) ? '-' : eq.toTex(L);
        else coef = e.type === 'add' || negLeading(e) ? paren(calcTex(e, L)) : calcTex(e, L);
        let pw;
        if (eq) {
            const m = eq.sub(Q.ONE);
            if (m.isZero()) pw = '';
            else if (m.isOne()) pw = b.type === 'sym' ? calcTex(b, L) : paren(calcTex(b, L));
            else pw = texPowRaw(b, m, L);
        } else {
            const bt0 = b.type === 'sym' ? calcTex(b, L) : paren(calcTex(b, L));
            pw = `${bt0}^{${calcTex(add(e, NM1), L)}}`;
        }
        if (!pw) return coef === '' ? '1' : coef === '-' ? '-1' : coef;
        const sep = /\\frac/.test(coef) || (!eq && coef.length > 1) ? ' \\cdot ' : '';
        return coef + sep + pw;
    };
    return { t, k: eq && eq.isNeg() ? 'neg' : 'prod' };
}

function dPow(n, ctx, shown = n) {
    const { v } = ctx;
    const b = n.base;
    const e = n.exp;
    const bv = containsVar(b, v);
    const ev = containsVar(e, v);
    if (bv && !ev) {
        const eq = simplifyNum(e);
        const outer = tMul([eq ? num(eq) : e, pow(b, eq ? num(eq.sub(Q.ONE)) : add(e, NM1))]);
        const piece = powerPiece(b, e, eq);
        if (b.type === 'sym') {
            const res = niceForm(outer, v);
            return {
                raw: outer,
                res,
                step: step({
                    title: T_('Производная степени', 'Power rule'),
                    tex: chainTex([(L) => `${paren(calcTex(shown, L))}'`, piece, pNode(res)]),
                    text: T_(`(${v}ⁿ)′ = n·${v}ⁿ⁻¹: показатель становится множителем, а степень уменьшается на единицу.`, `(${v}ⁿ)′ = n·${v}ⁿ⁻¹: the exponent becomes a factor and the power drops by one.`),
                    rule: 'power',
                }),
            };
        }
        const k = dS(b, ctx);
        return finish(shown, ctx, {
            title: T_('Степень сложной функции', 'Power of a function (chain rule)'),
            text: T_(`Сложная функция: внешняя — степень uⁿ, внутренняя — u = ${plain(b, 'ru')}. По цепному правилу (uⁿ)′ = n·uⁿ⁻¹·u′.`,
                `A composite function: the outer one is the power uⁿ, the inner one is u = ${plain(b, 'en')}. By the chain rule (uⁿ)′ = n·uⁿ⁻¹·u′.`),
            rule: 'chain',
            ruleLine: pProd([piece, pPrime(b)]),
            assembled: pProd([piece, pNode(k.res)], { dropOnes: true }),
            asm: tMul([outer, k.res]),
            raw: tMul([outer, k.raw]),
            kids: [k],
        });
    }
    if (!bv && ev) {
        const isE = isConst(b) && b.name === 'e';
        const lnB = fn('ln', b);
        const outer = isE ? n : mul(n, lnB);
        if (e.type === 'sym') {
            const res = niceForm(outer, v);
            return {
                raw: outer,
                res,
                step: step({
                    title: isE ? T_('Производная экспоненты', 'Derivative of the exponential') : T_('Показательная функция', 'Exponential function'),
                    tex: chainTex([(L) => `${paren(calcTex(shown, L))}'`, pNode(outer), pNode(res)]),
                    text: isE
                        ? T_(`(e^${v})′ = e^${v}: экспонента при дифференцировании не меняется.`, `(e^${v})′ = e^${v}: the exponential is its own derivative.`)
                        : T_(`Табличная производная: (a^${v})′ = a^${v}·ln a.`, `A table derivative: (a^${v})′ = a^${v}·ln a.`),
                    rule: isE ? 'exp' : 'exp-base',
                }),
            };
        }
        const k = dS(e, ctx);
        const outerPieces = isE ? [pNode(n)] : [pNode(n), pNode(lnB)];
        return finish(shown, ctx, {
            title: isE ? T_('Экспонента от функции', 'Exponential of a function') : T_('Показательная функция от функции', 'Exponential function of a function'),
            text: isE
                ? T_(`Сложная функция: внешняя — экспонента, внутренняя — u = ${plain(e, 'ru')}. (eᵘ)′ = eᵘ·u′.`, `A composite function: the outer one is the exponential, the inner one is u = ${plain(e, 'en')}. (eᵘ)′ = eᵘ·u′.`)
                : T_(`Сложная функция: внешняя — показательная aᵘ, внутренняя — u = ${plain(e, 'ru')}. (aᵘ)′ = aᵘ·ln a·u′.`, `A composite function: the outer one is aᵘ, the inner one is u = ${plain(e, 'en')}. (aᵘ)′ = aᵘ·ln a·u′.`),
            rule: 'chain',
            ruleLine: pProd([...outerPieces, pPrime(e)]),
            assembled: pProd([...outerPieces, pNode(k.res)], { dropOnes: true }),
            asm: tMul([outer, k.res]),
            raw: tMul([outer, k.raw]),
            kids: [k],
        });
    }
    // both vary: u^w = e^(w ln u)
    const prod = mul(e, fn('ln', b));
    const k = dS(prod, ctx);
    return finish(shown, ctx, {
        title: T_('Логарифмическое дифференцирование', 'Logarithmic differentiation'),
        text: T_('Переменная есть и в основании, и в показателе, поэтому не подходит ни правило степени, ни правило показательной функции. Запишем uᵛ = e^(v·ln u): тогда (uᵛ)′ = uᵛ·(v·ln u)′. То же получится, если прологарифмировать: ln y = v·ln u.',
            'The variable is both in the base and in the exponent, so neither the power rule nor the exponential rule applies. Write uᵛ = e^(v·ln u); then (uᵛ)′ = uᵛ·(v·ln u)′. Taking logarithms, ln y = v·ln u, gives the same.'),
        rule: 'log-diff',
        ruleLine: pProd([pNode(n), pPrime(prod)]),
        assembled: pProd([pNode(n), pNode(k.res)], { dropOnes: true }),
        asm: tMul([n, k.res]),
        raw: tMul([n, k.raw]),
        kids: [k],
    });
}

function dFn(n, ctx) {
    const { v } = ctx;
    const name = n.name;
    if (name === 'fact') throw FACT_ERR();
    if (name === 'exp') return dPow(pow(E_, n.args[0]), ctx, n);
    if (name === 'root') {
        const [x, k] = n.args;
        const kq = simplifyNum(k);
        if (!kq || kq.isZero()) return dS(pow(x, div(N1, k)), ctx);
        const inner = dPow(pow(x, num(kq.inv())), ctx);
        const st = step({
            title: T_('Корень как степень', 'A root as a power'),
            tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, (L) => `${paren(texPowRaw(x, kq.inv(), L))}'`, pNode(inner.res)]),
            text: T_('Корень n-й степени — это степень с показателем 1/n: ⁿ√u = u^(1/n). Дальше — правило степени.', 'An n-th root is a power with exponent 1/n: ⁿ√u = u^(1/n). Then the power rule.'),
            rule: 'rewrite-power',
            sub: inner.step ? [inner.step] : [],
        });
        return { raw: inner.raw, res: inner.res, step: st };
    }
    if (name === 'log' && containsVar(n.args[0], v)) {
        const q = div(fn('ln', n.args[1]), fn('ln', n.args[0]));
        const inner = dS(q, ctx);
        const st = step({
            title: T_('Переход к натуральному логарифму', 'Change to the natural logarithm'),
            tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, (L) => `${paren(calcTex(q, L))}'`, pNode(inner.res)]),
            text: T_('Основание логарифма зависит от переменной, поэтому переходим к натуральным логарифмам: logₐb = ln b / ln a.', 'The base depends on the variable, so switch to natural logarithms: logₐb = ln b / ln a.'),
            rule: 'log-base',
            sub: inner.step ? [inner.step] : [],
        });
        return { raw: inner.raw, res: inner.res, step: st };
    }
    if (name === 'sign' || name === 'floor' || name === 'ceil') {
        const text = name === 'sign'
            ? T_('Функция sgn постоянна и слева, и справа от нуля, поэтому её производная равна 0 везде, где аргумент не равен нулю (в самом нуле скачок, и производной нет).',
                'sgn is constant on each side of zero, so its derivative is 0 wherever the argument is not zero (at zero there is a jump and no derivative).')
            : T_('Функция постоянна между соседними целыми значениями аргумента, поэтому производная равна 0 везде, кроме точек, где аргумент целый (там скачок, и производной нет).',
                'The function is constant between consecutive whole values of the argument, so the derivative is 0 except where the argument is a whole number (there it jumps and has no derivative).');
        return { raw: N0, res: N0, step: step({ title: T_('Ступенчатая функция', 'A step function'), tex: bt((L) => `${paren(calcTex(n, L))}' = 0`), text, rule: 'step-fn' }) };
    }
    const u = name === 'log' ? n.args[1] : n.args[0];
    const outer = outerReadable(name, u, n.args);
    if (!outer) throw new MathError({ ru: `Не умею дифференцировать функцию ${name}`, en: `Cannot differentiate ${name}` }, null, null, 'unsupported');
    const absNote = name === 'abs'
        ? T_(' Это верно при u ≠ 0: в нуле у модуля излом, и производной там нет.', ' This holds for u ≠ 0: the absolute value has a corner at zero, with no derivative there.')
        : T_('', '');
    if (u.type === 'sym' && u.name === v && !isConst(u)) {
        const res = niceForm(outer, v);
        const f = formula(name, v);
        let text;
        if (name === 'abs') text = T_(`(|${v}|)′ = ${v}/|${v}|: это +1 при ${v} > 0 и −1 при ${v} < 0. В нуле у модуля излом, и производной там нет.`, `(|${v}|)′ = ${v}/|${v}|: it is +1 for ${v} > 0 and −1 for ${v} < 0. At zero there is a corner, with no derivative.`);
        else if (name === 'log') text = T_(`Табличная производная: (logₐ ${v})′ = 1/(${v}·ln a).`, `A table derivative: (logₐ ${v})′ = 1/(${v}·ln a).`);
        else if (f) text = T_(`Табличная производная: ${f.ru}.`, `A table derivative: ${f.en}.`);
        return {
            raw: outer,
            res,
            step: step({ title: T_('Табличная производная', 'Table derivative'), tex: chainTex([(L) => `${paren(calcTex(n, L))}'`, pNode(outer), pNode(res)]), text, rule: 'table' }),
        };
    }
    const k = dS(u, ctx);
    const nm = FN_NAME[name] ?? [name, name];
    const f = formula(name, 'u');
    let law;
    if (name === 'log') law = T_('(logₐ u)′ = u′/(u·ln a)', '(logₐ u)′ = u′/(u·ln a)');
    else if (name === 'abs') law = T_('(|u|)′ = u/|u|·u′', '(|u|)′ = u/|u|·u′');
    else law = T_(`${f.ru}·u′`, `${f.en}·u′`);
    return finish(n, ctx, {
        title: T_(`Сложная функция: ${nm[0]}`, `Chain rule: ${nm[1]}`),
        text: T_(`Внешняя функция — ${nm[0]}, внутренняя — u = ${plain(u, 'ru')}. Берём производную внешней функции по u и умножаем на производную внутренней: ${law.ru}.${absNote.ru}`,
            `The outer function is the ${nm[1]}, the inner one is u = ${plain(u, 'en')}. Differentiate the outer function with respect to u and multiply by the derivative of the inner one: ${law.en}.${absNote.en}`),
        rule: 'chain',
        ruleLine: pProd([pNode(outer), pPrime(u)]),
        assembled: pProd([pNode(outer), pNode(k.res)], { dropOnes: true }),
        asm: tMul([outer, k.res]),
        raw: tMul([outer, k.raw]),
        kids: [k],
    });
}

// ---------------------------------------------------------------- numeric check against central differences

function smoothPoints(f, v, count, seed) {
    const r = rng(seed);
    const vars = freeVars(f).filter((w) => w !== v);
    const ranges = [[0.3, 1.7], [-1.7, -0.3], [1.7, 4], [-4, -1.7], [0.1, 0.9], [-0.9, -0.1]];
    const out = [];
    for (let k = 0; k < count * 4 && out.length < count; k++) {
        const env = randomEnv(vars, r);
        const [lo, hi] = ranges[k % ranges.length];
        env[v] = r.real(lo, hi);
        const h = 1e-3 * Math.max(1, Math.abs(env[v]));
        try {
            const ys = [-2, -1, 0, 1, 2].map((j) => evaluate(f, { ...env, [v]: env[v] + j * h }));
            if (ys.every((y) => Number.isFinite(y) && Math.abs(y) < 1e8)) out.push(env);
        } catch {
            return out;
        }
    }
    return out;
}

/** Five-point central difference with one Richardson step; NaN when two step sizes disagree (a point too close to a pole). */
function centralDiff(f, env, v) {
    const x = env[v];
    const at = (t) => evaluate(f, { ...env, [v]: t });
    const D = (h) => (at(x - 2 * h) - 8 * at(x - h) + 8 * at(x + h) - at(x + 2 * h)) / (12 * h);
    const h = 1e-3 * Math.max(1, Math.abs(x));
    const a = D(h);
    const b = D(h / 2);
    if (!Number.isFinite(a) || !Number.isFinite(b) || Math.abs(a - b) > 1e-6 * Math.max(1, Math.abs(b))) return NaN;
    return (16 * b - a) / 15;
}

function numericCheck(f, d, v) {
    const pts = smoothPoints(f, v, 6, 101);
    let ok = 0;
    for (const env of pts) {
        let a;
        let b;
        try {
            a = evaluate(d, env);
            b = centralDiff(f, env, v);
        } catch {
            return null;
        }
        if (!Number.isFinite(a) || !Number.isFinite(b)) continue;
        if (Math.abs(a - b) > 1e-5 * Math.max(1, Math.abs(a), Math.abs(b))) return false;
        ok++;
    }
    return ok >= 2 ? true : null;
}

// ---------------------------------------------------------------- public API

function primeTex(v, order = 1, partial = false, name = 'f') {
    if (partial) return order === 1 ? `\\frac{\\partial ${name}}{\\partial ${v}}` : `\\frac{\\partial^{${order}} ${name}}{\\partial ${v}^{${order}}}`;
    const marks = order <= 3 ? "'".repeat(order) : `^{(${order})}`;
    return `${name}${marks}(${v})`;
}

function answerStep(title, tex) {
    const s = step({ title, tex, rule: 'answer' });
    s.final = true;
    return s;
}

/**
 * Derivative of node (AST or string) by v. opts: {steps = false, simplify = true, partial = false}.
 * → {result (display node), steps (Step[], empty unless asked), verified, tex ("f'(x) = …", string | {ru, en})}.
 * Other letters are constants (a partial derivative). Throws MathError for equations/lists and fact().
 */
export function derivative(node, v = 'x', opts = {}) {
    node = asNode(node);
    checkExpr(node);
    const wantSteps = !!opts.steps;
    const partial = !!opts.partial;
    const fast = quickDerivative(node, v);
    let result;
    const steps = [];
    if (wantSteps || opts.simplify === false) {
        const r = dS(node, { v });
        result = opts.simplify === false ? r.raw : r.res;
        if (wantSteps) {
            const others = freeVars(node).filter((w) => w !== v);
            steps.push(step({
                title: T_('Что дифференцируем', 'What we differentiate'),
                tex: bt((L) => `f(${v}) = ${calcTex(node, L)}`),
                text: others.length
                    ? T_(`Ищем производную по ${v}. Остальные буквы (${others.join(', ')}) считаем постоянными — это частная производная.`, `We differentiate with respect to ${v}. The other letters (${others.join(', ')}) are treated as constants: this is a partial derivative.`)
                    : T_(`Ищем производную по ${v}: разбираем выражение от внешней операции к внутренним.`, `We differentiate with respect to ${v}, going from the outermost operation inwards.`),
                rule: 'start',
            }));
            if (r.step) steps.push(r.step);
        }
        if (opts.simplify !== false) {
            // the independent canonical derivative sometimes tidies up better than the rule tree
            const alt = niceForm(fast, v);
            if (score(alt) + penalty(alt) < score(result) + penalty(result) && agree(alt, result, v, { tol: 1e-8 }).ok !== false) {
                if (wantSteps) {
                    const from = result;
                    steps.push(step({
                        title: T_('Упрощаем', 'Simplify'),
                        tex: bt((L) => `${calcTex(from, L)} = ${calcTex(alt, L)}`),
                        text: T_('Раскрываем скобки, приводим к общему знаменателю и собираем подобные.', 'Expand, bring to a common denominator and collect like terms.'),
                        rule: 'simplify',
                    }));
                }
                result = alt;
            }
        }
    } else {
        result = niceForm(fast, v);
    }
    let verified = true;
    if (agree(result, fast, v, { tol: 1e-8 }).ok === false) {
        // never show a result that disagrees with the independent computation
        result = niceForm(fast, v);
        verified = agree(result, fast, v, { tol: 1e-8 }).ok !== false;
    }
    if (numericCheck(node, result, v) === false) verified = false;
    const tex = bt((L) => `${primeTex(v, 1, partial)} = ${calcTex(result, L)}`);
    if (wantSteps) steps.push(answerStep(T_('Ответ', 'Answer'), tex));
    return { result, steps, verified, tex };
}

/** Partial derivative ∂f/∂v (the other letters are constants): derivative() with ∂ notation. */
export function partialDerivative(node, v = 'x', opts = {}) {
    return derivative(node, v, { ...opts, partial: true });
}

/**
 * n-th derivative (1 ≤ n ≤ 30). → {result, list: [f', f'', …], steps, verified, tex}. Each order
 * differentiates the previous answer as written; with opts.steps every order is a step holding its rule tree.
 */
export function derivativeN(node, v = 'x', n = 2, opts = {}) {
    node = asNode(node);
    checkExpr(node);
    if (!Number.isInteger(n) || n < 1 || n > 30) throw new MathError({ ru: 'Порядок производной — целое число от 1 до 30', en: 'The order must be a whole number from 1 to 30' }, null, null, 'range');
    let cur = node;
    const list = [];
    const steps = [];
    let verified = true;
    for (let k = 1; k <= n; k++) {
        const r = derivative(cur, v, { steps: !!opts.steps });
        verified = verified && r.verified;
        list.push(r.result);
        if (opts.steps) {
            const prevTex = k === 1 ? null : primeTex(v, k - 1);
            const src = cur;
            steps.push(step({
                title: T_(`Производная ${k}-го порядка`, `Derivative of order ${k}`),
                tex: bt((L) => `${primeTex(v, k)} = \\left(${prevTex ?? calcTex(src, L)}\\right)' = ${calcTex(r.result, L)}`),
                text: k === 1 ? undefined : T_('Дифференцируем предыдущую производную.', 'Differentiate the previous derivative.'),
                rule: 'order',
                sub: r.steps.filter((s) => s.rule !== 'start' && s.rule !== 'answer'),
            }));
        }
        cur = r.result;
        if (isZero(r.result)) {
            for (let j = k + 1; j <= n; j++) list.push(N0);
            break;
        }
    }
    const result = list[n - 1];
    const tex = bt((L) => `${primeTex(v, n)} = ${calcTex(result, L)}`);
    if (opts.steps) steps.push(answerStep(T_('Ответ', 'Answer'), tex));
    return { result, list, steps, verified, tex };
}

/** ∇f → {result: list node of the partials, components: {x: node, …}, vars, steps, tex}. vars default: freeVars. */
export function gradientOf(node, vars = null, opts = {}) {
    node = asNode(node);
    checkExpr(node);
    const vs = vars ?? freeVars(node);
    if (!vs.length) throw new MathError({ ru: 'В выражении нет переменных', en: 'The expression has no variables' }, null, null, 'no-var');
    const components = {};
    const steps = [];
    for (const w of vs) {
        const r = partialDerivative(node, w, { steps: !!opts.steps });
        components[w] = r.result;
        if (opts.steps) {
            steps.push(step({
                title: T_(`Частная производная по ${w}`, `Partial derivative with respect to ${w}`),
                tex: r.tex,
                text: T_(`Дифференцируем по ${w}, остальные переменные считаем постоянными.`, `Differentiate with respect to ${w}, keeping the other variables constant.`),
                rule: 'partial',
                sub: r.steps.filter((s) => s.rule !== 'start' && s.rule !== 'answer'),
            }));
        }
    }
    const result = Object.freeze({ type: 'list', items: Object.freeze(vs.map((w) => components[w])) });
    const tex = bt((L) => {
        const sep = L === 'ru' ? ';\\ ' : ',\\ ';
        return `\\nabla f = \\left(${vs.map((w) => primeTex(w, 1, true)).join(sep)}\\right) = \\left(${vs.map((w) => calcTex(components[w], L)).join(sep)}\\right)`;
    });
    if (opts.steps) steps.push(answerStep(T_('Градиент', 'Gradient'), tex));
    return { result, components, vars: vs, steps, tex };
}

/**
 * Tangent to y = f(v) at v = a (number, string or node): {k, b (nodes), point: {x, y}, line (node), tex, steps}.
 * Throws MathError 'undefined' when f(a) is not defined and 'no-derivative' when f'(a) is not finite.
 */
export function tangentLine(node, v = 'x', a = 0, opts = {}) {
    node = asNode(node);
    checkExpr(node);
    const A = typeof a === 'string' ? parse(a) : toNode(a);
    const noF = () => new MathError({ ru: 'Функция не определена в этой точке', en: 'The function is not defined at this point' }, null, null, 'undefined');
    let fa;
    try {
        fa = simplify(substitute(node, { [v]: A }));
    } catch {
        throw noF();
    }
    const others = freeVars(node).filter((w) => w !== v);
    const env = Object.fromEntries(others.map((w) => [w, 1.3]));
    if (!Number.isFinite(evaluate(fa, env))) throw noF();
    const d = derivative(node, v, { steps: !!opts.steps });
    let k = null;
    try {
        k = simplify(substitute(quickDerivative(node, v), { [v]: A }));
    } catch {
        k = null;
    }
    if (!k || !Number.isFinite(evaluate(k, env))) {
        throw new MathError({ ru: 'В этой точке у функции нет конечной производной: касательная вертикальна или её нет', en: 'The function has no finite derivative here: the tangent is vertical or does not exist' }, null, null, 'no-derivative');
    }
    const C = canonContext();
    const X = sym(v);
    const b = C.add([fa, C.mul([NM1, k, A])]);
    const line = niceForm(C.add([C.mul([k, X]), b]), v);
    const tex = bt((L) => `y = ${calcTex(line, L)}`);
    const steps = [];
    if (opts.steps) {
        const at = (L) => calcTex(A, L);
        steps.push(step({
            title: T_('Уравнение касательной', 'Equation of the tangent'),
            tex: bt((L) => `y = f(${at(L)}) + f'(${at(L)})\\,${isZero(A) ? v : `(${v} ${negLeading(A) ? '+ ' + calcTex(simplify(neg(A)), L) : '- ' + at(L)})`}`),
            text: T_('Касательная проходит через точку графика, а её наклон равен производной в этой точке.', 'The tangent passes through the point of the graph, and its slope equals the derivative at that point.'),
            rule: 'tangent-formula',
        }));
        steps.push(step({ title: T_('Значение функции', 'Value of the function'), tex: bt((L) => `f(${at(L)}) = ${calcTex(fa, L)}`), rule: 'value' }));
        steps.push(step({ title: T_('Производная', 'Derivative'), tex: d.tex, rule: 'derivative', sub: d.steps.filter((s) => s.rule !== 'start' && s.rule !== 'answer') }));
        steps.push(step({
            title: T_('Угловой коэффициент', 'Slope'),
            tex: bt((L) => `k = f'(${at(L)}) = ${calcTex(k, L)}`),
            text: T_('Подставляем точку в производную: это тангенс угла наклона касательной.', 'Substitute the point into the derivative: this is the slope of the tangent.'),
            rule: 'slope',
        }));
        steps.push(answerStep(T_('Касательная', 'Tangent line'), tex));
    }
    return { k, b, point: { x: A, y: fa }, line, tex, steps };
}
