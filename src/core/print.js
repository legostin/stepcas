// print — AST → TeX (for KaTeX) and → plain text (that parse() reads back).
//
// TeX conventions:
//   * minimal brackets by precedence; a + (−b) prints as a − b, a + (−2)b as a − 2b
//   * implicit multiplication where it reads unambiguously (2x, 2\sqrt{3}, x(x+1), 3\sin x);
//     \cdot before a factor that starts with a digit or a fraction, after a function written without
//     brackets (\sin x \cdot y), between numbers; negative factors are bracketed
//   * canonical products with negative powers become one \frac; a rational coefficient goes into the
//     fraction (\frac{3x}{4}, \frac{\sqrt{2}}{2}) when the rest is "simple" (letters, powers, radicals),
//     otherwise it stays in front (\frac{3}{4}(x+1), \frac{1}{2}\sin x) and takes only the leading constants
//     along (\frac{\sqrt{3}}{3}\operatorname{arctg} x, \frac{\pi}{4}\sin x)
//   * x^{1/2} → \sqrt{x}, x^{1/n} → \sqrt[n]{x}, x^{-1} → \frac{1}{x}, x^{-1/2} → \frac{1}{\sqrt{x}};
//     {roots: true}: x^{3/2} → x\sqrt{x}, x^{2/3} → \sqrt[3]{x^{2}}, (x+1)^{3/2} → \sqrt{(x + 1)^{3}}
//   * RU: tg, ctg, arctg, arcctg, sh, ch, th, lg, decimal comma 2{,}5, list separator ";";
//     EN: tan, cot, arctan, sinh, log_{10}, 2.5, ","
//   * function arguments without brackets only for a letter or a plain number: \sin x, \ln 2, \sin(2x)

import { Q } from './rational.js';
import { mul, num, pow, isConst, freeVars, nodeSome } from './ast.js';
import { notation, resolveLanguage, DEFAULT_LANGUAGE, MACHINE } from '../i18n/index.js';

// TeX of the functions: the neutral defaults; a language overrides some in its notation (tg for tan in Russian)
const FN_TEX = {
    sin: '\\sin',
    cos: '\\cos',
    tan: '\\tan',
    cot: '\\cot',
    sec: '\\sec',
    csc: '\\csc',
    asin: '\\arcsin',
    acos: '\\arccos',
    atan: '\\arctan',
    acot: '\\operatorname{arccot}',
    sinh: '\\sinh',
    cosh: '\\cosh',
    tanh: '\\tanh',
    coth: '\\coth',
    asinh: '\\operatorname{arsinh}',
    acosh: '\\operatorname{arcosh}',
    atanh: '\\operatorname{artanh}',
    ln: '\\ln',
    lg: '\\log_{10}',
    exp: '\\exp',
    sign: '\\operatorname{sgn}',
};


const GREEK = new Set(['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa', 'lambda', 'mu', 'nu', 'xi',
    'rho', 'sigma', 'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega', 'Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Phi', 'Psi', 'Omega']);
const GREEK_TEX = { epsilon: '\\varepsilon', phi: '\\varphi' };

const REL_TEX = { '=': '=', '<': '<', '>': '>', '<=': '\\le', '>=': '\\ge', '!=': '\\ne' };
const REL_TEXT = { '=': '=', '<': '<', '>': '>', '<=': '<=', '>=': '>=', '!=': '!=' };

// ---------------------------------------------------------------- shared helpers

const isPlainNum = (n) => n.type === 'num' && !n.raw;

/** Does the printed form start with a minus sign? */
function leadsMinus(n) {
    switch (n.type) {
        case 'num':
            return n.value.isNeg();
        case 'neg':
            return true;
        case 'mul':
            return n.args.length > 0 && leadsMinus(n.args[0]);
        case 'add':
            return leadsMinus(n.args[0]);
        default:
            return false;
    }
}

/** Precedence of the printed form (higher binds tighter). */
function prec(n) {
    switch (n.type) {
        case 'list':
            return 0;
        case 'rel':
        case 'chain':
            return 1;
        case 'add':
        case 'neg':
            return 2;
        case 'mul':
            return leadsMinus(n) ? 2 : 3;
        case 'div':
            return 3;
        case 'pow':
            if (isPlainNum(n.exp) && n.exp.value.isNeg()) return 3;
            if (isPlainNum(n.exp) && n.exp.value.n === 1n && !n.exp.value.isInt()) return 6;
            return 4;
        case 'fn':
            return 5;
        case 'num':
            if (n.value.isNeg()) return 2;
            if (!n.value.isInt() && !n.raw) return 3;
            return 6;
        default:
            return 6;
    }
}

/** Split a term into sign and absolute part for printing sums: a + (−2x) → a − 2x. */
function splitSign(t, strict = false) {
    if (t.type === 'num' && t.value.isNeg()) return { neg: true, abs: t.raw ? { ...t, value: t.value.neg(), raw: t.raw.replace(/^-/, '') } : num(t.value.neg()) };
    if (t.type === 'neg') return { neg: true, abs: t.arg };
    if (t.type === 'mul' && t.args.length) {
        const f = t.args[0];
        if (f.type === 'num' && f.value.isNeg() && !f.raw) {
            const a = f.value.neg();
            const rest = t.args.slice(1);
            return { neg: true, abs: a.isOne() && rest.length ? mul(rest) : mul([num(a), ...rest]) };
        }
        if (f.type === 'neg' && !strict) return { neg: true, abs: mul([f.arg, ...t.args.slice(1)]) };
    }
    return { neg: false, abs: t };
}

/** Split a canonical product into sign, rational coefficient, numerator and denominator factors. */
function splitProduct(n) {
    let sign = false;
    let coef = Q.ONE;
    let rest = n.args;
    const first = rest[0];
    if (first && isPlainNum(first) && !first.value.isOne()) {
        coef = first.value;
        rest = rest.slice(1);
        if (coef.isNeg()) {
            sign = true;
            coef = coef.neg();
        }
    } else if (first && first.type === 'neg') {
        sign = true;
        rest = [first.arg, ...rest.slice(1)];
    }
    const top = [];
    const bottom = [];
    for (const f of rest) {
        if (f.type === 'pow' && isPlainNum(f.exp) && f.exp.value.isNeg()) {
            const e = f.exp.value.neg();
            bottom.push(e.isOne() ? f.base : pow(f.base, num(e)));
        } else top.push(f);
    }
    return { sign, coef, top, bottom };
}

// "Simple" numerators go into the fraction together with the coefficient: \frac{3x^2}{4}, \frac{\sqrt{2}}{2}.
function simpleFactor(f) {
    if (f.type === 'sym') return !isConst(f) || f.name !== 'i';
    if (f.type === 'pow') return (f.base.type === 'sym' || (isPlainNum(f.base) && f.base.value.isPos())) && isPlainNum(f.exp);
    return false;
}

// A positive constant factor that reads well on top of a fraction: √3, ∛4, π, e, √(2π), √e.
function constFactor(f) {
    if (f.type === 'sym') return !f.var && (f.name === 'pi' || f.name === 'e');
    if (f.type !== 'pow' || !isPlainNum(f.exp) || !f.exp.value.isPos()) return false;
    const atom = (b) => (isPlainNum(b) && b.value.isPos()) || (b.type === 'sym' && !b.var && (b.name === 'pi' || b.name === 'e'));
    return atom(f.base) || (f.base.type === 'mul' && f.base.args.every(atom));
}

function lastIsCommand(s) {
    return /\\[a-zA-Z]+$/.test(s);
}

// ---------------------------------------------------------------- TeX

function texParen(s) {
    return /\\frac|\\dfrac/.test(s) ? `\\left(${s}\\right)` : `(${s})`;
}

function texNum(n, o) {
    const q = n.value;
    if (n.raw) {
        // a decimal as typed (or an approximate value built with a raw string; those may carry a minus)
        const m = /^(-?)(\d*)[.,](\d*)(?:\((\d+)\))?$/.exec(n.raw);
        if (m && (m[1] === '-') === q.isNeg()) {
            const sep = o.n.decimalTex;
            return `${m[1]}${m[2] || '0'}${sep}${m[3]}${m[4] ? `(${m[4]})` : ''}`;
        }
    }
    if (o.decimals && !q.isInt() && q.isFiniteDecimal()) {
        return q.toDecimalString(40, MACHINE).replace('.', o.n.decimalTex);
    }
    return q.toTex(o.lang);
}

// A symbol built directly from a Unicode letter (sym('λ')) prints like the parsed name (sym('lambda')).
const UNICODE_GREEK = { α: 'alpha', β: 'beta', γ: 'gamma', δ: 'delta', ε: 'varepsilon', ζ: 'zeta', η: 'eta', θ: 'theta', ι: 'iota', κ: 'kappa',
    λ: 'lambda', μ: 'mu', ν: 'nu', ξ: 'xi', π: 'pi', ρ: 'rho', σ: 'sigma', τ: 'tau', φ: 'varphi', χ: 'chi', ψ: 'psi', ω: 'omega',
    Γ: 'Gamma', Δ: 'Delta', Θ: 'Theta', Λ: 'Lambda', Σ: 'Sigma', Φ: 'Phi', Ψ: 'Psi', Ω: 'Omega' };

function texSym(n) {
    if (!n.var) {
        if (n.name === 'pi') return '\\pi';
        if (n.name === 'inf') return '\\infty';
    }
    const u = n.name.indexOf('_');
    const head = u > 0 ? n.name.slice(0, u) : n.name;
    const sub = u > 0 ? n.name.slice(u + 1) : null;
    let h;
    const uni = UNICODE_GREEK[head];
    if (uni) h = `\\${uni}`;
    else if (GREEK.has(head)) h = GREEK_TEX[head] ?? `\\${head}`;
    else if (head === 'pi') h = '\\pi';
    else if (head.length === 1) h = head;
    else h = `\\mathrm{${head}}`;
    return sub === null ? h : `${h}_{${sub}}`;
}

// Can a function argument go without brackets? (|x| brings its own delimiters: \ln|x|)
function bareArg(a) {
    return a.type === 'sym' || (a.type === 'num' && !a.value.isNeg() && (a.value.isInt() || a.raw)) || delimited(a);
}

function delimited(a) {
    return a.type === 'fn' && (a.name === 'abs' || a.name === 'floor' || a.name === 'ceil');
}

// Function printed as "\sin x" (no brackets), after which a following factor needs \cdot.
function isBareFn(n) {
    if (n.type === 'pow' && n.base.type === 'fn' && powerable(n.base) && isPlainNum(n.exp) && n.exp.value.isInt() && n.exp.value.isPos()) n = n.base;
    if (n.type !== 'fn') return false;
    if (!FN_TEX[n.name] && n.name !== 'log') return false;
    const a = n.args[n.args.length - 1];
    return bareArg(a) && !delimited(a);
}

function powerable(f) {
    return !!FN_TEX[f.name] || f.name === 'log';
}

function texFn(n, o, power = null) {
    const t = (x) => tex(x, o);
    const a = n.args;
    switch (n.name) {
        case 'sqrt':
            return `\\sqrt{${t(a[0])}}`;
        case 'root':
            return `\\sqrt[${t(a[1])}]{${t(a[0])}}`;
        case 'abs':
            return `\\left|${t(a[0])}\\right|`;
        case 'floor':
            return `\\left\\lfloor ${t(a[0])}\\right\\rfloor`;
        case 'ceil':
            return `\\left\\lceil ${t(a[0])}\\right\\rceil`;
        case 'fact': {
            const x = a[0];
            const s = t(x);
            return (x.type === 'sym' || (isPlainNum(x) && x.value.isInt() && !x.value.isNeg()) ? s : texParen(s)) + '!';
        }
        default:
            break;
    }
    let head;
    let arg;
    if (n.name === 'log') {
        const b = a[0];
        arg = a[1];
        if (isPlainNum(b) && b.value.eq(10)) head = o.n.log10Tex;
        else if (isConst(b) && b.name === 'e') head = '\\ln';
        else head = `\\log_{${t(b)}}`;
    } else {
        head = o.n.fnTex?.[n.name] ?? FN_TEX[n.name];
        arg = a[0];
    }
    if (power !== null) head += `^{${power}}`;
    const s = t(arg);
    if (delimited(arg)) return head + s;
    return bareArg(arg) ? `${head} ${s}` : head + texParen(s);
}

function texFactor(f, o, first) {
    const s = tex(f, o);
    if (f.type === 'add' || f.type === 'rel' || f.type === 'chain' || f.type === 'list' || f.type === 'mul') return texParen(s);
    if (!first && leadsMinus(f)) return texParen(s);
    if (f.type === 'neg') return first ? s : texParen(s);
    return s;
}

function texProduct(factors, o) {
    let out = '';
    let prev = null;
    for (let k = 0; k < factors.length; k++) {
        const f = factors[k];
        const s = texFactor(f, o, k === 0);
        if (prev === null) out = s;
        else {
            let dot = o.mulDot;
            if (!dot) {
                if (/^[\d.]/.test(s)) dot = true;
                else if (/^\\[dt]?frac/.test(s)) dot = true;
                else if (/^\\left\(-|^\(-/.test(s)) dot = true;
                else if (isBareFn(prev.node) && !(f.type === 'fn' && FN_TEX[f.name]) && !(f.type === 'pow' && f.base.type === 'fn' && FN_TEX[f.base.name])) dot = true;
                else if (prev.node.type === 'fn' && prev.node.name === 'fact' && /^[a-zA-Z(]/.test(s)) dot = true;
            }
            if (dot) out += ' \\cdot ' + s;
            else out += (lastIsCommand(out) && /^[a-zA-Z]/.test(s) ? ' ' : '') + s;
        }
        prev = { node: f, s };
    }
    return out;
}

function texMul(n, o) {
    const { sign, coef, top, bottom } = splitProduct(n);
    let s;
    const cNum = coef.n;
    const cDen = coef.d;
    if (bottom.length || cDen !== 1n) {
        if (!bottom.length && top.length && !top.every(simpleFactor)) {
            // a fraction coefficient followed by the factors: \frac{3}{4}(x+1), \frac{1}{2}\sin x;
            // leading constants (radicals, π) go on top: \frac{\sqrt{3}}{3}\operatorname{arctg} x, \frac{\pi}{4}\sin x
            let k = 0;
            while (k < top.length - 1 && constFactor(top[k])) k++;
            const upper = cNum !== 1n || !k ? [num(cNum), ...top.slice(0, k)] : top.slice(0, k);
            const head = upper.length === 1 ? tex(upper[0], o) : texProduct(upper, o);
            const rest = texProduct(top.slice(k), o);
            // a number after the fraction needs a dot: \frac{1}{2} \cdot \frac{1}{2}
            s = `\\frac{${head}}{${cDen}}` + (/^[\d.]|^\\[dt]?frac|^\\left\(-|^\(-/.test(rest) ? ' \\cdot ' : '') + rest;
        } else {
            const upper = cNum !== 1n || !top.length ? [num(cNum), ...top] : top;
            const lower = cDen !== 1n ? [num(cDen), ...bottom] : bottom;
            const part = (fs) => (fs.length === 1 ? tex(fs[0], o) : texProduct(fs, o));
            s = `\\frac{${part(upper)}}{${part(lower)}}`;
        }
    } else {
        const fs = !coef.isOne() || !top.length ? [num(coef), ...top] : top;
        s = texProduct(fs, o);
    }
    return (sign ? '-' : '') + s;
}

// x^{p/q} with p > q or p > 1 as roots (opts.roots): x^{3/2} → x\sqrt{x}, x^{7/3} → x^{2}\sqrt[3]{x},
// x^{2/3} → \sqrt[3]{x^{2}}; a base that is not a letter or a number stays whole: \sqrt{(x + 1)^{3}}.
function texRootPow(base, e, o) {
    const p = e.n;
    const q = e.d;
    const root = (s) => (q === 2n ? `\\sqrt{${s}}` : `\\sqrt[${q}]{${s}}`);
    if (base.type === 'sym' || (isPlainNum(base) && base.value.isInt() && base.value.isPos())) {
        const k = p / q;
        const r = p % q;
        const inner = tex(r === 1n ? base : pow(base, num(r)), o);
        if (k === 0n) return root(inner);
        return tex(k === 1n ? base : pow(base, num(k)), o) + root(inner);
    }
    return root(tex(pow(base, num(p)), o));
}

function texPow(n, o) {
    const { base, exp } = n;
    if (isPlainNum(exp)) {
        const e = exp.value;
        if (e.isNeg()) {
            const pe = e.neg();
            return `\\frac{1}{${tex(pe.isOne() ? base : pow(base, num(pe)), o)}}`;
        }
        if (e.n === 1n && e.d === 2n) return `\\sqrt{${tex(base, o)}}`;
        if (e.n === 1n && e.d > 1n) return `\\sqrt[${e.d}]{${tex(base, o)}}`;
        if (o.roots && !e.isInt()) return texRootPow(base, e, o);
        if (base.type === 'fn' && powerable(base) && e.isInt()) return texFn(base, o, e.toString());
    }
    let b = tex(base, o);
    let paren = true;
    if (base.type === 'sym') paren = false;
    else if (isPlainNum(base) && base.value.isInt() && !base.value.isNeg()) paren = false;
    else if (base.type === 'fn' && (base.name === 'abs' || base.name === 'floor' || base.name === 'ceil')) paren = false;
    if (paren) b = texParen(b);
    return `${b}^{${tex(exp, o)}}`;
}

// A sum of numbers (no variables) reads better starting with a positive term: ln 3 − ln 2, √2 − 1.
// Sums with variables keep their order (polynomials go by descending degree: −x² + 3x).
// Display only (toTex): toText must round-trip structurally.
// Only simplify output is reordered: a sum with parser shapes or unfolded numbers in it (−2² + 4·2 − 4 after
// substituting x = 2 into −x² + 4x − 4) is a substitution and keeps the term order of the original expression.
const DISPLAY_FN = new Set(['sqrt', 'root', 'cbrt', 'exp']);
function notSimplified(t) {
    return nodeSome(t, (x) => x.type === 'neg' || x.type === 'div' || (x.type === 'num' && !!x.raw)
        || (x.type === 'fn' && DISPLAY_FN.has(x.name))
        || (x.type === 'mul' && x.args.filter((a) => a.type === 'num').length > 1)
        || (x.type === 'pow' && x.base.type === 'num' && x.exp.type === 'num' && x.exp.value.isInt()));
}
function displayOrder(args) {
    // Left alone: complex numbers (−3 + 2i is the canonical form), sums that start with a plain
    // number, and sums that are not simplify output — those come from substituting a value and
    // should mirror the original expression.
    if (args.length < 2 || !splitSign(args[0]).neg || isPlainNum(splitSign(args[0]).abs)) return args;
    const k = args.findIndex((t) => !splitSign(t).neg);
    if (k < 0 || args.some((t) => freeVars(t).length || nodeSome(t, (x) => x.type === 'sym' && x.name === 'i'))) return args;
    if (args.some(notSimplified)) return args;
    return [args[k], ...args.slice(0, k), ...args.slice(k + 1)];
}

function texAdd(n, o) {
    let out = '';
    displayOrder(n.args).forEach((t, k) => {
        const { neg, abs } = splitSign(t);
        let s = tex(abs, o);
        if (prec(abs) <= 2) s = texParen(s);
        if (k === 0) out = (neg ? '-' : '') + s;
        else out += (neg ? ' - ' : ' + ') + s;
    });
    return out;
}

function tex(n, o) {
    switch (n.type) {
        case 'num':
            return texNum(n, o);
        case 'sym':
            return texSym(n);
        case 'add':
            return texAdd(n, o);
        case 'mul':
            return texMul(n, o);
        case 'div':
            return `\\frac{${tex(n.num, o)}}{${tex(n.den, o)}}`;
        case 'neg': {
            const s = tex(n.arg, o);
            return '-' + (prec(n.arg) <= 2 ? texParen(s) : s);
        }
        case 'pow':
            return texPow(n, o);
        case 'fn':
            return texFn(n, o);
        case 'rel':
            return `${tex(n.lhs, o)} ${REL_TEX[n.op]} ${tex(n.rhs, o)}`;
        case 'chain':
            return n.items.map((x, k) => (k ? ` ${REL_TEX[n.ops[k - 1]]} ` : '') + tex(x, o)).join('');
        case 'list':
            return n.items.map((x) => tex(x, o)).join(o.n.listTex);
        default:
            throw new TypeError(`toTex: unknown node ${n?.type}`);
    }
}

/**
 * TeX for KaTeX. opts: {lang: 'ru'|'en' (default 'ru'), mulDot: false — \cdot between all factors,
 * decimals: false — print finite-decimal rationals as decimals (2{,}5) instead of \frac,
 * roots: false — fractional powers as roots, the textbook way: x^{3/2} → x\sqrt{x}, x^{2/3} → \sqrt[3]{x^{2}},
 * (x + 1)^{3/2} → \sqrt{(x + 1)^{3}}, x^{-3/2} → \frac{1}{x\sqrt{x}}}.
 */
export function toTex(node, opts = {}) {
    const lang = resolveLanguage(opts.lang);
    const o = { lang, n: notation(lang), mulDot: !!opts.mulDot, decimals: !!opts.decimals, roots: !!opts.roots };
    return tex(node, o);
}

// ---------------------------------------------------------------- plain text

function textNum(n, o) {
    const q = n.value;
    if (n.raw) {
        const m = /^(-?)(\d*)[.,](\d*)(?:\((\d+)\))?$/.exec(n.raw);
        if (m && (m[1] === '-') === q.isNeg()) return `${m[1]}${m[2] || '0'}${o.n.decimalText}${m[3]}${m[4] ? `(${m[4]})` : ''}`;
    }
    return q.toString();
}

function textSym(n) {
    const u = n.name.indexOf('_');
    if (u > 0) {
        const sub = n.name.slice(u + 1);
        return /^\d+$|^[A-Za-z]$/.test(sub) ? n.name : `${n.name.slice(0, u)}_{${sub}}`;
    }
    return n.name;
}

function textFactor(f, o, first) {
    const s = text(f, o);
    if (f.type === 'add' || f.type === 'rel' || f.type === 'chain' || f.type === 'list' || f.type === 'mul' || f.type === 'div' || f.type === 'neg') return `(${s})`;
    if (f.type === 'num' && !f.value.isInt() && !f.raw) return `(${s})`;
    if (f.type === 'pow' && isPlainNum(f.exp) && f.exp.value.isNeg()) return `(${s})`;
    if (!first && leadsMinus(f)) return `(${s})`;
    return s;
}

function textProduct(factors, o) {
    let out = '';
    factors.forEach((f, k) => {
        const s = textFactor(f, o, k === 0);
        if (k === 0) out = s;
        else {
            const prev = factors[k - 1];
            const implicit = prev.type === 'num' && !prev.value.isNeg() && prev.value.isInt() && /^[a-zA-Z(]/.test(s);
            out += implicit ? s : '*' + s;
        }
    });
    return out;
}

function textMul(n, o) {
    if (n.args[0].type === 'neg') return textProduct(n.args, o);
    const { sign, coef, top, bottom } = splitProduct(n);
    let s;
    if (bottom.length || coef.d !== 1n) {
        const upper = coef.n !== 1n || !top.length ? [num(coef.n), ...top] : top;
        const lower = coef.d !== 1n ? [num(coef.d), ...bottom] : bottom;
        // a single factor is printed bare and bracketed here once (textFactor would bracket it too)
        let u = upper.length === 1 ? text(upper[0], o) : textProduct(upper, o);
        if (upper.length === 1 && (prec(upper[0]) <= 2 || leadsMinus(upper[0]))) u = `(${u})`;
        let l = lower.length === 1 ? text(lower[0], o) : textProduct(lower, o);
        if (lower.length > 1 || prec(lower[0]) < 4 || lower[0].type === 'pow' || leadsMinus(lower[0])) l = `(${l})`;
        s = `${u}/${l}`;
    } else {
        s = textProduct(!coef.isOne() || !top.length ? [num(coef), ...top] : top, o);
    }
    return (sign ? '-' : '') + s;
}

function textFnName(name, o) {
    return o.n.fnText?.[name] ?? name;
}

function textFn(n, o) {
    const t = (x) => text(x, o);
    const a = n.args;
    switch (n.name) {
        case 'fact': {
            const x = a[0];
            const s = t(x);
            return (x.type === 'sym' || (isPlainNum(x) && x.value.isInt() && !x.value.isNeg()) ? s : `(${s})`) + '!';
        }
        case 'root':
            return `root(${t(a[0])}; ${t(a[1])})`;
        case 'log': {
            const b = a[0];
            const bs = b.type === 'sym' || (isPlainNum(b) && b.value.isInt() && !b.value.isNeg()) ? t(b) : `(${t(b)})`;
            return `log_${bs}(${t(a[1])})`;
        }
        default:
            return `${textFnName(n.name, o)}(${t(a[0])})`;
    }
}

function textPow(n, o) {
    const { base, exp } = n;
    if (isPlainNum(exp)) {
        const e = exp.value;
        if (e.isNeg()) {
            const pe = e.neg();
            const inner = pe.isOne() ? base : pow(base, num(pe));
            let s = text(inner, o);
            if (prec(inner) < 4) s = `(${s})`;
            return `1/${s}`;
        }
        if (e.n === 1n && e.d === 2n) return `sqrt(${text(base, o)})`;
    }
    let b = text(base, o);
    const atomic = base.type === 'sym' || (isPlainNum(base) && base.value.isInt() && !base.value.isNeg()) || (base.type === 'fn' && base.name !== 'fact');
    if (!atomic) b = `(${b})`;
    let e = text(exp, o);
    const eAtomic = exp.type === 'sym' || (isPlainNum(exp) && exp.value.isInt() && !exp.value.isNeg());
    if (!eAtomic) e = `(${e})`;
    return `${b}^${e}`;
}

function text(n, o) {
    switch (n.type) {
        case 'num':
            return textNum(n, o);
        case 'sym':
            return textSym(n);
        case 'add': {
            let out = '';
            n.args.forEach((t, k) => {
                const { neg, abs } = splitSign(t, true);
                let s = text(abs, o);
                if (prec(abs) <= 2) s = `(${s})`;
                if (k === 0) out = (neg ? '-' : '') + s;
                else out += (neg ? ' - ' : ' + ') + s;
            });
            return out;
        }
        case 'mul':
            return textMul(n, o);
        case 'div': {
            let a = text(n.num, o);
            if (prec(n.num) <= 2) a = `(${a})`;
            let b = text(n.den, o);
            if (prec(n.den) <= 3 || (n.den.type === 'pow' && isPlainNum(n.den.exp) && n.den.exp.value.isNeg())) b = `(${b})`;
            return `${a}/${b}`;
        }
        case 'neg': {
            const s = text(n.arg, o);
            return '-' + (prec(n.arg) <= 2 ? `(${s})` : s);
        }
        case 'pow':
            return textPow(n, o);
        case 'fn':
            return textFn(n, o);
        case 'rel':
            return `${text(n.lhs, o)} ${REL_TEXT[n.op]} ${text(n.rhs, o)}`;
        case 'chain':
            return n.items.map((x, k) => (k ? ` ${REL_TEXT[n.ops[k - 1]]} ` : '') + text(x, o)).join('');
        case 'list':
            return n.items.map((x) => text(x, o)).join(o.n.listText);
        default:
            throw new TypeError(`toText: unknown node ${n?.type}`);
    }
}

/** The language-neutral plain text of a node — ASCII names, a decimal point, ", " between items — for machines. */
export function plainText(node) {
    return toText(node, { lang: MACHINE });
}

/**
 * Plain text that parse() reads back (x^2 - 5x + 6, sqrt(x), log_2(x), root(x; 3), 3x/4).
 * RU uses a decimal comma and "; " between list items, EN a point and ", ".
 */
export function toText(node, opts = {}) {
    const lang = resolveLanguage(opts.lang);
    return text(node, { lang, n: notation(lang) });
}

// ---------------------------------------------------------------- numbers for widgets

function groupDigits(int) {
    if (int.length <= 4) return int;
    return int.replace(/\B(?=(\d{3})+(?!\d))/g, '\\,');
}

/**
 * TeX for a number: Q prints exactly (\frac{3}{4}, or a decimal when {decimal: true} and it is finite);
 * a JS number is rounded to `digits` fractional digits (default 6, trailing zeros dropped), very large or
 * tiny values in scientific form. RU uses a decimal comma {,}. opts: {digits, group (thin-space thousands),
 * decimal}.
 */
export function texNumber(value, lang = DEFAULT_LANGUAGE, opts = {}) {
    const digits = opts.digits ?? 6;
    const comma = notation(lang).decimalTex;
    const fix = (s) => {
        const parts = s.split('.');
    let i = parts[0];
    const f = parts[1];
        const neg = i.startsWith('-');
        if (neg) i = i.slice(1);
        if (opts.group) i = groupDigits(i);
        return (neg ? '-' : '') + i + (f ? comma + f : '');
    };
    if (value instanceof Q) {
        if (value.isInt()) return fix(value.toString());
        if (opts.decimal) return fix(value.toDecimalString(digits, MACHINE));
        return value.toTex(lang);
    }
    if (typeof value === 'bigint') return fix(value.toString());
    const x = Number(value);
    if (Number.isNaN(x)) return '\\text{—}';
    if (x === Infinity) return '\\infty';
    if (x === -Infinity) return '-\\infty';
    const ax = Math.abs(x);
    if (ax !== 0 && (ax >= 1e15 || ax < 10 ** -Math.max(digits, 1))) {
        const [m, e] = x.toExponential(Math.max(digits - 1, 0)).split('e');
        const mant = m.replace(/\.?0+$/, '');
        return `${fix(mant)} \\cdot 10^{${Number(e)}}`;
    }
    let s = x.toFixed(digits);
    if (s.includes('.')) s = s.replace(/\.?0+$/, '');
    if (s === '-0') s = '0';
    return fix(s);
}
