// core/parse — what people actually type → AST (ast.js). Errors are MathError with a message, pos, len.
//
// Conventions (see README.md for the full list):
//   * implicit multiplication binds like * and /, left to right: 1/2x = (1/2)·x, 6/2(1+2) = 9
//   * unary minus covers the whole product/power after it: -x^2 = -(x^2), -2^2 = -4, -2x = -(2x)
//   * ^ is right-associative: 2^3^2 = 2^9; the exponent takes one factor: e^2x = e^2·x
//   * a function without brackets takes one implicit product: sin 2x = sin(2x), sin x cos x = sin x · cos x,
//     sin x/2 = (sin x)/2; sin^2 x = (sin x)^2; sin^-1 x = arcsin x
//   * log x and log(x) mean log base 10 (like lg); log_2 x, log_{10}(x), log2(x), log(b, x) have a base
//   * "3,5" (comma between digits, no space) is a decimal comma; "3, 5" and "3;5" separate list items;
//     inside root(...)/log(...) a comma separates arguments unless the call also uses ";"
//   * there is no scientific notation in expressions: 2e3 is 2·e·3
//   * xy is x·y: letter runs split into known names (sin, pi, alpha, …) and single letters
//   * newline and ";" separate list items; ":" is division; % is /100; ° is ·π/180
//   * one ± (∓, \pm, +/-) in a list item makes it two items, the sign read in place: 1 ± √2 → 1 + √2; 1 − √2
//   * parseFunctionInput reads f(x) = …, y = …, g(t) := … and bare expressions for solvers and plots

import { Q, MathError } from './rational.js';
import { num, sym, add, mul, div, neg, pow, fn, rel, chain, list, toNode } from './ast.js';
import { msg, notation, resolveLanguage, lookalikes } from '../i18n/index.js';

// ---------------------------------------------------------------- vocabulary

const FN_ALIASES = {
    sin: 'sin',
    cos: 'cos',
    tan: 'tan',
    tg: 'tan',
    cot: 'cot',
    ctg: 'cot',
    cotg: 'cot',
    sec: 'sec',
    csc: 'csc',
    cosec: 'csc',
    asin: 'asin',
    arcsin: 'asin',
    acos: 'acos',
    arccos: 'acos',
    atan: 'atan',
    arctan: 'atan',
    arctg: 'atan',
    acot: 'acot',
    arccot: 'acot',
    arcctg: 'acot',
    sinh: 'sinh',
    sh: 'sinh',
    cosh: 'cosh',
    ch: 'cosh',
    tanh: 'tanh',
    th: 'tanh',
    coth: 'coth',
    cth: 'coth',
    asinh: 'asinh',
    arsinh: 'asinh',
    arcsinh: 'asinh',
    arsh: 'asinh',
    acosh: 'acosh',
    arcosh: 'acosh',
    arccosh: 'acosh',
    arch: 'acosh',
    atanh: 'atanh',
    artanh: 'atanh',
    arctanh: 'atanh',
    arth: 'atanh',
    ln: 'ln',
    lg: 'lg',
    log: 'log',
    exp: 'exp',
    sqrt: 'sqrt',
    cbrt: 'cbrt',
    root: 'root',
    abs: 'abs',
    sign: 'sign',
    sgn: 'sign',
    floor: 'floor',
    ceil: 'ceil',
    sine: 'sin',
    cosine: 'cos',
    tangent: 'tan',
    cotangent: 'cot',
};

const INVERSE = { sin: 'asin', cos: 'acos', tan: 'atan', cot: 'acot', sinh: 'asinh', cosh: 'acosh', tanh: 'atanh' };

const CONST_WORDS = { pi: 'pi', inf: 'inf', infty: 'inf', infinity: 'inf' };

// Greek names recognised inside letter runs (short risky ones — eta, nu, xi, chi — only as \eta or unicode).
const GREEK_WORDS = [
    'alpha',
    'beta',
    'gamma',
    'delta',
    'epsilon',
    'varepsilon',
    'zeta',
    'theta',
    'vartheta',
    'iota',
    'kappa',
    'lambda',
    'mu',
    'rho',
    'sigma',
    'tau',
    'upsilon',
    'phi',
    'varphi',
    'psi',
    'omega',
    'Gamma',
    'Delta',
    'Theta',
    'Lambda',
    'Sigma',
    'Phi',
    'Psi',
    'Omega',
];
const GREEK_ALL = [...GREEK_WORDS, 'eta', 'nu', 'xi', 'chi', 'Xi', 'Pi'];
const GREEK_NORMAL = { varepsilon: 'epsilon', varphi: 'phi', vartheta: 'theta' };

const GREEK_CHARS = {
    α: 'alpha',
    β: 'beta',
    γ: 'gamma',
    δ: 'delta',
    ε: 'epsilon',
    ϵ: 'epsilon',
    ζ: 'zeta',
    η: 'eta',
    θ: 'theta',
    ϑ: 'theta',
    ι: 'iota',
    κ: 'kappa',
    λ: 'lambda',
    μ: 'mu',
    ν: 'nu',
    ξ: 'xi',
    ρ: 'rho',
    σ: 'sigma',
    τ: 'tau',
    υ: 'upsilon',
    φ: 'phi',
    ϕ: 'phi',
    χ: 'chi',
    ψ: 'psi',
    ω: 'omega',
    Γ: 'Gamma',
    Δ: 'Delta',
    Θ: 'Theta',
    Λ: 'Lambda',
    Σ: 'Sigma',
    Φ: 'Phi',
    Ψ: 'Psi',
    Ω: 'Omega',
};

// letters of other layouts that look like Latin ones (a Russian keyboard left on): the language packs list them
const lookalike = (c) => lookalikes()[c];

const SUP = {
    '⁰': '0',
    '¹': '1',
    '²': '2',
    '³': '3',
    '⁴': '4',
    '⁵': '5',
    '⁶': '6',
    '⁷': '7',
    '⁸': '8',
    '⁹': '9',
    '⁺': '+',
    '⁻': '-',
    '⁽': '(',
    '⁾': ')',
    ⁿ: 'n',
    ˣ: 'x',
    ⁱ: 'i',
    ᵏ: 'k',
    ᵐ: 'm',
    '˙': '',
};
const SUB = {
    '₀': '0',
    '₁': '1',
    '₂': '2',
    '₃': '3',
    '₄': '4',
    '₅': '5',
    '₆': '6',
    '₇': '7',
    '₈': '8',
    '₉': '9',
    ₙ: 'n',
    ₖ: 'k',
    ᵢ: 'i',
    ⱼ: 'j',
    ₓ: 'x',
    ₘ: 'm',
};

const MINUS = new Set(['-', '−', '–', '—', '‐', '‑', '‒', '﹣', '－']);
const TIMES = new Set(['*', '·', '×', '⋅', '∙', '∗', '•', '✕']);
const DIVIDE = new Set(['/', '÷', '∕', '⁄', ':']);
const SPACES = new Set([' ', '\t', '\r', '\u00a0', '\u202f', '\u2009', '\u2002', '\u2003', '\u200b', '\f', '\v']);
const OPEN = { '(': ')', '[': ']', '{': '}' };
const CLOSE = { ')': '(', ']': '[', '}': '{' };

// Words that look like functions people might try, but that the engine does not read.
const UNSUPPORTED = new Set([
    'max',
    'min',
    'gcd',
    'lcm',
    'mod',
    'lim',
    'sum',
    'int',
    'det',
    'deg',
    'rad',
    'arg',
    'diff',
    'sqr',
    'rank',
    'dim',
    'arcsec',
    'arccsc',
    'arccosec',
    'binom',
    'nod',
    'nok',
    'prod',
    'integral',
    'derivative',
]);

const WORDS = new Map();
for (const [k, v] of Object.entries(FN_ALIASES)) WORDS.set(k, { kind: 'fn', name: v });
for (const [k, v] of Object.entries(CONST_WORDS)) WORDS.set(k, { kind: 'sym', name: v });
for (const g of GREEK_WORDS) WORDS.set(g, { kind: 'sym', name: GREEK_NORMAL[g] ?? g });
const MAX_WORD = Math.max(...[...WORDS.keys()].map((w) => w.length));

const TEX_OPS = {
    cdot: '*',
    times: '*',
    ast: '*',
    div: '/',
    le: '<=',
    leq: '<=',
    leqslant: '<=',
    ge: '>=',
    geq: '>=',
    geqslant: '>=',
    ne: '!=',
    neq: '!=',
    lt: '<',
    gt: '>',
    vert: '|',
    lvert: '|',
    rvert: '|',
    mid: '|',
    lbrace: '{',
    rbrace: '}',
    pm: '±',
    mp: '∓',
};
const TEX_SKIP = new Set([
    'left',
    'right',
    'big',
    'Big',
    'bigg',
    'Bigg',
    'bigl',
    'bigr',
    'Bigl',
    'Bigr',
    'biggl',
    'biggr',
    'displaystyle',
    'textstyle',
    'limits',
]);
const TEX_WORD = new Set(['operatorname', 'mathrm', 'text', 'mathit', 'textrm']);

const isDigit = (c) => c >= '0' && c <= '9';
const isLatin = (c) => (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
const isLetterish = (c) => isLatin(c) || lookalike(c) !== undefined;

function levenshtein(a, b) {
    const d = Array.from({ length: a.length + 1 }, (_, i) => [i]);
    for (let j = 1; j <= b.length; j++) d[0][j] = j;
    for (let i = 1; i <= a.length; i++) {
        for (let j = 1; j <= b.length; j++) {
            d[i][j] = Math.min(d[i - 1][j] + 1, d[i][j - 1] + 1, d[i - 1][j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
        }
    }
    return d[a.length][b.length];
}

function suggestFn(word) {
    const w = word.toLowerCase();
    let best = null;
    let bd = Infinity;
    for (const k of Object.keys(FN_ALIASES)) {
        if (k.length < 3) continue;
        const dd = levenshtein(w, k);
        if (dd < bd) {
            bd = dd;
            best = k;
        }
    }
    const limit = w.length <= 4 ? 1 : 2;
    return bd <= limit ? best : null;
}

function err(msg, pos = null, len = 1, code = 'syntax') {
    return new MathError(msg, pos, len, code);
}

const show = (s) => (s === '\n' ? '↵' : s);

// ---------------------------------------------------------------- tokenizer

// Token: {t, v, pos, len, ...}; t ∈ num sym fn op rel sep open close bar root frac texsqrt
function tokenize(src, opts, offset = 0, spanLen = null) {
    const s = src;
    const n = s.length;
    const toks = [];
    const declared = opts._declared;
    const declaredLong = opts._declaredLong;
    const at = (p, l) => (spanLen === null ? { pos: offset + p, len: l } : { pos: offset, len: spanLen });
    const push = (t, v, p, l, extra) => toks.push({ t, v, ...at(p, l), ...extra });

    // comma runs: 1,2,3 is a list; 1,000,000 (groups of exactly three digits) is one number; 3,5 is 3.5
    const listCommas = new Set();
    const thousandCommas = new Set();
    for (let k = 0; k < n; k++) {
        if (!isDigit(s[k]) || (k > 0 && (isDigit(s[k - 1]) || s[k - 1] === ',' || s[k - 1] === '.'))) continue;
        const commas = [];
        let j = k;
        while (j < n && isDigit(s[j])) j++;
        while (s[j] === ',' && isDigit(s[j + 1])) {
            commas.push(j);
            j++;
            while (j < n && isDigit(s[j])) j++;
        }
        if (!commas.length) continue;
        const groups = commas.map((c, idx) => s.slice(c + 1, commas[idx + 1] ?? j));
        const lead = s.slice(k, commas[0]);
        const thousands =
            lead.length <= 3 && lead[0] !== '0' && groups.every((g) => g.length === 3) && (commas.length >= 2 || notation(opts.lang).thousandsComma);
        if (thousands) for (const c of commas) thousandCommas.add(c);
        else if (commas.length >= 2) for (const c of commas) listCommas.add(c);
    }

    // bracket contexts: inside root(...) / log(...) a comma separates arguments (unless ';' is used there)
    const ctx = [];
    const argsCtxAt = (p) => {
        // does the bracket group starting at p contain ';' at its own depth?
        let depth = 0;
        for (let j = p; j < n; j++) {
            const c = s[j];
            if (OPEN[c]) depth++;
            else if (CLOSE[c]) {
                depth--;
                if (depth === 0) return false;
            } else if (c === ';' && depth === 1) return true;
        }
        return false;
    };
    const commaIsDecimal = (p) => {
        if (listCommas.has(p) || thousandCommas.has(p)) return false;
        const top = ctx[ctx.length - 1];
        return !(top && top.args && !top.semi);
    };

    let i = 0;

    while (i < n) {
        const c = s[i];
        if (SPACES.has(c)) {
            i++;
            continue;
        }
        if (c === '\n') {
            push('sep', ';', i, 1, { nl: true });
            i++;
            continue;
        }

        // ---- numbers
        if (isDigit(c) || (c === '.' && isDigit(s[i + 1]))) {
            const start = i;
            let int = '';
            while (i < n && isDigit(s[i])) int += s[i++];
            const prev = toks[toks.length - 1];
            const prev2 = toks[toks.length - 2];
            const afterSup = prev2 && prev2.t === 'op' && (prev2.v === '^' || prev2.v === '_');
            if (prev && prev.t === 'num' && !afterSup && spanLen === null) {
                throw err(msg('core.parse.two_numbers_in_row_put_operation'), prev.pos, offset + i + 1 - prev.pos);
            }
            // thousands groups: "1 000 000", "12 345", "1,000,000" (not right after ^ or _: log_2 100 is log base 2 of 100)
            const noGroup = prev && prev.t === 'op' && (prev.v === '^' || prev.v === '_');
            if (int.length > 0 && int.length <= 3 && int[0] !== '0' && !noGroup) {
                let j = i;
                for (;;) {
                    const sp = s[j];
                    const spaceSep = sp === ' ' || sp === '\u00a0' || sp === '\u202f' || sp === '\u2009';
                    if (!spaceSep && !(sp === ',' && thousandCommas.has(j))) break;
                    const g = s.slice(j + 1, j + 4);
                    if (!/^\d{3}$/.test(g) || isDigit(s[j + 4] ?? '')) break;
                    int += g;
                    j += 4;
                }
                i = j;
            }
            let frac = null;
            let period = null;
            let sepChar = null;
            if ((s[i] === '.' || (s[i] === ',' && commaIsDecimal(i))) && (isDigit(s[i + 1]) || (s[i + 1] === '(' && /^\(\d+\)/.test(s.slice(i + 1))))) {
                sepChar = s[i];
                i++;
                frac = '';
                while (i < n && isDigit(s[i])) frac += s[i++];
                const m = /^\((\d+)\)/.exec(s.slice(i));
                if (m) {
                    period = m[1];
                    i += m[0].length;
                }
            }
            if (s[i] === '.' && isDigit(s[i + 1] ?? '')) throw err(msg('core.parse.two_decimal_points_in_one_number'), offset + start, i - start + 2);
            const raw = s.slice(start, i).replace(/[\s\u00a0\u202f\u2009]/g, '');
            let q;
            if (period !== null) q = Q.of(`${int || '0'}.${frac}(${period})`);
            else if (frac !== null) q = Q.of(`${int || '0'}.${frac}`);
            else q = Q.of(BigInt(int));
            push('num', q, start, i - start, sepChar || period !== null ? { raw } : {});
            continue;
        }

        // ---- declared multi-character variables (opts.vars), e.g. x1, speed
        if (declaredLong.length && (isLetterish(c) || c === '_')) {
            const hit = declaredLong.find((v) => s.startsWith(v, i));
            if (hit) {
                push('sym', hit, i, hit.length, { isVar: true });
                i += hit.length;
                i = readSubscript(i);
                continue;
            }
        }

        // ---- letter runs
        if (isLetterish(c)) {
            const start = i;
            let word = '';
            while (i < n && isLetterish(s[i])) {
                word += lookalike(s[i]) ?? s[i];
                i++;
            }
            if (opts.foldCase) word = word.toLowerCase();
            const lower = word.toLowerCase();
            if (UNSUPPORTED.has(lower) && !declared.has(word)) {
                throw err(msg('core.parse.is_not_supported_here', { word }), offset + start, word.length, 'unsupported');
            }
            const pieces = splitWord(word, declared);
            if (word.length >= 3 && pieces.every((p) => p.kind === 'letter')) {
                let j = i;
                while (SPACES.has(s[j])) j++;
                if (s[j] === '(') {
                    const sug = suggestFn(word);
                    if (sug) {
                        throw err(msg('core.parse.unknown_function_did_you_mean', { word, sug }), offset + start, word.length, 'unknown-fn');
                    }
                }
            }
            for (let k = 0; k < pieces.length; k++) {
                const p = pieces[k];
                const last = k === pieces.length - 1;
                const ppos = start + p.at;
                if (p.kind === 'fn') {
                    const extra = { raw: word.slice(p.at, p.at + p.len) };
                    let plen = p.len;
                    if (p.name === 'log' && last && isDigit(s[i] ?? '')) {
                        // log2(x), log10 x
                        let d = '';
                        while (i < n && isDigit(s[i])) d += s[i++];
                        extra.base = Q.of(BigInt(d));
                        plen += d.length;
                    }
                    push('fn', p.name, ppos, plen, extra);
                } else if (p.kind === 'letter') {
                    push('sym', p.name, ppos, p.len, declared.has(p.name) ? { isVar: true } : {});
                } else {
                    push('sym', p.name, ppos, p.len, p.kind === 'var' ? { isVar: true } : {});
                }
            }
            const lastPiece = pieces[pieces.length - 1];
            if (lastPiece.kind !== 'fn') i = readSubscript(i);
            else if (s[i] === '_') {
                if (lastPiece.name !== 'log') throw err(msg('core.parse.only_variable_or_logarithm_can_have'), offset + i, 1);
                push('op', '_', i, 1);
                i++;
            }
            continue;
        }

        // ---- greek and other unicode symbols
        if (GREEK_CHARS[c]) {
            push('sym', GREEK_CHARS[c], i, 1, declared.has(GREEK_CHARS[c]) ? { isVar: true } : {});
            i = readSubscript(i + 1);
            continue;
        }
        if (c === 'π') {
            push('sym', 'pi', i, 1, declared.has('pi') ? { isVar: true } : {});
            i++;
            continue;
        }
        if (c === '∞') {
            push('sym', 'inf', i, 1);
            i++;
            continue;
        }
        if (c === '√' || c === '∛' || c === '∜') {
            push('root', c === '√' ? 2 : c === '∛' ? 3 : 4, i, 1);
            i++;
            continue;
        }

        // ---- superscripts: x², x⁻¹
        if (SUP[c] !== undefined) {
            const start = i;
            let t = '';
            while (i < n && SUP[s[i]] !== undefined) t += SUP[s[i++]];
            if (!t) continue;
            push('op', '^', start, i - start);
            toks.push(...tokenize(`(${t})`, opts, offset + start, i - start));
            continue;
        }
        if (SUB[c] !== undefined) throw err(msg('core.parse.subscript_without_variable'), offset + i, 1);

        // ---- LaTeX commands
        if (c === '\\') {
            const start = i;
            i++;
            let cmd = '';
            while (i < n && isLatin(s[i])) cmd += s[i++];
            if (!cmd) {
                const d = s[i++] ?? '';
                if (d === ',' || d === ';' || d === ':' || d === '!' || d === ' ' || d === '>') continue;
                if (d === '{' || d === '}') {
                    push(d === '{' ? 'open' : 'close', d, start, 2);
                    if (d === '{') ctx.push({});
                    else ctx.pop();
                    continue;
                }
                if (d === '|') {
                    push('bar', '|', start, 2);
                    continue;
                }
                throw err(msg('core.parse.unknown_command', { d }), offset + start, 2);
            }
            if (TEX_SKIP.has(cmd)) continue;
            if (cmd in TEX_OPS) {
                const v = TEX_OPS[cmd];
                if (v === '*' || v === '/' || v === '±' || v === '∓') push('op', v, start, i - start);
                else if (v === '|') push('bar', '|', start, i - start);
                else if (v === '{') {
                    push('open', '{', start, i - start);
                    ctx.push({});
                } else if (v === '}') {
                    push('close', '}', start, i - start);
                    ctx.pop();
                } else push('rel', v, start, i - start);
                continue;
            }
            if (cmd === 'frac' || cmd === 'dfrac' || cmd === 'tfrac') {
                push('frac', cmd, start, i - start);
                continue;
            }
            if (cmd === 'sqrt') {
                push('texsqrt', cmd, start, i - start);
                continue;
            }
            if (TEX_WORD.has(cmd)) {
                const m = /^\s*\{([^{}]*)\}/.exec(s.slice(i));
                if (!m) throw err(msg('core.parse.needs', { cmd }), offset + start, i - start);
                const w = m[1].trim();
                i += m[0].length;
                if (FN_ALIASES[w]) push('fn', FN_ALIASES[w], start, i - start, { raw: w });
                else if (/^[A-Za-z]$/.test(w)) push('sym', w, start, i - start);
                else throw err(msg('core.parse.unknown_name', { w }), offset + start, i - start, 'unknown-fn');
                continue;
            }
            if (FN_ALIASES[cmd]) {
                push('fn', FN_ALIASES[cmd], start, i - start, { raw: cmd });
                if (s[i] === '_' && FN_ALIASES[cmd] === 'log') {
                    push('op', '_', i, 1);
                    i++;
                }
                continue;
            }
            if (cmd === 'pi' || cmd === 'infty') {
                push('sym', cmd === 'pi' ? 'pi' : 'inf', start, i - start);
                continue;
            }
            if (GREEK_ALL.includes(cmd)) {
                const g = GREEK_NORMAL[cmd] ?? cmd;
                push('sym', g, start, i - start, declared.has(g) ? { isVar: true } : {});
                i = readSubscript(i);
                continue;
            }
            throw err(msg('core.parse.unknown_command_2', { cmd }), offset + start, i - start, 'unknown-fn');
        }

        // ---- operators and punctuation
        if (c === '±' || c === '∓') {
            push('op', c, i, 1);
            i++;
            continue;
        }
        if (c === '+' && s[i + 1] === '/' && MINUS.has(s[i + 2])) {
            push('op', '±', i, 3); // +/- (but +- stays a + (−b))
            i += 3;
            continue;
        }
        if (c === '+' || c === '＋') {
            push('op', '+', i, 1);
            i++;
            continue;
        }
        if (MINUS.has(c)) {
            push('op', '-', i, 1);
            i++;
            continue;
        }
        if (TIMES.has(c)) {
            if (c === '*' && s[i + 1] === '*') {
                push('op', '^', i, 2);
                i += 2;
                continue;
            }
            push('op', '*', i, 1);
            i++;
            continue;
        }
        if (DIVIDE.has(c)) {
            push('op', '/', i, 1);
            i++;
            continue;
        }
        if (c === '^') {
            push('op', '^', i, 1);
            i++;
            continue;
        }
        if (c === '!') {
            if (s[i + 1] === '=') {
                push('rel', '!=', i, 2);
                i += 2;
                continue;
            }
            push('op', '!', i, 1);
            i++;
            continue;
        }
        if (c === '%' || c === '°') {
            push('op', c, i, 1);
            i++;
            continue;
        }
        if (c === '=') {
            if (s[i + 1] === '=') {
                push('rel', '=', i, 2);
                i += 2;
            } else if (s[i + 1] === '<') {
                push('rel', '<=', i, 2);
                i += 2;
            } else if (s[i + 1] === '>') {
                push('rel', '>=', i, 2);
                i += 2;
            } else {
                push('rel', '=', i, 1);
                i++;
            }
            continue;
        }
        if (c === '<' || c === '>') {
            if (s[i + 1] === '=') {
                push('rel', c + '=', i, 2);
                i += 2;
            } else if (c === '<' && s[i + 1] === '>') {
                push('rel', '!=', i, 2);
                i += 2;
            } else {
                push('rel', c, i, 1);
                i++;
            }
            continue;
        }
        if (c === '≤' || c === '⩽') {
            push('rel', '<=', i, 1);
            i++;
            continue;
        }
        if (c === '≥' || c === '⩾') {
            push('rel', '>=', i, 1);
            i++;
            continue;
        }
        if (c === '≠') {
            push('rel', '!=', i, 1);
            i++;
            continue;
        }
        if (c === ',' || c === ';') {
            push('sep', c, i, 1);
            i++;
            continue;
        }
        if (OPEN[c]) {
            const prev = toks[toks.length - 1];
            const args = prev && prev.t === 'fn' && (prev.v === 'root' || (prev.v === 'log' && !prev.base));
            ctx.push(args ? { args: true, semi: argsCtxAt(i) } : {});
            push('open', c, i, 1);
            i++;
            continue;
        }
        if (CLOSE[c]) {
            ctx.pop();
            push('close', c, i, 1);
            i++;
            continue;
        }
        if (c === '|' || c === '｜' || c === '∣') {
            push('bar', '|', i, 1);
            i++;
            continue;
        }
        if (c === '_') throw err(msg('core.parse.subscript_without_variable'), offset + i, 1);
        if (c === "'" || c === '′') throw err(msg('core.parse.primes_derivatives_are_not_read_here'), offset + i, 1, 'unsupported');
        if (/\p{L}/u.test(c)) throw err(msg('core.parse.unknown_letter', { c }), offset + i, 1);
        throw err(msg('core.parse.unexpected_character', { c: show(c) }), offset + i, 1);
    }
    return toks;

    // x_1, a_{12}, x_n, x₁ — merged into the name of the symbol just pushed
    function readSubscript(j) {
        const last = toks[toks.length - 1];
        let subs = '';
        const from = j;
        if (s[j] === '_') {
            j++;
            if (s[j] === '{') {
                const m = /^\{\s*([A-Za-z0-9]+)\s*\}/.exec(s.slice(j));
                if (!m) throw err(msg('core.parse.subscript_in_must_be_letters_and'), offset + from, 2);
                subs = m[1];
                j += m[0].length;
            } else if (isDigit(s[j] ?? '')) {
                while (j < n && isDigit(s[j])) subs += s[j++];
            } else if (isLetterish(s[j] ?? '')) {
                subs = lookalike(s[j]) ?? s[j];
                j++;
            } else throw err(msg('core.parse.subscript_is_expected_after'), offset + from, 1);
        } else if (SUB[s[j]] !== undefined) {
            while (j < n && SUB[s[j]] !== undefined) subs += SUB[s[j++]];
        } else return j;
        const name = `${last.v}_${subs}`;
        last.v = name;
        last.len = spanLen === null ? offset + j - last.pos : spanLen;
        if (declared.has(name)) last.isVar = true;
        return j;
    }
}

// Greedy split of a letter run into known words and single letters.
function splitWord(word, declared) {
    const out = [];
    let p = 0;
    while (p < word.length) {
        let found = null;
        for (let L = Math.min(Math.max(MAX_WORD, 12), word.length - p); L >= 2; L--) {
            const sub = word.substr(p, L);
            if (declared.has(sub)) {
                found = { kind: 'var', name: sub, at: p, len: L };
                break;
            }
            const w = WORDS.get(sub);
            if (w) {
                found = { ...w, at: p, len: L };
                break;
            }
            if (p === 0 && (sub === sub.toUpperCase() || sub[0] + sub.slice(1).toLowerCase() === sub)) {
                const wl = WORDS.get(sub.toLowerCase());
                if (wl && wl.kind === 'fn') {
                    found = { ...wl, at: p, len: L };
                    break;
                }
            }
        }
        if (!found) found = { kind: 'letter', name: word[p], at: p, len: 1 };
        out.push(found);
        p += found.len;
    }
    return out;
}

// ---------------------------------------------------------------- parser

const END = { t: 'end' };
const MAX_DEPTH = 200;

class Parser {
    constructor(src, toks) {
        this.src = src;
        this.toks = toks;
        this.i = 0;
        this.abs = 0;
        this.depth = 0;
    }

    peek(k = 0) {
        return this.toks[this.i + k] ?? { ...END, pos: this.src.length, len: 0 };
    }

    prev() {
        return this.toks[this.i - 1];
    }

    next() {
        return this.toks[this.i++] ?? { ...END, pos: this.src.length, len: 0 };
    }

    isOp(v, k = 0) {
        const t = this.peek(k);
        return t.t === 'op' && t.v === v;
    }

    enter(tok) {
        if (++this.depth > MAX_DEPTH) throw err(msg('core.parse.nested_too_deeply'), tok.pos, 1, 'too-big');
    }

    canImplicit(t) {
        return (
            t.t === 'num' ||
            t.t === 'sym' ||
            t.t === 'fn' ||
            t.t === 'open' ||
            t.t === 'root' ||
            t.t === 'frac' ||
            t.t === 'texsqrt' ||
            (t.t === 'bar' && this.abs === 0)
        );
    }

    parseTop() {
        const node = this.parseList();
        const t = this.peek();
        if (t.t !== 'end') this.unexpected(t);
        return node;
    }

    parseList() {
        const items = [];
        // leading separators (e.g. blank first line) are skipped
        while (this.peek().t === 'sep' && this.peek().nl) this.next();
        items.push(this.parseRel());
        while (this.peek().t === 'sep') {
            const s = this.next();
            const t = this.peek();
            if (t.t === 'end' || t.t === 'close') {
                if (s.v === ';' || s.nl) break; // trailing ; or newline
                throw err(msg('core.parse.nothing_after_comma'), s.pos, 1);
            }
            if (t.t === 'sep') {
                if (s.nl || t.nl) continue;
                throw err(msg('core.parse.empty_list_item'), t.pos, 1);
            }
            items.push(this.parseRel());
        }
        return items.length > 1 ? list(items) : items[0];
    }

    parseRel() {
        const items = [this.parseAdd()];
        const ops = [];
        while (this.peek().t === 'rel') {
            const r = this.next();
            const t = this.peek();
            if (t.t === 'end' || t.t === 'sep' || t.t === 'close') throw err(msg('core.parse.nothing_after', { v: r.v }), r.pos, r.len);
            if (t.t === 'rel') throw err(msg('core.parse.two_relation_signs_in_row_and', { v: r.v, v2: t.v }), t.pos, t.len);
            ops.push(r.v);
            items.push(this.parseAdd());
        }
        if (!ops.length) return items[0];
        if (ops.length === 1) return rel(ops[0], items[0], items[1]);
        return chain(items, ops);
    }

    parseAdd() {
        const terms = [this.parseTerm()];
        for (;;) {
            const t = this.peek();
            if (t.t !== 'op' || (t.v !== '+' && t.v !== '-')) break;
            this.next();
            const rhs = this.parseTerm();
            terms.push(t.v === '-' ? neg(rhs) : rhs);
        }
        return terms.length > 1 ? add(terms) : terms[0];
    }

    // leading signs apply to the whole product that follows: -2x = -(2x)
    parseTerm() {
        const t = this.peek();
        if (t.t === 'op' && t.v === '-') {
            this.next();
            this.enter(t);
            const r = neg(this.parseTerm());
            this.depth--;
            return r;
        }
        if (t.t === 'op' && t.v === '+') {
            this.next();
            return this.parseTerm();
        }
        return this.parseMul();
    }

    parseMul(stopAtFn = false) {
        let cur = [this.parsePower()];
        let acc;
        for (;;) {
            const t = this.peek();
            if (t.t === 'op' && (t.v === '*' || t.v === '/')) {
                if (stopAtFn) break;
                this.next();
                const f = this.parseSigned();
                if (t.v === '*') cur.push(f);
                else {
                    acc = div(cur.length > 1 ? mul(cur) : cur[0], f);
                    cur = [acc];
                }
                continue;
            }
            if (this.canImplicit(t)) {
                if (stopAtFn && t.t === 'fn') break;
                cur.push(this.parsePower());
                continue;
            }
            break;
        }
        return cur.length > 1 ? mul(cur) : cur[0];
    }

    // operand after * or / : a sign is allowed (2*-3)
    parseSigned() {
        const t = this.peek();
        if (t.t === 'op' && t.v === '-') {
            this.next();
            this.enter(t);
            const r = neg(this.parseSigned());
            this.depth--;
            return r;
        }
        if (t.t === 'op' && t.v === '+') {
            this.next();
            return this.parseSigned();
        }
        return this.parsePower();
    }

    parsePower() {
        const base = this.parsePostfix();
        if (this.isOp('^')) {
            const t = this.next();
            this.enter(t);
            const nt = this.peek();
            if (nt.t === 'end' || nt.t === 'sep' || nt.t === 'close' || nt.t === 'rel') throw err(msg('core.parse.power_has_no_exponent'), t.pos, t.len);
            const e = this.parseExponent();
            this.depth--;
            return pow(base, e);
        }
        return base;
    }

    parseExponent() {
        const t = this.peek();
        if (t.t === 'op' && t.v === '-') {
            this.next();
            return neg(this.parseExponent());
        }
        if (t.t === 'op' && t.v === '+') {
            this.next();
            return this.parseExponent();
        }
        return this.parsePower();
    }

    parsePostfix() {
        let node = this.parsePrimary();
        for (;;) {
            const t = this.peek();
            if (t.t !== 'op') break;
            if (t.v === '!') {
                this.next();
                node = fn('fact', node);
            } else if (t.v === '%') {
                this.next();
                node = div(node, num(100));
            } else if (t.v === '°') {
                this.next();
                node = div(mul(node, sym('pi')), num(180));
            } else break;
        }
        return node;
    }

    parseGroup(open) {
        // after an opening bracket
        const saved = this.abs;
        this.abs = 0;
        const t = this.peek();
        if (t.t === 'close') throw err(msg('core.parse.empty_brackets'), open.pos, t.pos + t.len - open.pos);
        const inner = this.parseList();
        const c = this.next();
        if (c.t !== 'close') this.unexpected(c, open);
        this.abs = saved;
        return inner;
    }

    parsePrimary() {
        const t = this.peek();
        this.enter(t);
        let r;
        switch (t.t) {
            case 'num':
                this.next();
                r = num(t.v, t.raw);
                break;
            case 'sym':
                this.next();
                r = sym(t.v, !!t.isVar);
                break;
            case 'open':
                this.next();
                r = this.parseGroup(t);
                break;
            case 'bar': {
                this.next();
                this.abs++;
                const nt = this.peek();
                if (nt.t === 'bar' && this.peek(1).t !== 'sym' && this.peek(1).t !== 'num' && this.peek(1).t !== 'open') {
                    throw err(msg('core.parse.empty_absolute_value'), t.pos, nt.pos + 1 - t.pos);
                }
                if (nt.t === 'end') throw err(msg('core.parse.absolute_value_is_not_closed_is'), t.pos, 1);
                const inner = this.parseAdd();
                const c = this.next();
                if (c.t !== 'bar') {
                    if (c.t === 'end') throw err(msg('core.parse.absolute_value_is_not_closed_is'), t.pos, 1);
                    this.unexpected(c);
                }
                this.abs--;
                r = fn('abs', inner);
                break;
            }
            case 'root': {
                this.next();
                const nt = this.peek();
                if (nt.t === 'end' || nt.t === 'sep' || nt.t === 'close' || nt.t === 'rel' || (nt.t === 'op' && nt.v !== '-' && nt.v !== '+')) {
                    throw err(msg('core.parse.nothing_under_root_sign'), t.pos, 1);
                }
                const a = this.parseExponent();
                r = t.v === 2 ? fn('sqrt', a) : fn('root', a, num(t.v));
                break;
            }
            case 'fn':
                r = this.parseFunction();
                break;
            case 'frac': {
                this.next();
                const a = this.texArg(t);
                const b = this.texArg(t);
                r = div(a, b);
                break;
            }
            case 'texsqrt': {
                this.next();
                let idx = null;
                if (this.peek().t === 'open' && this.peek().v === '[') {
                    const o = this.next();
                    idx = this.parseGroup(o);
                }
                const a = this.texArg(t);
                r = idx ? fn('root', a, idx) : fn('sqrt', a);
                break;
            }
            default:
                this.unexpected(t);
        }
        this.depth--;
        return r;
    }

    texArg(cmd) {
        const t = this.peek();
        if (t.t === 'open') {
            this.next();
            return this.parseGroup(t);
        }
        if (t.t === 'num' || t.t === 'sym') {
            this.next();
            return t.t === 'num' ? num(t.v, t.raw) : sym(t.v, !!t.isVar);
        }
        throw err(msg('core.parse.needs_2', { v: cmd.v }), cmd.pos, cmd.len);
    }

    parseFunction() {
        const tok = this.next();
        const label = tok.raw ?? tok.v;
        let name = tok.v;
        let power = null;
        let base = tok.base ? num(tok.base) : null;
        const readPower = () => {
            if (this.isOp('^')) {
                const p = this.next();
                const nt = this.peek();
                if (nt.t === 'end' || nt.t === 'sep' || nt.t === 'close' || nt.t === 'rel') throw err(msg('core.parse.power_has_no_exponent'), p.pos, p.len);
                power = this.parseExponent();
            }
        };
        readPower();
        if (name === 'log' && !base && this.isOp('_')) {
            const u = this.next();
            const t = this.peek();
            if (t.t === 'open') {
                this.next();
                base = this.parseGroup(t);
            } else if (t.t === 'num' || t.t === 'sym') {
                this.next();
                base = t.t === 'num' ? num(t.v, t.raw) : sym(t.v, !!t.isVar);
            } else throw err(msg('core.parse.base_is_expected_after_log'), u.pos, 1);
            if (!power) readPower();
        }
        let args;
        const t = this.peek();
        if (t.t === 'open') {
            this.next();
            args = this.parseArgs(t, label);
        } else if (this.canImplicit(t) || (t.t === 'op' && t.v === '-')) {
            args = [this.parseBareArg()];
        } else {
            throw err(msg('core.parse.needs_argument_e_g_x', { label }), tok.pos, tok.len, 'no-arg');
        }
        const one = () => {
            if (args.length !== 1) throw err(msg('core.parse.takes_one_argument', { label }), tok.pos, tok.len, 'arity');
            return args[0];
        };
        if (power && INVERSE[name]) {
            const pv = power.type === 'neg' && power.arg.type === 'num' ? power.arg.value.neg() : power.type === 'num' ? power.value : null;
            if (pv && pv.eq(-1)) {
                name = INVERSE[name];
                power = null;
            }
        }
        let node;
        switch (name) {
            case 'log':
                if (base) node = fn('log', base, one());
                else if (args.length === 2) node = fn('log', args[0], args[1]);
                else node = fn('log', num(10), one());
                break;
            case 'root':
                if (args.length !== 2) throw err(msg('core.parse.root_needs_index_root_x_3'), tok.pos, tok.len, 'arity');
                node = fn('root', args[0], args[1]);
                break;
            case 'sqrt':
                node = args.length === 2 ? fn('root', args[0], args[1]) : fn('sqrt', one());
                break;
            case 'cbrt':
                node = fn('root', one(), num(3));
                break;
            default:
                node = fn(name, one());
        }
        return power ? pow(node, power) : node;
    }

    parseArgs(open, label) {
        const saved = this.abs;
        this.abs = 0;
        if (this.peek().t === 'close') throw err(msg('core.parse.empty_brackets_after', { label }), open.pos, 2);
        const args = [this.parseRel()];
        while (this.peek().t === 'sep') {
            this.next();
            args.push(this.parseRel());
        }
        const c = this.next();
        if (c.t !== 'close') this.unexpected(c, open);
        this.abs = saved;
        return args;
    }

    // sin 2x → sin(2x): one implicit product, stops at + - * / relations and the next function name
    parseBareArg() {
        const t = this.peek();
        if (t.t === 'op' && t.v === '-') {
            this.next();
            return neg(this.parseBareArg());
        }
        if (t.t === 'op' && t.v === '+') {
            this.next();
            return this.parseBareArg();
        }
        const factors = [this.parsePower()];
        for (;;) {
            const nt = this.peek();
            if (nt.t === 'fn' || !this.canImplicit(nt)) break;
            factors.push(this.parsePower());
        }
        return factors.length > 1 ? mul(factors) : factors[0];
    }

    unexpected(t, open = null) {
        const prev = this.prev();
        const pv = prev ? (prev.raw ?? prev.v) : '';
        switch (t.t) {
            case 'end':
                if (open) throw err(msg('core.parse.bracket_is_not_closed', { v: open.v }), open.pos, 1, 'brackets');
                if (prev) throw err(msg('core.parse.expression_ends_right_after', { pv }), prev.pos, prev.len);
                throw err(msg('core.parse.empty_input'), 0, 0, 'empty');
            case 'close':
                if (prev && prev.t === 'open') throw err(msg('core.parse.empty_brackets'), prev.pos, t.pos + 1 - prev.pos);
                if (prev && (prev.t === 'op' || prev.t === 'rel' || prev.t === 'sep'))
                    throw err(msg('core.parse.number_or_expression_is_expected_after', { pv }), prev.pos, prev.len);
                throw err(msg('core.parse.unexpected', { v: t.v }), t.pos, 1, 'brackets');
            case 'op':
                if (prev && prev.t === 'op') throw err(msg('core.parse.two_operators_in_row', { pv, v: t.v }), prev.pos, t.pos + t.len - prev.pos);
                throw err(msg('core.parse.number_or_expression_is_missing_before', { v: t.v }), t.pos, t.len);
            case 'rel':
                throw err(msg('core.parse.expression_is_missing_before', { v: t.v }), t.pos, t.len);
            case 'sep':
                throw err(msg('core.parse.nothing_before', { v: t.v }), t.pos, t.len);
            case 'bar':
                throw err(msg('core.parse.unpaired'), t.pos, 1);
            default:
                throw err(msg('core.parse.unexpected_2', { p: t.raw ?? t.v }), t.pos, t.len);
        }
    }
}

function checkBrackets(toks) {
    const stack = [];
    for (const t of toks) {
        if (t.t === 'open') stack.push(t);
        else if (t.t === 'close') {
            const o = stack.pop();
            if (!o) throw err(msg('core.parse.closing_without_opening_one', { v: t.v }), t.pos, 1, 'brackets');
            if (OPEN[o.v] !== t.v) throw err(msg('core.parse.is_closed_by', { v: o.v, v2: t.v }), o.pos, t.pos + 1 - o.pos, 'brackets');
        }
    }
    if (stack.length) {
        const o = stack[stack.length - 1];
        throw err(msg('core.parse.bracket_is_not_closed', { v: o.v }), o.pos, 1, 'brackets');
    }
}

// «x = 1 ± √2», «±3», «(1 ± √5)/2»: a list item with one ± (∓, \pm, +/-) becomes two items — the ± read
// as + and as − in place (∓: − first). Items are split at separators outside brackets (kit/check.js
// splits answers the same way). Two ± in one item are refused.
function expandPlusMinus(toks) {
    const isPm = (t) => t.t === 'op' && (t.v === '±' || t.v === '∓');
    if (!toks.some(isPm)) return toks;
    const out = [];
    let item = [];
    let depth = 0;
    // «{1 ± 1; 7}»: brackets around the whole list are the list's own
    let base = 0;
    if (toks[0].t === 'open') {
        let d = 0;
        let k = 0;
        for (; k < toks.length; k++) {
            if (toks[k].t === 'open') d++;
            else if (toks[k].t === 'close' && --d === 0) break;
        }
        if (k === toks.length - 1) base = 1;
    }
    const flush = (sep) => {
        const pms = item.filter(isPm);
        if (pms.length > 1) throw err(msg('core.parse.only_one_per_item'), pms[1].pos, pms[1].len, 'unsupported');
        if (!pms.length) out.push(...item);
        else {
            const signs = pms[0].v === '±' ? ['+', '-'] : ['-', '+'];
            signs.forEach((v, k) => {
                if (k) out.push({ t: 'sep', v: ';', pos: pms[0].pos, len: pms[0].len });
                out.push(...item.map((t) => (isPm(t) ? { ...t, v } : t)));
            });
        }
        if (sep) out.push(sep);
        item = [];
    };
    for (const t of toks) {
        if (t.t === 'open') depth++;
        else if (t.t === 'close') depth--;
        if (t.t === 'sep' && depth === base) flush(t);
        else if (base && t.t === 'open' && depth === 1) out.push(t);
        else if (base && t.t === 'close' && depth === 0) {
            flush(null);
            out.push(t);
        } else item.push(t);
    }
    flush(null);
    return out;
}

/**
 * Parse user input into an AST node. Throws MathError (a message, pos, len).
 * opts: { vars?: string[] — extra variable names (multi-letter, or constants like 'i'/'e' used as variables),
 *         foldCase?: boolean — read X as x, Sin as sin, maxLength?: number (default 2000),
 *         lang?: a registered language — in one whose notation has thousandsComma (English) a comma before exactly three
 *         digits is a thousands separator (1,000) }
 */
export function parse(text, opts = {}) {
    if (typeof text !== 'string') throw err(msg('core.parse.input_must_be_string'), 0, 0, 'empty');
    const maxLength = opts.maxLength ?? 2000;
    if (text.length > maxLength) throw err(msg('core.parse.input_is_too_long_over_characters', { maxLength }), maxLength, text.length - maxLength, 'too-big');
    const vars = (opts.vars ?? []).map(String);
    const o = {
        foldCase: !!opts.foldCase,
        lang: resolveLanguage(opts.lang),
        _declared: new Set(vars),
        _declaredLong: vars.filter((v) => v.length > 1 && !/^[A-Za-z]+$/.test(v)).sort((a, b) => b.length - a.length),
    };
    if (!text.trim()) throw err(msg('core.parse.empty_input'), 0, 0, 'empty');
    let toks;
    try {
        toks = tokenize(text, o);
        if (!toks.length) throw err(msg('core.parse.empty_input'), 0, 0, 'empty');
        checkBrackets(toks);
        toks = expandPlusMinus(toks);
        return new Parser(text, toks).parseTop();
    } catch (e) {
        if (e instanceof MathError) throw e;
        if (e instanceof RangeError) throw err(msg('core.parse.expression_is_too_complex'), 0, text.length, 'too-big');
        throw e;
    }
}

/** Like parse, but never throws: {ok: true, node} or {ok: false, error: MathError}. */
export function tryParse(text, opts = {}) {
    try {
        return { ok: true, node: parse(text, opts) };
    } catch (e) {
        if (e instanceof MathError) return { ok: false, error: e };
        return { ok: false, error: new MathError(msg('core.parse.could_not_read_input'), 0, 0, 'internal') };
    }
}

/**
 * An expression as the engine's functions accept it: a node as it is, a string parsed (with opts), a number, bigint
 * or Q as a number node, ±Infinity as ±∞.
 */
export function asNode(x, opts) {
    if (x && typeof x === 'object' && typeof x.type === 'string') return x;
    if (typeof x === 'string') return parse(x, opts);
    if (x === Infinity) return sym('inf');
    if (x === -Infinity) return neg(sym('inf'));
    return toNode(x);
}

// ---------------------------------------------------------------- function inputs

const FN_PREFER = ['x', 't', 'y', 'z', 'u', 'v', 'w', 's', 'n', 'k'];

function freeNames(node, out = new Set()) {
    if (!node || typeof node !== 'object') return out;
    if (node.type === 'sym') {
        if (node.var || !['pi', 'e', 'i', 'inf'].includes(node.name)) out.add(node.name);
        return out;
    }
    for (const k of ['args', 'items']) if (Array.isArray(node[k])) node[k].forEach((a) => freeNames(a, out));
    for (const k of ['num', 'den', 'arg', 'base', 'exp', 'lhs', 'rhs']) if (node[k] && typeof node[k] === 'object') freeNames(node[k], out);
    return out;
}

// parse a piece of the text, with error positions in the whole text
function parseAt(text, from, opts) {
    try {
        return parse(text.slice(from), opts);
    } catch (e) {
        if (e instanceof MathError && typeof e.pos === 'number') throw new MathError(e.msg, e.pos + from, e.len, e.code);
        throw e;
    }
}

// a single name (letter, letter with index, greek, or a declared word) → its canonical name, else null
function nameOf(src, opts) {
    const s = src.trim();
    if (!s) return null;
    const word = /^[A-Za-z]{2,}$/.test(s) && !WORDS.has(s.toLowerCase()) && !UNSUPPORTED.has(s.toLowerCase());
    const tries = [opts, word ? { ...opts, vars: [...(opts.vars ?? []), s] } : null];
    for (const o of tries) {
        if (!o) continue;
        const r = tryParse(s, o);
        if (r.ok && r.node.type === 'sym' && (r.node.var || !['pi', 'e', 'i', 'inf'].includes(r.node.name)))
            return { name: r.node.name, word: word ? s : null };
    }
    return null;
}

const NOT_FN = msg('core.parse.function_is_expected_f_x_y');

/**
 * A function as people type it for a solver or a plot: `f(x) = x^2 - 1`, `y = sin x`, `g(t)=t^3`,
 * `f(x, y) = x y`, `s(t) := 5t^2`, or just `x^2 - 1` → {name: 'f' | null, v: 'x', body: node, vars, lhs, params}:
 * name — the function's letter from `f(…) =` (null for `y = …` and bare expressions); v — its variable
 * (from the brackets, else the body's letter: opts.v, x, t, y, z, … in that order of preference, default
 * opts.v or 'x'); vars — all variables in the brackets ([v] otherwise); lhs — the letter left of `=` in
 * `y = …` (else null); params — other letters of the body. opts are passed to parse (vars, lang, …).
 * Throws MathError: parse errors with positions in the whole text; code 'not-expr' for an equation that
 * defines no function (x^2 + y^2 = 1, x = x^2), an inequality or a list.
 */
export function parseFunctionInput(text, opts = {}) {
    if (typeof text !== 'string') throw err(msg('core.parse.input_must_be_string'), 0, 0, 'empty');
    const done = (name, vars, body, lhs, at) => {
        if (body.type === 'rel' || body.type === 'chain' || body.type === 'list') throw new MathError(NOT_FN, at, text.length - at, 'not-expr');
        const names = [...freeNames(body)];
        let v = vars[0];
        if (!v) {
            const pref = [opts.v, ...FN_PREFER].filter(Boolean);
            v = pref.find((p) => names.includes(p) && p !== lhs) ?? names.filter((p) => p !== lhs).sort()[0] ?? opts.v ?? 'x';
        }
        const all = vars.length ? vars : [v];
        return { name, v, body, vars: all, lhs: lhs ?? null, params: names.filter((p) => !all.includes(p)).sort() };
    };
    // f(x) = …, g(t) := …, f(x, y) = …
    const m = /^(\s*)([^\s()=:]{1,12}?)\s*\(([^()=]*)\)\s*(:=|=(?![=<>]))/.exec(text);
    if (m) {
        // the function's own name is one letter, maybe with an index: f, g, F, y, f_1, φ
        const fname = /^[A-Za-zА-Яа-яЁё\u0370-\u03ff](?:_\{?\w+\}?|[₀-₉]+)?$/.test(m[2]) ? nameOf(m[2], opts) : null;
        const args = m[3].split(/[,;]/).map((a) => nameOf(a, opts));
        if (fname && args.length && args.every(Boolean)) {
            const words = args.map((a) => a.word).filter(Boolean);
            const o = words.length ? { ...opts, vars: [...(opts.vars ?? []), ...words] } : opts;
            const vars = args.map((a) => a.name);
            const body = parseAt(text, m[0].length, o);
            if (!freeNames(body).has(fname.name) || vars.includes(fname.name)) return done(fname.name, vars, body, null, m[0].length);
        }
    }
    // y = …
    const g = /^(\s*)([^\s()=<>!]{1,12}?)\s*=(?![=<>])/.exec(text);
    if (g) {
        const lhs = nameOf(g[2], opts);
        if (lhs) {
            const body = parseAt(text, g[0].length, opts);
            const names = freeNames(body);
            const r = done(null, [], body, lhs.name, g[0].length);
            if (!names.has(lhs.name) && r.v !== lhs.name) return r;
            throw new MathError(NOT_FN, 0, text.length, 'not-expr');
        }
    }
    return done(null, [], parse(text, opts), null, 0);
}
