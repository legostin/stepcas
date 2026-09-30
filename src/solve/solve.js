// solve — equations, inequalities and systems with school-style steps («что делаем и почему»).
//
//   solveEquation(input, v = 'x', {steps, domain: 'real'|'complex', interval})  → roots, steps, check, ОДЗ
//   solveTrig(input, v, opts)                  → the same shape, trigonometric equations only
//   solveInequality(input, v, {steps})         → {set: IntervalSet, steps, signChart}
//   solveLinearSystem(rels, vars, {method})    → unique / none / infinite (parametric)
//   solveSystem2(rels, vars)                   → a linear and a quadratic equation, by substitution
//   checkRoot(rel, v, value)                   → substitution with steps
//   IntervalSet, intervalTex, intervalText, parseIntervalSet, intervalEquals — answers as sets
//
// Correctness first: every root found by a transformation that may add roots (squaring, multiplying by an
// expression, combining logarithms, substitution) is checked by substitution into the original equation and
// against the ОДЗ; roots that fail are listed as extraneous with the reason. When no exact method applies the
// solver says so and, where it makes sense, gives numeric roots marked «≈» together with the search range.

import { Q, MathError, bigGcd, bigLcm, rootExtract } from '../core/rational.js';
import { num, sym, add, mul, div, neg, pow, fn, rel, isConst, nodeKey, freeVars, containsVar, substitute, nodeSome, numValue, nodeChildren, mapNode } from '../core/ast.js';
import { parse } from '../core/parse.js';
import { toTex, toText } from '../core/print.js';
import { simplify, splitCoeff } from '../core/simplify.js';
import { expand, collectTerms, numDen } from '../core/expand.js';
import { Poly, linearForm } from '../core/poly.js';
import { evaluate, compile } from '../core/evaluate.js';
import { step as mkStep } from '../core/steps.js';
import { numFindRoots, numPolyRoots } from '../numbers/numeric.js';
import { Matrix, matSolve, matSolveCramer } from '../linalg/matrix.js';

// ---------------------------------------------------------------- small helpers

const T = (ru, en = ru) => ({ ru, en });
/** {ru, en} from a function of the language; a plain string when both agree. */
const byLang = (f) => {
    const ru = f('ru');
    const en = f('en');
    return ru === en ? ru : { ru, en };
};
const pick = (x, lang) => (typeof x === 'string' ? x : x?.[lang] ?? '');
const tex = (node, lang = 'ru', o = {}) => toTex(node, { ...o, lang });
const texB = (node, o = {}) => byLang((l) => tex(node, l, o));

function S(title, o = {}) {
    const s = mkStep({ title, tex: o.tex, text: o.text, rule: o.rule, sub: o.sub });
    if (o.final) s.final = true;
    return s;
}

const N0 = num(0);
const N1 = num(1);
const PI = sym('pi');
const qn = (q) => num(Q.of(q));

/** Simplify without throwing (null on failure). */
function simp(node, opts) {
    try {
        return simplify(node, opts);
    } catch {
        return null;
    }
}

/** Simplify, falling back to the node itself. */
function simpOr(node, opts) {
    return simp(node, opts) ?? node;
}

/** Expanded canonical form (null on failure). */
function expd(node, opts) {
    try {
        return expand(node, opts);
    } catch {
        return null;
    }
}

/** Real numeric value (NaN on failure). */
function approxOf(node, env = {}) {
    try {
        const x = evaluate(node, env);
        return typeof x === 'number' ? x : NaN;
    } catch {
        return NaN;
    }
}

/** Complex value {re, im} (null on failure). */
function approxC(node, env = {}) {
    try {
        const z = evaluate(node, env, { complex: true });
        return z && Number.isFinite(z.re) && Number.isFinite(z.im) ? { re: z.re, im: z.im } : null;
    } catch {
        return null;
    }
}

/** true / false when a constant expression is exactly zero or not, null when unknown. */
function exactZero(node, opts) {
    for (const f of [simp, expd]) {
        const s = f(node, opts);
        if (s && s.type === 'num') return s.value.isZero();
    }
    return null;
}

const close = (a, b, tol = 1e-9) => Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b));

/** Is the node free of letters (a constant, possibly with π, e, √)? */
const isConstNode = (n) => freeVars(n).length === 0;

/** Round a double to a short decimal node (for approximate roots); it prints as a decimal (2{,}0946), not a fraction. */
function approxNode(x, digits = 6, decimal = true) {
    if (!Number.isFinite(x) || Math.abs(x) < 1e-12) return num(0);
    const s = Number(x.toPrecision(digits)).toString();
    try {
        return num(Q.of(s), decimal && /^-?\d+\.\d+$/.test(s) ? s : undefined);
    } catch {
        return num(Q.of(Math.round(x * 1e6) / 1e6));
    }
}

/** A short decimal for showing an approximate value inside a substitution: 4 decimals (like approxTex), a real minus. */
function approxShowNode(x) {
    if (!Number.isFinite(x)) return num(0);
    const a = Math.abs(x);
    const s = a !== 0 && (a < 1e-3 || a >= 1e15) ? Number(a.toPrecision(5)).toString() : Number(a.toFixed(4)).toString();
    const node = /^\d+(\.\d+)?$/.test(s) ? num(Q.of(s), s.includes('.') ? s : undefined) : approxNode(a, 5);
    return x < 0 && !(node.type === 'num' && node.value.isZero()) ? neg(node) : node;
}
const approxShowComplex = (z) => {
    if (Math.abs(z.im) < 1e-12) return approxShowNode(z.re);
    const im = Math.abs(z.im);
    const imNode = Math.abs(im - 1) < 5e-5 ? sym('i') : mul(approxShowNode(im), sym('i'));
    const imPart = z.im < 0 ? neg(imNode) : imNode;
    return Math.abs(z.re) < 5e-5 ? imPart : add(approxShowNode(z.re), imPart);
};

/** Σ|terms| of a side at the root (the scale for a numeric «= 0»: 735134400x⁵ − x − 735134400 cancels to ~1e-6). */
function termScale(node, complex) {
    const terms = node.type === 'add' ? node.args : [node];
    let s = 0;
    for (const t of terms) {
        const val = complex ? approxC(t) : approxOf(t);
        const m = complex ? (val ? Math.hypot(val.re, val.im) : NaN) : Math.abs(val);
        if (Number.isFinite(m)) s += m;
    }
    return s;
}

/** Number TeX for approximate values: 1{,}2346 in RU, 1.2346 in EN. */
function approxTex(x, lang, digits = 4) {
    if (!Number.isFinite(x)) return '\\text{—}';
    let s = Number(x.toFixed(digits)).toString();
    if (s === '-0') s = '0';
    if (/e/.test(s)) s = x.toExponential(3);
    return lang === 'ru' ? s.replace('.', '{,}') : s;
}

const sq = (n) => fn('sqrt', n);

/** gcd of two rationals: gcd(p₁q₂, p₂q₁)/(q₁q₂). */
const qGcd = (a, b) => new Q(bigGcd(a.n * b.d, b.n * a.d), a.d * b.d);

/** TeX of a rational in brackets when negative (for substitutions): (-5), \left(-\frac{1}{2}\right). */
function parQ(q, lang = 'ru') {
    const t = tex(num(q), lang);
    if (!q.isNeg()) return t;
    return q.isInt() ? `(${t})` : `\\left(${t}\\right)`;
}

// ---------------------------------------------------------------- IntervalSet

const INF_TEX = { lo: '-\\infty', hi: '+\\infty' };

/** Endpoint {node, x, q}: exact node, its double value and, when rational, its exact Q. */
function endOf(v) {
    if (v && typeof v === 'object' && 'node' in v && 'x' in v) return v;
    let node;
    if (v && typeof v === 'object' && typeof v.type === 'string') node = v;
    else if (v instanceof Q || typeof v === 'bigint') node = num(v);
    else if (typeof v === 'number') node = Number.isInteger(v) ? num(v) : approxNode(v, 12, false);
    else if (typeof v === 'string') node = parse(v);
    else throw new TypeError('bad interval endpoint');
    const s = simp(node) ?? node;
    const q = numValue(s);
    return Object.freeze({ node: q ? num(q) : s, x: q ? q.toNumber() : approxOf(s), q: q ?? null });
}

function cmpEnd(a, b) {
    if (a.q && b.q) return a.q.cmp(b.q);
    const d = a.x - b.x;
    if (Math.abs(d) <= 1e-10 * Math.max(1, Math.abs(a.x), Math.abs(b.x))) {
        if (a.node && b.node && Math.abs(d) > 0) {
            const z = exactZero(add(a.node, neg(b.node)));
            if (z === false) return d < 0 ? -1 : 1;
        }
        return 0;
    }
    return d < 0 ? -1 : 1;
}

// lo/hi: endpoint or null (−∞ / +∞)
const cmpLo = (a, b) => (a === null ? (b === null ? 0 : -1) : b === null ? 1 : cmpEnd(a, b));
const cmpHi = (a, b) => (a === null ? (b === null ? 0 : 1) : b === null ? -1 : cmpEnd(a, b));
// a lower end against an upper end
const cmpLoHi = (lo, hi) => (lo === null || hi === null ? -1 : cmpEnd(lo, hi));

function partEmpty(p) {
    if (p.lo === null || p.hi === null) return false;
    const c = cmpEnd(p.lo, p.hi);
    return c > 0 || (c === 0 && !(p.loC && p.hiC));
}

function normalizeParts(parts) {
    const ps = parts.filter((p) => !partEmpty(p)).map((p) => ({ ...p, loC: p.lo === null ? false : !!p.loC, hiC: p.hi === null ? false : !!p.hiC }));
    ps.sort((a, b) => cmpLo(a.lo, b.lo) || (a.loC === b.loC ? 0 : a.loC ? -1 : 1));
    const out = [];
    for (const p of ps) {
        const cur = out[out.length - 1];
        if (cur) {
            const c = cmpLoHi(p.lo, cur.hi);
            if (cur.hi === null || c < 0 || (c === 0 && (cur.hiC || p.loC))) {
                const h = cmpHi(p.hi, cur.hi);
                if (h > 0) {
                    cur.hi = p.hi;
                    cur.hiC = p.hiC;
                } else if (h === 0) cur.hiC = cur.hiC || p.hiC;
                if (cmpLo(p.lo, cur.lo) === 0) cur.loC = cur.loC || p.loC;
                continue;
            }
        }
        out.push({ ...p });
    }
    return out.map((p) => Object.freeze(p));
}

function isPointPart(p) {
    return p.lo !== null && p.hi !== null && cmpEnd(p.lo, p.hi) === 0;
}

/**
 * A union of intervals of the real line with open/closed ends, ±∞ and isolated points ([a; a]).
 * Endpoints are exact nodes with a double value; parts are sorted, disjoint and merged.
 * parts: [{lo, hi, loC, hiC}] with lo/hi = {node, x, q} or null for −∞ / +∞.
 */
export class IntervalSet {
    constructor(parts = []) {
        this.parts = Object.freeze(normalizeParts(parts));
        Object.freeze(this);
    }

    static empty() {
        return new IntervalSet([]);
    }

    static all() {
        return new IntervalSet([{ lo: null, hi: null, loC: false, hiC: false }]);
    }

    /** Interval between a and b (null = infinity) with closed flags; ends: node, Q, number or text. */
    static interval(a, b, loClosed = false, hiClosed = false) {
        return new IntervalSet([{ lo: a === null ? null : endOf(a), hi: b === null ? null : endOf(b), loC: !!loClosed, hiC: !!hiClosed }]);
    }

    static point(a) {
        const e = endOf(a);
        return new IntervalSet([{ lo: e, hi: e, loC: true, hiC: true }]);
    }

    static points(list) {
        return new IntervalSet(list.map((a) => {
            const e = endOf(a);
            return { lo: e, hi: e, loC: true, hiC: true };
        }));
    }

    /** x < a (closed: x ≤ a). */
    static below(a, closed = false) {
        return IntervalSet.interval(null, a, false, closed);
    }

    /** x > a (closed: x ≥ a). */
    static above(a, closed = false) {
        return IntervalSet.interval(a, null, closed, false);
    }

    union(other) {
        return new IntervalSet([...this.parts, ...other.parts]);
    }

    intersect(other) {
        const out = [];
        for (const a of this.parts) {
            for (const b of other.parts) {
                const cl = cmpLo(a.lo, b.lo);
                const ch = cmpHi(a.hi, b.hi);
                const lo = cl >= 0 ? a.lo : b.lo;
                const loC = cl > 0 ? a.loC : cl < 0 ? b.loC : a.loC && b.loC;
                const hi = ch <= 0 ? a.hi : b.hi;
                const hiC = ch < 0 ? a.hiC : ch > 0 ? b.hiC : a.hiC && b.hiC;
                out.push({ lo, hi, loC, hiC });
            }
        }
        return new IntervalSet(out);
    }

    complement() {
        if (!this.parts.length) return IntervalSet.all();
        const out = [];
        let prev = null;
        for (const p of this.parts) {
            if (prev === null) {
                if (p.lo !== null) out.push({ lo: null, hi: p.lo, loC: false, hiC: !p.loC });
            } else out.push({ lo: prev.hi, hi: p.lo, loC: !prev.hiC, hiC: !p.loC });
            prev = p;
            if (p.hi === null) return new IntervalSet(out);
        }
        out.push({ lo: prev.hi, hi: null, loC: !prev.hiC, hiC: false });
        return new IntervalSet(out);
    }

    minus(other) {
        return this.intersect(other.complement());
    }

    isEmpty() {
        return this.parts.length === 0;
    }

    isAll() {
        return this.parts.length === 1 && this.parts[0].lo === null && this.parts[0].hi === null;
    }

    /** Only isolated points (a finite set)? */
    isFinite() {
        return this.parts.every(isPointPart);
    }

    /** Isolated points (endpoints {node, x, q} of degenerate parts). */
    get pointList() {
        return this.parts.filter(isPointPart).map((p) => p.lo);
    }

    /** Does the set contain x (a number, or a node / Q / text)? */
    contains(x) {
        const e = typeof x === 'number' ? { node: null, x, q: null } : endOf(x);
        const cmp = (a, b) => (a.node && b.node ? cmpEnd(a, b) : Math.abs(a.x - b.x) <= 1e-12 * Math.max(1, Math.abs(a.x)) ? 0 : a.x < b.x ? -1 : 1);
        return this.parts.some((p) => {
            const lo = p.lo === null ? -1 : cmp(p.lo, e);
            const hi = p.hi === null ? 1 : cmp(p.hi, e);
            return (lo < 0 || (lo === 0 && p.loC)) && (hi > 0 || (hi === 0 && p.hiC));
        });
    }

    equals(other, tol = 1e-9) {
        other = other instanceof IntervalSet ? other : parseIntervalSet(String(other));
        if (this.parts.length !== other.parts.length) return false;
        const eq = (a, b) => (a === null || b === null ? a === b : a.q && b.q ? a.q.eq(b.q) : Math.abs(a.x - b.x) <= tol * Math.max(1, Math.abs(a.x)));
        return this.parts.every((p, k) => {
            const o = other.parts[k];
            return eq(p.lo, o.lo) && eq(p.hi, o.hi) && p.loC === o.loC && p.hiC === o.hiC;
        });
    }

    toTex(lang = 'ru') {
        return intervalTex(this, lang);
    }

    toText(lang = 'ru') {
        return intervalText(this, lang);
    }

    toJSON() {
        return this.parts.map((p) => ({
            lo: p.lo === null ? '-inf' : toText(p.lo.node, { lang: 'en' }),
            hi: p.hi === null ? '+inf' : toText(p.hi.node, { lang: 'en' }),
            loClosed: p.loC,
            hiClosed: p.hiC,
        }));
    }
}

function setPieces(set, endTex, inf, sep, empty, cup, braces) {
    if (set.isEmpty()) return empty;
    const out = [];
    let pts = [];
    const flush = () => {
        if (pts.length) out.push(braces(pts.join(sep)));
        pts = [];
    };
    for (const p of set.parts) {
        if (isPointPart(p)) {
            pts.push(endTex(p.lo));
            continue;
        }
        flush();
        const a = p.lo === null ? inf.lo : endTex(p.lo);
        const b = p.hi === null ? inf.hi : endTex(p.hi);
        out.push(`${p.loC ? '[' : '('}${a}${sep}${b}${p.hiC ? ']' : ')'}`);
    }
    flush();
    return out.join(cup);
}

/** TeX of a set: (-\infty;\,2] \cup (3;\,+\infty) in RU, (-\infty, 2] \cup (3, +\infty) in EN; \varnothing. */
export function intervalTex(set, lang = 'ru') {
    return setPieces(set, (e) => tex(e.node, lang, e.approx ? { decimals: true } : {}), INF_TEX, lang === 'ru' ? ';\\,' : ',\\ ', '\\varnothing', ' \\cup ', (s) => `\\{${s}\\}`);
}

/** Plain text of a set: (-∞; 2] ∪ (3; +∞) in RU, (-∞, 2] ∪ (3, +∞) in EN; ∅. */
export function intervalText(set, lang = 'ru') {
    return setPieces(set, (e) => (e.approx ? String(Number(e.x.toFixed(5))).replace('.', lang === 'ru' ? ',' : '.') : toText(e.node, { lang })), { lo: '-∞', hi: '+∞' }, lang === 'ru' ? '; ' : ', ', '∅', ' ∪ ', (s) => `{${s}}`);
}

// ---------------------------------------------------------------- reading sets typed by people

const SET_ERR = (text) => new MathError({ ru: `Не удалось прочитать множество «${text}»`, en: `Could not read the set "${text}"` }, 0, String(text).length, 'interval');
const INF_RE = /^([+-]?)\s*(?:∞|inf|infty|infinity|oo|бесконечность)$/i;

function readEnd(s, v) {
    const t = s.trim().replace(/[−–—]/g, '-');
    const m = INF_RE.exec(t);
    if (m) return m[1] === '-' ? '-inf' : '+inf';
    let node;
    try {
        node = parse(t, { vars: v ? [v] : [] });
    } catch {
        throw SET_ERR(s);
    }
    if (!isConstNode(node)) throw SET_ERR(s);
    const e = endOf(node);
    if (!Number.isFinite(e.x)) throw SET_ERR(s);
    return e;
}

function splitPair(inner, lang) {
    if (inner.includes(';')) return inner.split(';');
    const commas = [...inner.matchAll(/,/g)].map((m) => m.index);
    if (commas.length === 1) return [inner.slice(0, commas[0]), inner.slice(commas[0] + 1)];
    if (/,\s/.test(inner)) {
        const k = inner.search(/,\s/);
        return [inner.slice(0, k), inner.slice(k + 1)];
    }
    if (lang === 'en' || commas.length !== 3) return inner.split(',');
    return [inner.slice(0, commas[1]), inner.slice(commas[1] + 1)]; // 1,5,2,5 in RU
}

function relToSet(op, e) {
    switch (op) {
        case '<':
            return IntervalSet.below(e, false);
        case '<=':
            return IntervalSet.below(e, true);
        case '>':
            return IntervalSet.above(e, false);
        case '>=':
            return IntervalSet.above(e, true);
        case '=':
            return IntervalSet.point(e);
        case '!=':
            return IntervalSet.point(e).complement();
        default:
            return null;
    }
}

const FLIP = { '<': '>', '>': '<', '<=': '>=', '>=': '<=', '=': '=', '!=': '!=' };

function sideEnd(node) {
    const s = simp(node) ?? node;
    if (s.type === 'sym' && s.name === 'inf' && !s.var) return '+inf';
    if (s.type === 'mul' && s.args.length === 2 && s.args[0].type === 'num' && s.args[0].value.isNeg() && s.args[1].type === 'sym' && s.args[1].name === 'inf') return '-inf';
    if (!isConstNode(node) || nodeSome(s, (n) => n.type === 'sym' && n.name === 'inf')) return null;
    const e = endOf(node);
    return Number.isFinite(e.x) ? e : null;
}

function setFromRelation(node, v, piece) {
    const isV = (n) => n.type === 'sym' && n.name === v;
    const one = (op, a, b) => {
        if (isV(a)) {
            const e = sideEnd(b);
            if (e === null) throw SET_ERR(piece);
            if (e === '+inf') return op === '<' || op === '<=' || op === '!=' ? IntervalSet.all() : IntervalSet.empty();
            if (e === '-inf') return op === '>' || op === '>=' || op === '!=' ? IntervalSet.all() : IntervalSet.empty();
            return relToSet(op, e);
        }
        if (isV(b)) return one(FLIP[op], b, a);
        throw SET_ERR(piece);
    };
    if (node.type === 'rel') return one(node.op, node.lhs, node.rhs);
    if (node.type === 'chain') {
        let set = IntervalSet.all();
        for (let k = 0; k < node.ops.length; k++) {
            const a = node.items[k];
            const b = node.items[k + 1];
            if (!isV(a) && !isV(b)) throw SET_ERR(piece);
            set = set.intersect(one(node.ops[k], a, b));
        }
        return set;
    }
    if (node.type === 'list') {
        let set = IntervalSet.empty();
        for (const it of node.items) set = set.union(setFromRelation(it, v, piece));
        return set;
    }
    throw SET_ERR(piece);
}

function readPiece(piece, lang, v) {
    let s = piece.trim();
    if (!s) throw SET_ERR(piece);
    s = s.replace(new RegExp(`^${v}\\s*(?:∈|\\\\in\\b|in\\b)\\s*`, 'i'), '').trim();
    const low = s.toLowerCase();
    if (/^(∅|ø|\\varnothing|\\emptyset|\{\s*\}|нет решений|нет корней|решений нет|корней нет|no solutions?|no roots|none|empty)$/.test(low)) return IntervalSet.empty();
    if (/^(r|ℝ|все|любое|любое число|x\s*[-—–]\s*любое(\s+число)?|all|any|all reals?|all real numbers|\(\s*-\s*∞\s*[;,]\s*\+?\s*∞\s*\))$/.test(low)) return IntervalSet.all();
    // {a; b; c}
    const br = /^\\?\{(.*?)\\?\}$/.exec(s);
    if (br) {
        const inner = br[1];
        const items = inner.includes(';') ? inner.split(';') : lang === 'en' || /,\s/.test(inner) ? inner.split(/,\s*/) : [inner];
        return IntervalSet.points(items.filter((x) => x.trim()).map((x) => {
            const e = readEnd(x, v);
            if (typeof e === 'string') throw SET_ERR(piece);
            return e;
        }));
    }
    // (a; b], [a, b) …
    const iv = /^([([])(.*)([)\]])$/.exec(s);
    if (iv) {
        const parts = splitPair(iv[2], lang);
        if (parts.length !== 2) throw SET_ERR(piece);
        const a = readEnd(parts[0], v);
        const b = readEnd(parts[1], v);
        if (a === '+inf' || b === '-inf') throw SET_ERR(piece);
        return IntervalSet.interval(a === '-inf' ? null : a, b === '+inf' ? null : b, a !== '-inf' && iv[1] === '[', b !== '+inf' && iv[3] === ']');
    }
    // inequalities: x < 2, -1 < x <= 3, 2 > x, x != 1, x = 3
    let node;
    try {
        node = parse(s.replace(/\\leq?(?![a-z])/g, '<=').replace(/\\geq?(?![a-z])/g, '>=').replace(/\\neq?(?![a-z])/g, '!=').replace(/∞/g, 'inf'), { vars: [v] });
    } catch {
        throw SET_ERR(piece);
    }
    return setFromRelation(node, v, piece);
}

/**
 * Read a set typed as an answer: "(-∞; 2] ∪ (3; +∞)", "(-inf, 2] U (3, +inf)", "[1, 3)" (EN), "[1; 3)",
 * "{1; 2}", "x < 2", "-1 < x <= 3", "x < 2 или x > 3", "x ≠ 1", "∅", "R". Throws MathError('interval').
 */
export function parseIntervalSet(text, lang = 'ru', v = 'x') {
    if (text instanceof IntervalSet) return text;
    if (typeof text !== 'string' || !text.trim()) throw SET_ERR(text ?? '');
    let s = text.trim()
        .replace(/\$/g, '')
        .replace(/\\left|\\right|\\!/g, '')
        .replace(/\\[,;: ]/g, ' ')
        .replace(/[−–—]/g, '-')
        .replace(/\\infty|∞/g, '∞')
        .replace(/\\cup/g, '∪')
        .replace(/≤/g, '<=').replace(/≥/g, '>=').replace(/≠/g, '!=')
        .replace(/\\mathbb\s*\{?R\}?/g, 'ℝ');
    // union words and a Latin U between brackets
    s = s.replace(/\s+(?:или|or)\s+/gi, ' ∪ ').replace(/([)\]}])\s*[Uu]\s*(?=[([{\\])/g, '$1 ∪ ');
    let pieces = s.split('∪');
    // "x < -1; x > 3" — alternatives written with a separator
    if (pieces.length === 1 && !/^[([{\\]/.test(s) && /[<>=]/.test(s)) {
        const alt = s.split(lang === 'en' ? /[;,]\s*(?=[a-zA-Z\d(-])/ : /;\s*/);
        if (alt.length > 1 && alt.every((a) => new RegExp(`(^|[^a-zA-Z])${v}($|[^a-zA-Z])`).test(a))) pieces = alt;
    }
    let set = IntervalSet.empty();
    for (const p of pieces) set = set.union(readPiece(p, lang, v));
    return set;
}

/** Same set? a, b: IntervalSet or text (read with parseIntervalSet in `lang`). */
export function intervalEquals(a, b, lang = 'ru', tol = 1e-9) {
    try {
        const A = a instanceof IntervalSet ? a : parseIntervalSet(a, lang);
        const B = b instanceof IntervalSet ? b : parseIntervalSet(b, lang);
        return A.equals(B, tol);
    } catch {
        return false;
    }
}

// ---------------------------------------------------------------- ОДЗ (the domain of an equation)

// A condition: {kind: 'ne0' | 'ge0' | 'gt0' | 'cos' | 'sin', expr, why}; for 'cos'/'sin' expr is the argument u
// and the condition reads cos u ≠ 0 (tg, sec) or sin u ≠ 0 (ctg, cosec).
const RANK = { ne0: 1, ge0: 2, gt0: 3 };

function collectConds(node, v) {
    const out = [];
    const byKey = new Map();
    const push = (kind, expr, why) => {
        if (!containsVar(expr, v)) return;
        const e = simpOr(expr);
        if (!containsVar(e, v)) return;
        const key = (kind === 'cos' || kind === 'sin' ? kind : 'r') + nodeKey(e);
        const prev = byKey.get(key);
        if (prev) {
            if (prev.kind === kind || kind === 'cos' || kind === 'sin') return;
            prev.kind = (prev.kind === 'ne0' && kind === 'ge0') || (prev.kind === 'ge0' && kind === 'ne0') ? 'gt0' : RANK[kind] > RANK[prev.kind] ? kind : prev.kind;
            prev.whys.add(why);
            return;
        }
        const c = { kind, expr: e, whys: new Set([why]) };
        byKey.set(key, c);
        out.push(c);
    };
    const walk = (n) => {
        if (n.type === 'div' && containsVar(n.den, v)) push('ne0', n.den, 'den');
        else if (n.type === 'pow' && containsVar(n.base, v)) {
            const q = numValue(n.exp);
            if (q) {
                // a typed fractional power a^(m/n) is defined for a ≥ 0 (a > 0 when negative) — the RU school rule;
                // odd roots of negatives are written as roots: root(x, 3), cbrt(x)
                const even = q.d % 2n === 0n;
                if (!q.isInt()) push(q.isNeg() ? 'gt0' : 'ge0', n.base, even ? 'root' : 'powfrac');
                else if (q.isNeg()) push('ne0', n.base, 'den');
            } else push('gt0', n.base, 'powbase');
        } else if (n.type === 'fn') {
            const a = n.args;
            switch (n.name) {
                case 'sqrt':
                    push('ge0', a[0], 'root');
                    break;
                case 'root': {
                    const k = numValue(a[1]);
                    if (k && k.isInt() && k.n % 2n === 0n) push('ge0', a[0], 'root');
                    break;
                }
                case 'ln':
                case 'lg':
                    push('gt0', a[0], 'log');
                    break;
                case 'log':
                    push('gt0', a[1], 'log');
                    if (containsVar(a[0], v)) {
                        push('gt0', a[0], 'logbase');
                        push('ne0', add(a[0], num(-1)), 'logbase');
                    }
                    break;
                case 'tan':
                case 'sec':
                    push('cos', a[0], 'tan');
                    break;
                case 'cot':
                case 'csc':
                    push('sin', a[0], 'cot');
                    break;
                case 'asin':
                case 'acos':
                    push('ge0', add(num(1), neg(a[0])), 'arc');
                    push('ge0', add(a[0], num(1)), 'arc');
                    break;
                default:
                    break;
            }
        }
        for (const c of nodeChildren(n)) walk(c);
    };
    walk(node);
    return out;
}

const COND_OP = { ne0: '\\ne', ge0: '\\ge', gt0: '>' };

function condTex(c, lang) {
    if (c.kind === 'cos' || c.kind === 'sin') return `${tex(fn(c.kind, c.expr), lang)} \\ne 0`;
    return `${tex(c.expr, lang)} ${COND_OP[c.kind]} 0`;
}

const WHY = {
    den: T('знаменатель не равен нулю', 'a denominator is not zero'),
    root: T('под корнем чётной степени — неотрицательное число', 'an even root needs a non-negative radicand'),
    log: T('под логарифмом — положительное число', 'a logarithm needs a positive argument'),
    logbase: T('основание логарифма положительно и не равно 1', 'the base of a logarithm is positive and not 1'),
    powbase: T('основание степени с переменным показателем положительно', 'a power with a variable exponent needs a positive base'),
    powfrac: T('степень с дробным показателем определена для неотрицательного основания', 'a power with a fractional exponent needs a non-negative base'),
    tan: T('тангенс определён, когда косинус не равен нулю', 'the tangent needs a non-zero cosine'),
    cot: T('котангенс определён, когда синус не равен нулю', 'the cotangent needs a non-zero sine'),
    arc: T('аргумент арксинуса и арккосинуса лежит в $[-1; 1]$', 'arcsin and arccos need an argument in $[-1, 1]$'),
};

/** Does the condition hold at the root {node, approx}? */
function condHolds(c, v, root) {
    const x = root.approx;
    if (typeof x !== 'number' || !Number.isFinite(x)) return true; // complex roots: no real domain
    if (c.kind === 'cos' || c.kind === 'sin') {
        const u = approxOf(c.expr, { [v]: x });
        const val = c.kind === 'cos' ? Math.cos(u) : Math.sin(u);
        // near a zero of cos/sin the rounding of u is what is left: cos(arctg 10¹⁰) = 10⁻¹⁰ is not zero
        if (Math.abs(val) > 64 * Number.EPSILON * Math.max(1, Math.abs(u))) return true;
        if (root.node && !root.approxOnly) {
            const z = exactZero(fn(c.kind, substitute(c.expr, { [v]: root.node })));
            if (z === false) return true;
        }
        return false;
    }
    const val = approxOf(c.expr, { [v]: x });
    if (!Number.isFinite(val)) return false;
    let zero = Math.abs(val) <= 1e-10 * Math.max(1, Math.abs(x));
    if (zero && root.node && !root.approxOnly && Math.abs(val) > 0) {
        const z = exactZero(substitute(c.expr, { [v]: root.node }));
        if (z === false) zero = false;
    }
    if (c.kind === 'ne0') return !zero;
    if (c.kind === 'ge0') return zero || val > 0;
    return !zero && val > 0;
}

/** Value of a substituted side for display: an exact node when it simplifies, else null. */
function sideValue(node, complex = false) {
    const co = complex ? { complex: true } : undefined;
    const s = simp(node, co);
    if (!s) return null;
    if (s.type === 'num') return s;
    const e = expd(node, co);
    if (e && e.type === 'num') return e;
    return e && nodeSizeOf(e) < nodeSizeOf(s) ? e : s;
}

function nodeSizeOf(n) {
    let k = 1;
    for (const c of nodeChildren(n)) k += nodeSizeOf(c);
    return k;
}

const REL_TEX = { '=': '=', '<': '<', '>': '>', '<=': '\\le', '>=': '\\ge', '!=': '\\ne' };
const NOT_REL_TEX = { '=': '\\ne', '<': '\\ge', '>': '\\le', '<=': '>', '>=': '<', '!=': '=' };

function relHoldsNum(op, a, b) {
    const eq = close(a, b, 1e-9);
    switch (op) {
        case '=':
            return eq;
        case '!=':
            return !eq;
        case '<':
            return a < b && !eq;
        case '<=':
            return a < b || eq;
        case '>':
            return a > b && !eq;
        case '>=':
            return a > b || eq;
        default:
            return false;
    }
}

/**
 * Substitution check of one value. → {ok, defined, exact, lhs, rhs (value nodes or null), lhsApprox, rhsApprox,
 * reason: null | 'odz' | 'undefined' | 'mismatch', tex, text, steps}.
 */
function checkRel(r, v, root, opts = {}) {
    const conds = opts.conds ?? collectConds(r, v);
    const val = root.approxOnly ? (typeof root.approx === 'number' ? approxNode(root.approx, 16) : complexApproxNode(root.approx.re, root.approx.im)) : root.node;
    const complex = !!opts.complex;
    const Ls = substitute(r.lhs, { [v]: val });
    const Rs = substitute(r.rhs, { [v]: val });
    // what the reader sees for a numeric root: a short decimal (2{,}0946), not the 16-digit fraction we compute with
    const shownVal = root.approxOnly ? (typeof root.approx === 'number' ? approxShowNode(root.approx) : approxShowComplex(root.approx)) : null;
    const LsD = shownVal ? substitute(r.lhs, { [v]: shownVal }) : Ls;
    const RsD = shownVal ? substitute(r.rhs, { [v]: shownVal }) : Rs;
    let l;
    let rr;
    let defined;
    if (complex) {
        l = approxC(Ls);
        rr = approxC(Rs);
        defined = !!(l && rr);
    } else {
        l = approxOf(Ls);
        rr = approxOf(Rs);
        defined = Number.isFinite(l) && Number.isFinite(rr);
    }
    const inDomain = complex || conds.every((c) => condHolds(c, v, { node: val, approx: typeof root.approx === 'number' ? root.approx : approxOf(val), approxOnly: root.approxOnly }));
    let exact = false;
    let ok = false;
    let lv = null;
    let rv = null;
    if (defined && inDomain) {
        lv = root.approxOnly ? null : sideValue(Ls, complex);
        rv = root.approxOnly ? null : sideValue(Rs, complex);
        const dz = root.approxOnly ? null : exactZero(add(Ls, neg(Rs)), complex ? { complex: true } : undefined);
        if (r.op === '=') {
            if (dz === true) {
                ok = true;
                exact = true;
            } else if (dz === false) ok = false;
            else {
                // numerically, relative to the size of the terms (they may cancel: 735134400x⁵ − x − 735134400)
                const scale = Math.max(1, termScale(Ls, complex), termScale(Rs, complex));
                ok = complex ? Math.hypot(l.re - rr.re, l.im - rr.im) <= 1e-8 * Math.max(scale, Math.hypot(l.re, l.im)) : Math.abs(l - rr) <= 1e-8 * Math.max(scale, Math.abs(l), Math.abs(rr)) + roundingSpread(r, v, root.approx);
            }
        } else if (!complex) {
            const lq = lv && numValue(lv);
            const rq = rv && numValue(rv);
            if (lq && rq) {
                exact = true;
                const c = lq.cmp(rq);
                ok = { '<': c < 0, '<=': c <= 0, '>': c > 0, '>=': c >= 0, '!=': c !== 0 }[r.op] ?? false;
            } else ok = relHoldsNum(r.op, l, rr);
        }
    }
    const reason = ok ? null : !inDomain ? 'odz' : !defined ? 'undefined' : 'mismatch';
    const texL = (lang) => {
        const big = nodeSizeOf(LsD) > 40;
        const shown = (sub, value, approx, side) => {
            const parts = [];
            if (!big) parts.push(tex(sub, lang));
            if (value) {
                const vt = tex(value, lang);
                if (!parts.length || parts[parts.length - 1] !== vt) parts.push(vt);
            } else if (root.approxOnly && !containsVar(side, v) && numValue(side)) {
                // a plain number on this side: nothing to approximate (… ≈ 0, not «0 ≈ 0»)
                if (big) parts.push(tex(side, lang));
            } else if (typeof approx === 'number' && Number.isFinite(approx)) parts.push(`\\approx ${approxTex(approx, lang)}`);
            else if (root.approxOnly && approx && typeof approx === 'object' && Number.isFinite(approx.re) && Number.isFinite(approx.im)) parts.push(`\\approx ${approxComplexTex(approx, lang)}`);
            return parts.join(' = ').replace('= \\approx', '\\approx');
        };
        if (!defined || !inDomain) return tex(rel(r.op, LsD, RsD), lang);
        const left = shown(LsD, lv, complex ? (root.approxOnly ? l : null) : l, r.lhs);
        const right = shown(RsD, rv, complex ? (root.approxOnly ? rr : null) : rr, r.rhs);
        const mark = ok ? '\\ \\checkmark' : '';
        const op = ok ? REL_TEX[r.op] : NOT_REL_TEX[r.op];
        // a constant right side equal to the last value on the left: 2^2 - 5*2 + 6 = 0 ✓, 2{,}0946^{3} - … \approx 0 ✓
        if (ok && r.op === '=' && !containsVar(r.rhs, v) && (left.endsWith(' = ' + right) || left.endsWith('\\approx ' + right))) return `${left}${mark}`;
        if (ok && r.op === '=' && !containsVar(r.rhs, v) && left === right) return `${left}${mark}`;
        return `${left} \\,${op}\\, ${right}${mark}`;
    };
    const texOut = byLang(texL);
    const valTex = (lang) => (root.approxOnly
        ? `${v} \\approx ${typeof root.approx === 'number' ? approxTex(root.approx, lang) : approxComplexTex(root.approx, lang)}`
        : `${v} = ${tex(val, lang)}`);
    const text = ok
        ? T('Верное равенство — корень подходит.', 'A true equality: the root fits.')
        : reason === 'odz'
            ? T('Значение не входит в ОДЗ — выражение не имеет смысла, это посторонний корень.', 'The value is outside the domain, the expression makes no sense there: an extraneous root.')
            : reason === 'undefined'
                ? T('При этом значении выражение не имеет смысла — посторонний корень.', 'The expression is not defined at this value: an extraneous root.')
                : T('Равенство неверно — это посторонний корень.', 'The equality is false: an extraneous root.');
    const ineqText = r.op !== '=' ? (ok ? T('Неравенство верно.', 'The inequality holds.') : T('Неравенство неверно.', 'The inequality fails.')) : text;
    return {
        ok,
        defined: defined && inDomain,
        exact,
        reason,
        lhs: lv,
        rhs: rv,
        lhsApprox: l,
        rhsApprox: rr,
        tex: texOut,
        text: ineqText,
        steps: [S(T(`Подставляем $${valTex('ru')}$`, `Substitute $${valTex('en')}$`), { tex: texOut, text: ineqText })],
    };
}

function valueNodeOf(value, v) {
    if (value && typeof value === 'object' && typeof value.type === 'string') return value;
    if (value instanceof Q || typeof value === 'bigint') return num(value);
    if (typeof value === 'number') return Number.isInteger(value) ? num(value) : approxNode(value, 15);
    if (typeof value === 'string') return parse(value, { vars: [v] });
    throw new TypeError('checkRoot: bad value');
}

function asRelation(input, v) {
    const n = typeof input === 'string' ? parse(input, { vars: v ? [v] : [] }) : input;
    if (!n || typeof n.type !== 'string') throw new TypeError('expected a relation');
    return n;
}

/**
 * Substitute value into the relation and check it: checkRoot('sqrt(x+2) = x', 'x', -1) →
 * {ok: false, reason: 'mismatch', lhs, rhs, tex, text, steps}. For inequalities `ok` says whether it holds.
 * value: number, Q, node or text. opts: {complex}.
 */
export function checkRoot(input, v = 'x', value, opts = {}) {
    const r = asRelation(input, v);
    if (r.type !== 'rel') throw new MathError(T('Нужно уравнение или неравенство', 'An equation or an inequality is needed'), null, null, 'not-rel');
    if (typeof value === 'number' && Number.isFinite(value) && !Number.isInteger(value) && Number(value.toPrecision(12)) !== value) {
        // a double like 1.000000000272059 (a numeric root) is an approximation: checked numerically, shown rounded
        return checkRel(r, v, { node: approxNode(value, 16), approx: value, approxOnly: true }, opts);
    }
    const node = valueNodeOf(value, v);
    const approx = opts.complex ? approxC(node) : approxOf(node);
    return checkRel(r, v, { node, approx }, opts);
}

// ---------------------------------------------------------------- roots and their TeX

// Root record: {node, approx: number | {re, im}, mult, minPoly?: Poly, approxOnly?: true, complex?: true}
function mkRoot(node, extra = {}) {
    return { node, approx: approxOf(node), mult: 1, ...extra };
}

const hasI = (n) => nodeSome(n, (x) => x.type === 'sym' && x.name === 'i' && !x.var);

/** A root that may be non-real (complex coefficients): {node, approx: number | {re, im}, complex?}. */
function mkRootC(node) {
    const x = approxOf(node);
    if (Number.isFinite(x)) return mkRoot(node);
    const z = approxC(node);
    if (!z) return mkRoot(node);
    if (Math.abs(z.im) <= 1e-12 * Math.max(1, Math.abs(z.re))) return { node, approx: z.re, mult: 1 };
    return { node, approx: z, mult: 1, complex: true };
}

function qRoot(q, extra = {}) {
    q = Q.of(q);
    return { node: num(q), approx: q.toNumber(), mult: 1, minPoly: new Poly([q.neg(), Q.ONE]), ...extra };
}

function approxComplexTex(z, lang) {
    if (Math.abs(z.im) < 1e-12) return approxTex(z.re, lang);
    const re = Math.abs(z.re) < 1e-12 ? '' : approxTex(z.re, lang);
    const im = approxTex(Math.abs(z.im), lang);
    const sign = z.im < 0 ? '-' : re ? '+' : '';
    return `${re} ${sign} ${im}i`.trim();
}

function rootValueTex(r, lang) {
    if (r.approxOnly) return `\\approx ${r.complex ? approxComplexTex(r.approx, lang) : approxTex(r.approx, lang)}`;
    return `= ${tex(r.node, lang)}`;
}

/** x_1 = 2;\quad x_2 = 3 (one root: x = 2). */
function rootsTex(roots, v, lang, start = 1) {
    if (!roots.length) return lang === 'ru' ? '\\text{корней нет}' : '\\text{no roots}';
    const idx = roots.length > 1;
    return roots.map((r, k) => `${idx ? `${v}_{${k + start}}` : v} ${rootValueTex(r, lang)}`).join(lang === 'ru' ? ';\\quad ' : ',\\quad ');
}

const rootsTexB = (roots, v, start) => byLang((l) => rootsTex(roots, v, l, start));

/** Distinct roots, ascending (complex ones after the real ones); equal roots merge (mult added when sum). */
function mergeRoots(list, sumMult = false) {
    const out = [];
    for (const r of list) {
        const same = out.find((o) => sameRoot(o, r));
        if (same) {
            if (sumMult) same.mult += r.mult;
            else same.mult = Math.max(same.mult, r.mult);
            if (same.approxOnly && !r.approxOnly) Object.assign(same, { node: r.node, approxOnly: undefined });
            continue;
        }
        out.push({ ...r });
    }
    return out.sort(cmpRoots);
}

function cmpRoots(a, b) {
    const ar = typeof a.approx === 'number';
    const br = typeof b.approx === 'number';
    if (ar && br) return a.approx - b.approx;
    if (ar !== br) return ar ? -1 : 1;
    return a.approx.re - b.approx.re || a.approx.im - b.approx.im;
}

function sameRoot(a, b) {
    const ar = typeof a.approx === 'number';
    const br = typeof b.approx === 'number';
    if (ar !== br) return false;
    const near = ar ? close(a.approx, b.approx, 1e-9) : Math.hypot(a.approx.re - b.approx.re, a.approx.im - b.approx.im) <= 1e-9 * Math.max(1, Math.hypot(a.approx.re, a.approx.im));
    if (!near) return false;
    if (a.approxOnly || b.approxOnly) return true;
    const z = exactZero(add(a.node, neg(b.node)), ar ? undefined : { complex: true });
    return z !== false;
}

// ---------------------------------------------------------------- polynomials: helpers

const polyTex = (P, v, lang) => tex(P.toNode(v), lang);
const polyTexB = (P, v) => byLang((l) => polyTex(P, v, l));
const X_POW = (v, k) => (k === 1 ? v : `${v}^{${k}}`);

function multOf(P, m) {
    if (!m || m.degree < 1) return 1;
    let k = 0;
    let cur = P;
    while (cur.degree >= m.degree && k < 64) {
        const { q, r } = cur.divmod(m);
        if (!r.isZero()) break;
        cur = q;
        k++;
    }
    return Math.max(k, 1);
}

/** p(x^m) */
function composeXm(p, m) {
    const c = new Array(p.degree * m + 1).fill(Q.ZERO);
    p.c.forEach((q, k) => {
        c[k * m] = q;
    });
    return new Poly(c);
}

/** Node for (p + sgn·q·√m·[i]) / r with integers (bigint), r > 0. */
function surdNode(p, q, m, r, sgn, imag = false) {
    const f = [];
    if (q !== 1n || (m === 1n && !imag)) f.push(num(q));
    if (imag) f.push(sym('i'));
    if (m !== 1n) f.push(sq(num(m)));
    const term = f.length === 1 ? f[0] : mul(f);
    if (p === 0n) {
        const n = r === 1n ? term : div(term, num(r));
        return sgn < 0 ? neg(n) : n;
    }
    const numer = add(num(p), sgn < 0 ? neg(term) : term);
    return r === 1n ? numer : div(numer, num(r));
}

/** Roots of a·x² + b·x + c = 0 via the formula with exact surds (a, b, c integers, a > 0). */
function quadFormulaRoots(a, b, c) {
    const D = b * b - 4n * a * c;
    if (D === 0n) {
        const q = new Q(-b, 2n * a);
        return { D, real: [qRoot(q)], cplx: [] };
    }
    const { out, in: inn } = rootExtract(D < 0n ? -D : D, 2);
    if (D > 0n && inn === 1n) {
        return { D, real: [qRoot(new Q(-b - out, 2n * a)), qRoot(new Q(-b + out, 2n * a))], cplx: [] };
    }
    const g0 = bigGcd(bigGcd(b < 0n ? -b : b, out), 2n * a);
    const g = g0 === 0n ? 1n : g0;
    const p = -b / g;
    const q = out / g;
    const r = (2n * a) / g;
    const mp = new Poly([new Q(c), new Q(b), new Q(a)]);
    const pr = Number(p) / Number(r);
    const im = (Number(q) * Math.sqrt(Number(inn))) / Number(r);
    if (D > 0n) {
        return { D, real: [-1, 1].map((s) => ({ node: surdNode(p, q, inn, r, s), approx: pr + s * im, mult: 1, minPoly: mp })), cplx: [], p, q, r, inn };
    }
    return { D, real: [], cplx: [-1, 1].map((s) => ({ node: surdNode(p, q, inn, r, s, true), approx: { re: pr, im: s * im }, mult: 1, minPoly: mp, complex: true })), p, q, r, inn };
}

/** Normalisation step text: P = k · Pn. */
function normStep(P, Pn, v) {
    const k = Pn.lead.div(P.lead); // multiply both sides by k
    let title;
    if (k.isInt()) title = k.eq(-1)
        ? T('Умножаем обе части на $-1$', 'Multiply both sides by $-1$')
        : T(`Умножаем обе части на $${tex(num(k))}$`, `Multiply both sides by $${tex(num(k))}$`);
    else if (k.inv().isInt()) title = T(`Делим обе части на $${tex(num(k.inv()))}$`, `Divide both sides by $${tex(num(k.inv()))}$`);
    else title = T(`Умножаем обе части на $${tex(num(k))}$`, `Multiply both sides by $${tex(num(k))}$`);
    const text = !k.isInt() && !k.inv().isInt()
        ? T('Так коэффициенты станут целыми и без общего множителя.', 'This makes the coefficients integers without a common factor.')
        : k.isNeg() && k.abs().isOne()
            ? T('Со старшим коэффициентом больше нуля считать удобнее.', 'A positive leading coefficient is easier to work with.')
            : k.isInt()
                ? T('Так избавимся от дробей.', 'This clears the fractions.')
                : T('Все коэффициенты делятся на это число — уравнение станет проще.', 'All coefficients share this factor, so the equation gets simpler.');
    return S(title, { tex: byLang((l) => `${polyTex(Pn, v, l)} = 0`), text });
}

// ---------------------------------------------------------------- quadratic equations

/** a x² + b x + c = 0 with rational coefficients → {roots, cplx, steps}. */
function quadSolve(P0, ctx) {
    const v = ctx.v;
    const steps = [];
    let P = P0;
    const Pn = P.primitive();
    if (!Pn.equals(P)) {
        steps.push(normStep(P, Pn, v));
        P = Pn;
    }
    const [c, b, a] = [P.coeff(0), P.coeff(1), P.coeff(2)];
    const roots = [];
    const cplx = [];
    const vv = `${v}^{2}`;
    if (c.isZero()) {
        const lin = new Poly([b, a]);
        const r = b.neg().div(a);
        steps.push(S(T(`Неполное квадратное уравнение: выносим $${v}$ за скобки`, `An incomplete quadratic: take $${v}$ out of the brackets`), {
            tex: byLang((l) => `${v}\\left(${polyTex(lin, v, l)}\\right) = 0`),
            text: T('Произведение равно нулю, когда хотя бы один множитель равен нулю, — дискриминант не нужен.', 'A product is zero when one of the factors is zero, so no discriminant is needed.'),
        }));
        const rs = mergeRoots([qRoot(Q.ZERO), qRoot(r)]);
        steps.push(S(T('Корни', 'The roots'), { tex: byLang((l) => `${v} = 0 \\quad ${l === 'ru' ? '\\text{или}' : '\\text{or}'} \\quad ${polyTex(lin, v, l)} = 0 \\;\\Rightarrow\\; ${v} = ${tex(num(r), l)}`) }));
        roots.push(...rs);
        return { roots, cplx, steps };
    }
    if (b.isZero()) {
        const r = c.neg().div(a);
        steps.push(S(T(`Неполное квадратное уравнение: выражаем $${vv}$`, `An incomplete quadratic: solve for $${vv}$`), {
            tex: byLang((l) => `${vv} = ${tex(num(r), l)}`),
        }));
        if (r.isPos()) {
            const s = simpOr(pow(num(r), num(Q.HALF)));
            const sq1 = numValue(s);
            steps.push(S(T('Извлекаем квадратный корень: два корня, равные по модулю', 'Take the square root: two roots of equal size'), {
                tex: byLang((l) => `${v} = \\pm\\sqrt{${tex(num(r), l)}} = \\pm ${tex(s, l)}`),
                text: T(`И $${tex(s)}$, и $${tex(simpOr(neg(s)))}$ в квадрате дают $${tex(num(r))}$.`, `Both $${tex(s)}$ and $${tex(simpOr(neg(s)))}$ squared give $${tex(num(r))}$.`),
            }));
            const mp = sq1 ? null : P;
            roots.push(sq1 ? qRoot(sq1.neg()) : { node: simpOr(neg(s)), approx: -Math.sqrt(r.toNumber()), mult: 1, minPoly: mp });
            roots.push(sq1 ? qRoot(sq1) : { node: s, approx: Math.sqrt(r.toNumber()), mult: 1, minPoly: mp });
        } else {
            const s = simpOr(pow(num(r.neg()), num(Q.HALF)));
            const zi = simpOr(mul(s, sym('i')));
            steps.push(S(T('Квадрат не бывает отрицательным — действительных корней нет', 'A square is never negative, so there are no real roots'), {
                text: T(`В комплексных числах корни есть: $${v} = \\pm ${tex(zi)}$.`, `In complex numbers there are roots: $${v} = \\pm ${tex(zi, 'en')}$.`),
            }));
            const im = Math.sqrt(-r.toNumber());
            cplx.push({ node: simpOr(neg(zi)), approx: { re: 0, im: -im }, mult: 1, minPoly: P, complex: true });
            cplx.push({ node: zi, approx: { re: 0, im }, mult: 1, minPoly: P, complex: true });
        }
        return { roots, cplx, steps };
    }
    const A = a.n;
    const B = b.n;
    const C = c.n;
    const D = B * B - 4n * A * C;
    const b2 = B * B;
    const ac4 = 4n * A * C;
    steps.push(S(T('Квадратное уравнение: выписываем коэффициенты', 'A quadratic equation: read off the coefficients'), {
        tex: byLang((l) => `a = ${tex(num(a), l)},\\quad b = ${tex(num(b), l)},\\quad c = ${tex(num(c), l)}`),
    }));
    steps.push(S(T('Считаем дискриминант', 'Compute the discriminant'), {
        tex: `D = b^2 - 4ac = ${parQ(b)}^{2} - 4 \\cdot ${parQ(a)} \\cdot ${parQ(c)} = ${b2} ${ac4 < 0n ? '+' : '-'} ${ac4 < 0n ? -ac4 : ac4} = ${D}`,
        text: T('Знак дискриминанта говорит, сколько корней: $D > 0$ — два, $D = 0$ — один, $D < 0$ — действительных нет.', 'Its sign tells how many roots there are: $D > 0$ two, $D = 0$ one, $D < 0$ no real ones.'),
    }));
    const f = quadFormulaRoots(A, B, C);
    const mb = tex(num(-B));
    const a2 = `${2n * A}`;
    if (D === 0n) {
        const r = f.real[0];
        steps.push(S(T('$D = 0$ — один корень (два совпавших)', '$D = 0$: one root (a double one)'), {
            tex: `${v} = -\\frac{b}{2a} = \\frac{${mb}}{${a2}} = ${tex(r.node)}`,
        }));
        roots.push(r);
    } else if (D > 0n) {
        let t = `${v}_{1,2} = \\frac{-b \\pm \\sqrt{D}}{2a} = \\frac{${mb} \\pm \\sqrt{${D}}}{${a2}}`;
        if (f.inn === undefined) {
            const s = rootExtract(D, 2).out;
            t = `${v}_{1,2} = \\frac{-b \\pm \\sqrt{D}}{2a} = \\frac{${mb} \\pm ${s}}{${a2}}`;
            steps.push(S(T('$D > 0$ — два корня', '$D > 0$: two roots'), { tex: t }));
            const [r1, r2] = f.real;
            steps.push(S(T('Считаем каждый корень', 'Compute each root'), {
                tex: byLang((l) => `${v}_1 = \\frac{${mb} - ${s}}{${a2}} = ${tex(r1.node, l)};\\quad ${v}_2 = \\frac{${mb} + ${s}}{${a2}} = ${tex(r2.node, l)}`),
            }));
            roots.push(...f.real);
            const qs = numValue(r1.node).add(numValue(r2.node));
            const qp = numValue(r1.node).mul(numValue(r2.node));
            steps.push(S(T('Проверка по теореме Виета', 'Check with Vieta’s formulas'), {
                tex: byLang((l) => `${v}_1 + ${v}_2 = ${tex(num(qs), l)} = -\\frac{b}{a},\\quad ${v}_1 ${v}_2 = ${tex(num(qp), l)} = \\frac{c}{a}`),
                text: T('Сумма корней равна $-\\frac{b}{a}$, произведение равно $\\frac{c}{a}$ — сходится.', 'The sum of the roots is $-\\frac{b}{a}$ and the product is $\\frac{c}{a}$: it matches.'),
            }));
        } else {
            const { out } = rootExtract(D, 2);
            if (out > 1n) t += ` = \\frac{${mb} \\pm ${out}\\sqrt{${f.inn}}}{${a2}}`;
            const [r1, r2] = f.real;
            const reduced = f.r !== 2n * A;
            steps.push(S(T('$D > 0$ — два корня', '$D > 0$: two roots'), {
                tex: t,
                text: out > 1n ? T(`Упрощаем корень: $\\sqrt{${D}} = ${out}\\sqrt{${f.inn}}$.`, `Simplify the root: $\\sqrt{${D}} = ${out}\\sqrt{${f.inn}}$.`) : undefined,
            }));
            steps.push(S(reduced ? T('Сокращаем дробь', 'Reduce the fraction') : T('Корни', 'The roots'), {
                tex: byLang((l) => `${v}_1 = ${tex(r1.node, l)};\\quad ${v}_2 = ${tex(r2.node, l)}`),
            }));
            roots.push(...f.real);
        }
    } else {
        const zs = f.cplx;
        steps.push(S(T('$D < 0$ — действительных корней нет', '$D < 0$: no real roots'), {
            text: T(`Корень из отрицательного числа среди действительных чисел не извлекается. В комплексных числах корни есть: $${v}_{1,2} = ${tex(zs[0].node)}, ${tex(zs[1].node)}$.`,
                `There is no real square root of a negative number. In complex numbers the roots exist: $${v}_{1,2} = ${tex(zs[0].node, 'en')}, ${tex(zs[1].node, 'en')}$.`),
        }));
        cplx.push(...zs);
    }
    return { roots, cplx, steps };
}

// ---------------------------------------------------------------- higher degree

const OR = T('или', 'or');

/** A nested "solve this part" step: the result in the title line, the details inside. */
function partStep(eqTex, res, v) {
    const found = [...res.roots, ...(res.cplx ?? [])];
    return S(byLang((l) => (l === 'ru' ? `Решаем $${pick(eqTex, 'ru')}$` : `Solve $${pick(eqTex, 'en')}$`)), {
        tex: byLang((l) => (res.kind === 'all' ? `${v} \\in \\mathbb{R}` : rootsTex(res.roots, v, l))),
        sub: res.steps,
        text: !res.roots.length && res.cplx?.length ? T('Действительных корней нет.', 'No real roots.') : undefined,
    });
}

/** Push "solve lhs = rhs" as a nested step, unless it is already the answer (x = c). */
function pushPart(steps, lhs, rhs, res, v) {
    if (lhs.type === 'sym' && lhs.name === v && !containsVar(rhs, v) && res.kind === 'roots' && res.roots.length === 1) return;
    steps.push(partStep(byLang((l) => `${tex(lhs, l)} = ${tex(rhs, l)}`), res, v));
}

/** Any polynomial over Q (degree ≥ 1) → {roots, cplx, steps, numeric}. */
function solveAnyPoly(P0, ctx) {
    const v = ctx.v;
    if (P0.degree < 1) return { kind: P0.isZero() ? 'all' : 'none', roots: [], cplx: [], steps: [] };
    const P = P0.primitive();
    const pre = P.equals(P0) ? [] : [normStep(P0, P, v)];
    let res;
    if (P.degree === 1) {
        const r = P.coeff(0).neg().div(P.coeff(1));
        res = {
            roots: [qRoot(r)],
            cplx: [],
            steps: [S(T(`Выражаем $${v}$`, `Solve for $${v}$`), { tex: byLang((l) => `${v} = ${tex(num(r), l)}`) })],
        };
    } else if (P.degree === 2) res = quadSolve(P, ctx);
    else res = highSolve(P, ctx);
    return { kind: 'roots', numeric: false, ...res, steps: [...pre, ...res.steps] };
}

function candidatesOrdered(P) {
    const c = P.rootCandidates();
    const key = new Map(c.map((q) => [q, Math.abs(Number(q.n) / Number(q.d))]));
    return c.sort((a, b) => key.get(a) - key.get(b) || a.abs().cmp(b.abs()) || (a.isNeg() ? 1 : -1));
}

function candidatesTex(cands, lang) {
    const pos = [];
    const seen = new Set();
    for (const c of cands) {
        if (pos.length > 16) break;
        const k = c.toString();
        if (c.isPos() && !seen.has(k)) {
            seen.add(k);
            pos.push(c);
        }
    }
    const shown = pos.slice(0, 16).map((c) => `\\pm ${tex(num(c), lang)}`);
    return shown.join(lang === 'ru' ? ';\\ ' : ',\\ ') + (pos.length > 16 ? ',\\ \\ldots' : '');
}

function hornerTex(P, r, lang) {
    const h = P.horner(r);
    const top = h.top.map((q) => tex(num(q), lang));
    const row = h.row.map((q) => tex(num(q), lang));
    return `\\begin{array}{c|${'c'.repeat(top.length)}} & ${top.join(' & ')} \\\\ \\hline ${tex(num(r), lang)} & ${row.join(' & ')} \\end{array}`;
}

const linFactorNode = (v, r) => (r.isZero() ? sym(v) : add(sym(v), num(r.neg())));

const complexApproxNode = (re, im, digits = 16) => {
    const imPart = mul(approxNode(Math.abs(im), digits), sym('i'));
    return add(approxNode(re, digits), im < 0 ? neg(imPart) : imPart);
};

function numericRoots(P, ctx) {
    const zs = numPolyRoots(P.c.map((q) => q.toNumber()));
    const roots = [];
    const cplx = [];
    for (const z of zs) {
        const scale = Math.max(1, Math.hypot(z.re, z.im));
        if (Math.abs(z.im) <= 1e-9 * scale) roots.push({ node: approxNode(z.re), approx: z.re, mult: 1, minPoly: P, approxOnly: true });
        else cplx.push({ node: complexApproxNode(z.re, z.im), approx: { re: z.re, im: z.im }, mult: 1, minPoly: P, approxOnly: true, complex: true });
    }
    return { roots: mergeRoots(roots), cplx };
}

function numericNote(deg) {
    if (deg === 3) return T('Для кубических уравнений есть формула Кардано, но её ответ громоздкий (а иногда требует комплексных чисел даже для действительных корней). Находим корни приближённо.', 'Cubics have Cardano’s formula, but its answer is bulky (and sometimes needs complex numbers even for real roots). We find the roots numerically.');
    if (deg === 4) return T('Для уравнений четвёртой степени есть метод Феррари, но он очень громоздкий. Находим корни приближённо.', 'Quartics have Ferrari’s method, but it is very bulky. We find the roots numerically.');
    return T('Для степени 5 и выше общей формулы в радикалах нет (теорема Абеля — Руффини). Находим корни приближённо.', 'From degree 5 on there is no general formula in radicals (the Abel–Ruffini theorem). We find the roots numerically.');
}

/** Primitive polynomial of degree ≥ 3 with school methods → {roots, cplx, steps, numeric}. */
function highSolve(P, ctx) {
    const v = ctx.v;
    const steps = [];
    const roots = [];
    const cplx = [];
    let numeric = false;
    const deg = P.degree;
    const nz = [];
    P.c.forEach((q, k) => {
        if (!q.isZero()) nz.push(k);
    });
    const collect = (res) => {
        roots.push(...res.roots);
        cplx.push(...(res.cplx ?? []));
        if (res.numeric) numeric = true;
    };
    const eqTex = (Q_) => byLang((l) => `${polyTex(Q_, v, l)} = 0`);

    // 1. common factor x^k
    if (nz[0] > 0) {
        const k = nz[0];
        const Qp = new Poly(P.c.slice(k));
        const xk = X_POW(v, k);
        steps.push(S(T(`Выносим $${xk}$ за скобки`, `Take $${xk}$ out of the brackets`), {
            tex: byLang((l) => `${xk}\\left(${polyTex(Qp, v, l)}\\right) = 0`),
            text: T(`Произведение равно нулю, когда один из множителей равен нулю: $${v} = 0$ или $${polyTex(Qp, v, 'ru')} = 0$.`, `A product is zero when one of the factors is: $${v} = 0$ or $${polyTex(Qp, v, 'en')} = 0$.`),
        }));
        roots.push(qRoot(Q.ZERO, { mult: k }));
        const sub = solveAnyPoly(Qp, ctx);
        collect(sub);
        steps.push(partStep(eqTex(Qp), sub, v));
        return { roots, cplx, steps, numeric };
    }

    // 2. two terms: a x^n + c = 0 (real roots; in complex numbers the factoring below finds all of them)
    if (nz.length === 2 && ctx.domain !== 'complex') {
        const r = P.coeff(0).neg().div(P.lead);
        const xn = X_POW(v, deg);
        steps.push(S(T(`Выражаем $${xn}$`, `Solve for $${xn}$`), { tex: byLang((l) => `${xn} = ${tex(num(r), l)}`) }));
        const exactR = r.exactRoot(deg);
        if (deg % 2 === 1) {
            const node = exactR ? num(exactR) : simpOr(pow(num(r), num(new Q(1n, BigInt(deg)))));
            steps.push(S(T('Нечётная степень — ровно один действительный корень', 'An odd power: exactly one real root'), {
                tex: byLang((l) => `${v} = \\sqrt[${deg}]{${tex(num(r), l)}} = ${tex(node, l)}`),
            }));
            roots.push(exactR ? qRoot(exactR) : { node, approx: Math.sign(r.toNumber()) * Math.abs(r.toNumber()) ** (1 / deg), mult: 1, minPoly: P });
        } else if (r.isPos()) {
            const node = exactR ? num(exactR) : simpOr(pow(num(r), num(new Q(1n, BigInt(deg)))));
            steps.push(S(T('Чётная степень — два корня, противоположные по знаку', 'An even power: two roots of opposite signs'), {
                tex: byLang((l) => `${v} = \\pm\\sqrt[${deg}]{${tex(num(r), l)}} = \\pm ${tex(node, l)}`),
            }));
            const a = r.toNumber() ** (1 / deg);
            roots.push(exactR ? qRoot(exactR.neg()) : { node: simpOr(neg(node)), approx: -a, mult: 1, minPoly: P });
            roots.push(exactR ? qRoot(exactR) : { node, approx: a, mult: 1, minPoly: P });
        } else {
            steps.push(S(T('Чётная степень не бывает отрицательной — действительных корней нет', 'An even power is never negative: no real roots')));
        }
        if (ctx.domain === 'complex') {
            const n = numericRoots(P, ctx);
            cplx.push(...n.cplx);
            if (n.cplx.length) steps.push(S(T('Комплексные корни', 'Complex roots'), { tex: byLang((l) => n.cplx.map((z) => approxComplexTex(z.approx, l)).join(';\\ ')), text: T('Найдены приближённо.', 'Found numerically.') }));
            numeric = numeric || n.cplx.length > 0;
        }
        return { roots, cplx, steps, numeric };
    }

    // 3. trinomial in x^m: a x^{2m} + b x^m + c
    if (nz.length === 3 && nz[0] === 0 && nz[2] === 2 * nz[1] && nz[1] >= 2) {
        const m = nz[1];
        const Tq = new Poly([P.coeff(0), P.coeff(m), P.coeff(2 * m)]);
        const xm = X_POW(v, m);
        const name = m === 2 ? T('биквадратное', 'biquadratic') : T('трёхчленное', 'trinomial');
        steps.push(S(T(`Это ${name.ru} уравнение: замена $t = ${xm}$`, `This is a ${name.en} equation: substitute $t = ${xm}$`), {
            tex: byLang((l) => `${polyTex(Tq, 't', l)} = 0`),
            text: m % 2 === 0
                ? T(`Так как $${xm} \\ge 0$, нам подойдут только $t \\ge 0$.`, `Since $${xm} \\ge 0$, only $t \\ge 0$ will do.`)
                : T('Уравнение стало квадратным относительно $t$.', 'The equation is now quadratic in $t$.'),
        }));
        const tr = solveAnyPoly(Tq, { v: 't', domain: 'real' });
        steps.push(partStep(byLang((l) => `${polyTex(Tq, 't', l)} = 0`), tr, 't'));
        const back = [];
        for (const t of tr.roots) {
            const tq = numValue(t.node);
            const tMin = t.minPoly ?? new Poly([tq.neg(), Q.ONE]);
            const mp = composeXm(tMin, m).primitive();
            const tt = (l) => tex(t.node, l);
            if (m % 2 === 0 && t.approx < -1e-12) {
                back.push(S(byLang((l) => `$${xm} = ${tt(l)}$`), { text: T('Чётная степень не бывает отрицательной — корней нет.', 'An even power is never negative: no roots.') }));
                if (ctx.domain === 'complex' && m === 2) {
                    const z = simpOr(mul(sym('i'), pow(simpOr(neg(t.node)), num(Q.HALF))));
                    const im = Math.sqrt(-t.approx);
                    cplx.push({ node: simpOr(neg(z)), approx: { re: 0, im: -im }, mult: 1, minPoly: mp, complex: true }, { node: z, approx: { re: 0, im }, mult: 1, minPoly: mp, complex: true });
                }
                continue;
            }
            if (Math.abs(t.approx) <= 1e-12) {
                back.push(S(byLang((l) => `$${xm} = 0$`), { tex: `${v} = 0` }));
                roots.push(qRoot(Q.ZERO));
                continue;
            }
            const rootNode = simpOr(pow(t.node, num(new Q(1n, BigInt(m)))));
            const a = Math.sign(t.approx) * Math.abs(t.approx) ** (1 / m);
            const rq = numValue(rootNode);
            if (m % 2 === 0) {
                back.push(S(byLang((l) => `$${xm} = ${tt(l)}$`), { tex: byLang((l) => `${v} = \\pm ${tex(rootNode, l)}`) }));
                roots.push(rq ? qRoot(rq.neg()) : { node: simpOr(neg(rootNode)), approx: -a, mult: 1, minPoly: mp });
                roots.push(rq ? qRoot(rq) : { node: rootNode, approx: a, mult: 1, minPoly: mp });
            } else {
                back.push(S(byLang((l) => `$${xm} = ${tt(l)}$`), { tex: byLang((l) => `${v} = ${tex(rootNode, l)}`) }));
                roots.push(rq ? qRoot(rq) : { node: rootNode, approx: a, mult: 1, minPoly: mp });
            }
        }
        if (ctx.domain === 'complex' && (m !== 2 || tr.cplx?.length)) {
            const n = numericRoots(P, ctx);
            const extra = n.cplx.filter((z) => !cplx.some((w) => sameRoot(w, z)));
            if (extra.length) {
                cplx.push(...extra);
                numeric = true;
            }
        }
        steps.push(S(T('Обратная замена', 'Substitute back'), { sub: back, tex: byLang((l) => rootsTex(mergeRoots(roots), v, l)) }));
        return { roots, cplx, steps, numeric };
    }

    // 4. reciprocal (symmetric) quartic: a x^4 + b x^3 + c x^2 + b x + a
    if (deg === 4 && P.coeff(4).eq(P.coeff(0)) && P.coeff(3).eq(P.coeff(1)) && !P.coeff(1).isZero()) {
        const a = P.coeff(4);
        const b = P.coeff(3);
        const c = P.coeff(2);
        const Tq = new Poly([c.sub(a.mul(2)), b, a]);
        steps.push(S(T(`Симметричное (возвратное) уравнение: делим на $${v}^2$`, `A symmetric (reciprocal) equation: divide by $${v}^2$`), {
            tex: byLang((l) => `${tex(num(a), l) === '1' ? '' : tex(num(a), l)}\\left(${v}^2 + \\frac{1}{${v}^2}\\right) ${b.isNeg() ? '-' : '+'} ${b.abs().isOne() ? '' : tex(num(b.abs()), l)}\\left(${v} + \\frac{1}{${v}}\\right) ${c.isNeg() ? '-' : '+'} ${tex(num(c.abs()), l)} = 0`),
            text: T(`Коэффициенты читаются одинаково слева направо и справа налево. $${v} = 0$ не корень (свободный член не равен нулю), поэтому делить на $${v}^2$ можно.`,
                `The coefficients read the same both ways. $${v} = 0$ is not a root (the constant term is not zero), so dividing by $${v}^2$ is allowed.`),
        }));
        steps.push(S(T(`Замена $t = ${v} + \\frac{1}{${v}}$, тогда $${v}^2 + \\frac{1}{${v}^2} = t^2 - 2$`, `Substitute $t = ${v} + \\frac{1}{${v}}$; then $${v}^2 + \\frac{1}{${v}^2} = t^2 - 2$`), {
            tex: byLang((l) => `${polyTex(Tq, 't', l)} = 0`),
        }));
        const tr = solveAnyPoly(Tq, { v: 't', domain: 'real' });
        steps.push(partStep(byLang((l) => `${polyTex(Tq, 't', l)} = 0`), tr, 't'));
        const back = [];
        for (const t of tr.roots) {
            const tq = numValue(t.node);
            if (tq) {
                const Qx = new Poly([Q.ONE, tq.neg(), Q.ONE]);
                const sub = solveAnyPoly(Qx, ctx);
                roots.push(...sub.roots);
                cplx.push(...(sub.cplx ?? []));
                back.push(partStep(byLang((l) => `${v} + \\frac{1}{${v}} = ${tex(t.node, l)} \\;\\Leftrightarrow\\; ${polyTex(Qx, v, l)} = 0`), sub, v));
            } else {
                const res = nodeQuadRoots(N1, simpOr(neg(t.node)), N1, ctx);
                roots.push(...res.roots.map((r) => ({ ...r, minPoly: P })));
                cplx.push(...res.cplx.map((r) => ({ ...r, minPoly: P })));
                back.push(S(byLang((l) => `$${v} + \\frac{1}{${v}} = ${tex(t.node, l)}$`), { tex: byLang((l) => rootsTex(res.roots, v, l)), sub: res.steps }));
            }
        }
        steps.push(S(T('Обратная замена', 'Substitute back'), { sub: back, tex: byLang((l) => rootsTex(mergeRoots(roots), v, l)) }));
        return { roots, cplx, steps, numeric };
    }

    // 5. grouping: a x^3 + b x^2 + c x + d with a·d = b·c
    if (deg === 3 && nz.length === 4 && P.coeff(3).mul(P.coeff(0)).eq(P.coeff(2).mul(P.coeff(1)))) {
        const a = P.coeff(3);
        const b = P.coeff(2);
        const m = P.coeff(1).div(a);
        const lin = new Poly([b, a]);
        const sqr = new Poly([m, Q.ZERO, Q.ONE]);
        const X = sym(v);
        const grouped = add(mul(pow(X, num(2)), lin.toNode(v)), mul(num(m), lin.toNode(v)));
        steps.push(S(T('Группируем слагаемые', 'Group the terms'), {
            tex: byLang((l) => `${tex(grouped, l)} = 0 \\;\\Rightarrow\\; \\left(${polyTex(lin, v, l)}\\right)\\left(${polyTex(sqr, v, l)}\\right) = 0`),
            text: T('Из первых двух слагаемых выносим $x^2$, из последних двух — число; в скобках остаётся одно и то же.', 'Take $x^2$ out of the first two terms and a number out of the last two: the same bracket remains.'),
        }));
        for (const F of [lin, sqr]) {
            const sub = solveAnyPoly(F, ctx);
            collect(sub);
            steps.push(partStep(eqTex(F), sub, v));
        }
        return { roots, cplx, steps, numeric };
    }

    // 6. rational roots + Horner, reducing the degree
    const cands = candidatesOrdered(P);
    steps.push(S(T('Ищем рациональные корни', 'Look for rational roots'), {
        text: T(`Если у многочлена с целыми коэффициентами есть рациональный корень $\\frac{p}{q}$, то $p$ делит свободный член, а $q$ — старший коэффициент. Кандидаты: $${candidatesTex(cands, 'ru')}$.`,
            `If a polynomial with integer coefficients has a rational root $\\frac{p}{q}$, then $p$ divides the constant term and $q$ divides the leading coefficient. Candidates: $${candidatesTex(cands, 'en')}$.`),
    }));
    let rest = P;
    let found = true;
    while (rest.degree >= 3 && found) {
        found = false;
        const tried = [];
        for (const c of cands) {
            if (tried.length > 40) break;
            const val = rest.evalAt(c);
            if (!val.isZero()) {
                tried.push([c, val]);
                continue;
            }
            const h = rest.horner(c);
            const Qn = h.quotient;
            const triedTex = (l) => tried.slice(-6).map(([x, y]) => `P(${tex(num(x), l)}) = ${tex(num(y), l)} \\ne 0`).join(l === 'ru' ? ';\\ ' : ',\\ ');
            steps.push(S(T(`Схема Горнера: $${v} = ${tex(num(c))}$ — корень`, `Horner’s scheme: $${v} = ${tex(num(c), 'en')}$ is a root`), {
                tex: byLang((l) => hornerTex(rest, c, l)),
                text: T(`${tried.length ? `Проверили: $${triedTex('ru')}$. ` : ''}Остаток (последнее число) равен нулю, значит $${tex(num(c))}$ — корень, и многочлен делится на $${tex(linFactorNode(v, c))}$: $${tex(mul(linFactorNode(v, c), Qn.toNode(v)))} = 0$.`,
                    `${tried.length ? `Checked: $${triedTex('en')}$. ` : ''}The remainder (the last number) is zero, so $${tex(num(c), 'en')}$ is a root and the polynomial is divisible by $${tex(linFactorNode(v, c), 'en')}$: $${tex(mul(linFactorNode(v, c), Qn.toNode(v)), 'en')} = 0$.`),
            }));
            roots.push(qRoot(c));
            rest = Qn;
            found = true;
            break;
        }
    }
    if (rest.degree <= 2) {
        if (rest.degree >= 1) {
            const sub = solveAnyPoly(rest, ctx);
            collect(sub);
            steps.push(partStep(eqTex(rest.primitive()), sub, v));
        }
        return { roots, cplx, steps, numeric };
    }
    // 7. no more rational roots: split into quadratics if possible, else numerically
    const restP = rest.primitive();
    const fz = restP.factor();
    const pieces = fz.factors.filter((f) => f.poly.degree >= 1);
    if (pieces.length > 1 && pieces.every((f) => f.poly.degree <= 2)) {
        const prod = mul(pieces.map((f) => (f.mult > 1 ? pow(f.poly.toNode(v), num(f.mult)) : f.poly.toNode(v))));
        steps.push(S(T('Раскладываем оставшийся многочлен на множители', 'Factor the remaining polynomial'), {
            tex: byLang((l) => `${polyTex(restP, v, l)} = ${tex(prod, l)}`),
        }));
        for (const f of pieces) {
            const sub = solveAnyPoly(f.poly, ctx);
            collect(sub);
            steps.push(partStep(eqTex(f.poly), sub, v));
        }
        return { roots, cplx, steps, numeric };
    }
    const n = numericRoots(restP, ctx);
    roots.push(...n.roots);
    cplx.push(...n.cplx);
    numeric = true;
    steps.push(S(T(`Рациональных корней у $${polyTex(restP, v, 'ru')}$ больше нет`, `$${polyTex(restP, v, 'en')}$ has no more rational roots`), {
        text: numericNote(restP.degree),
        tex: byLang((l) => (n.roots.length ? rootsTex(n.roots, v, l) : l === 'ru' ? '\\text{действительных корней нет}' : '\\text{no real roots}')),
    }));
    return { roots, cplx, steps, numeric };
}

/** Quadratic with constant node coefficients (irrational ones allowed) → {roots, cplx, steps}. */
function nodeQuadRoots(aN, bN, cN, ctx) {
    const v = ctx.v;
    const cx = [aN, bN, cN].some(hasI);
    const co = cx ? { complex: true } : undefined;
    const D = simpOr(expd(add(pow(bN, num(2)), mul(num(-4), aN, cN)), co) ?? add(pow(bN, num(2)), mul(num(-4), aN, cN)), co);
    const d = approxOf(D);
    const steps = [S(T('Дискриминант', 'The discriminant'), { tex: byLang((l) => `D = b^2 - 4ac = ${tex(D, l)}`) })];
    const two = mul(num(2), aN);
    const roots = [];
    const cplx = [];
    const Dc = cx ? approxC(D) : null;
    if (cx && Dc && Math.abs(Dc.im) > 1e-12 * Math.max(1, Math.abs(Dc.re))) {
        // a non-real discriminant (complex coefficients): its square root, exactly when it is a Gaussian rational
        const s = simpOr(pow(D, num(Q.HALF)), co);
        const exactS = !(s.type === 'pow' || nodeSome(s, (x) => x.type === 'pow' && hasI(x.base)));
        steps.push(S(T('Квадратный корень из комплексного дискриминанта', 'The square root of the complex discriminant'), {
            tex: byLang((l) => `\\sqrt{D} = ${exactS ? `\\pm\\left(${tex(s, l)}\\right)` : `\\pm\\sqrt{${tex(D, l)}}`}`),
            text: exactS
                ? T(`Ищем $w = p + qi$ с $w^2 = D$: $p^2 - q^2 = \\operatorname{Re} D$, $2pq = \\operatorname{Im} D$. Проверка: $\\left(${tex(s)}\\right)^2 = ${tex(D)}$.`,
                    `Look for $w = p + qi$ with $w^2 = D$: $p^2 - q^2 = \\operatorname{Re} D$, $2pq = \\operatorname{Im} D$. Check: $\\left(${tex(s, 'en')}\\right)^2 = ${tex(D, 'en')}$.`)
                : undefined,
        }));
        for (const sg of [-1, 1]) {
            const node = simpOr(div(add(neg(bN), sg < 0 ? neg(s) : s), two), co);
            const r = mkRootC(node);
            if (r.complex) cplx.push(r);
            else roots.push(r);
        }
        steps.push(S(T('Корни', 'The roots'), { tex: byLang((l) => `${v}_{1,2} = \\frac{-b \\pm \\sqrt{D}}{2a}:\\quad ${[...roots, ...cplx].map((r) => tex(r.node, l)).join(l === 'ru' ? ';\\ ' : ',\\ ')}`) }));
        return { roots, cplx, steps };
    }
    if (Math.abs(d) <= 1e-12 * Math.max(1, Math.abs(approxOf(bN)) ** 2) && exactZero(D) !== false) {
        const r = simpOr(div(neg(bN), two));
        roots.push(mkRoot(r, { mult: 2 }));
        steps.push(S(T('$D = 0$ — один корень', '$D = 0$: one root'), { tex: byLang((l) => `${v} = ${tex(r, l)}`) }));
    } else if (d > 0) {
        const s = simpOr(pow(D, num(Q.HALF)));
        for (const sg of [-1, 1]) roots.push(mkRoot(simpOr(div(add(neg(bN), sg < 0 ? neg(s) : s), two))));
        roots.sort(cmpRoots);
        steps.push(S(T('$D > 0$ — два корня', '$D > 0$: two roots'), { tex: byLang((l) => rootsTex(roots, v, l)) }));
    } else {
        const s = simpOr(pow(simpOr(neg(D)), num(Q.HALF)));
        for (const sg of [-1, 1]) {
            const node = simpOr(div(add(neg(bN), mul(num(sg), sym('i'), s)), two), { complex: true });
            cplx.push({ node, approx: approxC(node) ?? { re: NaN, im: NaN }, mult: 1, complex: true });
        }
        steps.push(S(T('$D < 0$ — действительных корней нет', '$D < 0$: no real roots')));
    }
    return { roots, cplx, steps };
}

// ---------------------------------------------------------------- linear equations (school style)

const isZeroNode = (n) => n.type === 'num' && n.value.isZero();
const monoNode = (c, v, k = 1) => simpOr(mul(num(c), k === 1 ? sym(v) : pow(sym(v), num(k))));
const sumNode = (terms) => (terms.length ? (terms.length === 1 ? terms[0] : add(terms)) : N0);

/** a₁x + a₀ = b₁x + b₀ (both sides polynomials over Q, the difference of degree ≤ 1). */
function solveLinearSchool(lhs, rhs, A, B, ctx) {
    const v = ctx.v;
    const steps = [];
    let den = 1n;
    for (const q of [...A.c, ...B.c]) den = bigLcm(den, q.d);
    let A1 = A;
    let B1 = B;
    const eqT = (P1, P2) => byLang((l) => `${polyTex(P1, v, l)} = ${polyTex(P2, v, l)}`);
    const expanded = nodeKey(simpOr(lhs)) !== nodeKey(A.toNode(v)) || nodeKey(simpOr(rhs)) !== nodeKey(B.toNode(v)) || nodeSome(lhs, (n) => n.type === 'mul' && n.args.some((a) => a.type === 'add')) || nodeSome(rhs, (n) => n.type === 'mul' && n.args.some((a) => a.type === 'add'));
    if (den > 1n) {
        A1 = A.scale(new Q(den));
        B1 = B.scale(new Q(den));
        steps.push(S(T(`Умножаем обе части на $${den}$ — общий знаменатель дробей`, `Multiply both sides by $${den}$, the common denominator`), {
            tex: eqT(A1, B1),
            text: T('Если обе части умножить на одно и то же число (не ноль), равенство сохранится, а дроби исчезнут.', 'Multiplying both sides by the same non-zero number keeps the equality and removes the fractions.'),
        }));
    } else if (expanded) {
        steps.push(S(T('Раскрываем скобки и приводим подобные', 'Expand the brackets and collect like terms'), { tex: eqT(A1, B1) }));
    }
    const a1 = A1.coeff(1);
    const a0 = A1.coeff(0);
    const b1 = B1.coeff(1);
    const b0 = B1.coeff(0);
    const a = a1.sub(b1);
    const b = b0.sub(a0);
    const hi = Math.max(A1.degree, B1.degree);
    if (!b1.isZero() || !a0.isZero() || hi >= 2) {
        const left = [];
        const right = [];
        if (!a1.isZero()) left.push(monoNode(a1, v));
        if (!b1.isZero()) left.push(monoNode(b1.neg(), v));
        if (!b0.isZero()) right.push(num(b0));
        if (!a0.isZero()) right.push(num(a0.neg()));
        steps.push(S(T(`Переносим слагаемые с $${v}$ влево, числа — вправо`, `Move the $${v}$ terms to the left and the numbers to the right`), {
            tex: byLang((l) => `${tex(sumNode(left), l)} = ${tex(sumNode(right), l)}`),
            text: hi >= 2
                ? T(`Слагаемые со старшими степенями $${v}$ в обеих частях одинаковые и сокращаются. При переносе через знак равенства слагаемое меняет знак.`, `The higher powers of $${v}$ are the same on both sides and cancel. A term that crosses the equals sign changes its sign.`)
                : T('При переносе через знак равенства слагаемое меняет знак.', 'A term that crosses the equals sign changes its sign.'),
        }));
        if (left.length > 1 || right.length > 1) steps.push(S(T('Приводим подобные', 'Collect like terms'), { tex: byLang((l) => `${tex(monoNode(a, v), l)} = ${tex(num(b), l)}`) }));
    }
    if (a.isZero()) {
        if (b.isZero()) {
            steps.push(S(T(`Получили $0 \\cdot ${v} = 0$ — верно при любом $${v}$`, `We get $0 \\cdot ${v} = 0$, true for every $${v}$`), {
                text: T('Уравнение превратилось в тождество: корень — любое число.', 'The equation is an identity: every number is a root.'),
            }));
            return { kind: 'all', roots: [], steps, type: 'linear' };
        }
        steps.push(S(T(`Получили $0 \\cdot ${v} = ${tex(num(b))}$ — так не бывает`, `We get $0 \\cdot ${v} = ${tex(num(b), 'en')}$, which never holds`), {
            text: T(`Слева ноль при любом $${v}$, справа не ноль — корней нет.`, `The left side is zero for every $${v}$, the right side is not: no roots.`),
        }));
        return { kind: 'none', roots: [], steps, type: 'linear' };
    }
    const r = b.div(a);
    if (!a.isOne()) {
        steps.push(S(T(`Делим обе части на $${tex(num(a))}$`, `Divide both sides by $${tex(num(a), 'en')}$`), {
            tex: byLang((l) => {
                const fr = a.isInt() && b.isInt() ? `\\frac{${tex(num(b), l)}}{${tex(num(a), l)}}` : `${tex(num(b), l)} : ${parQ(a, l)}`;
                const rt = tex(num(r), l);
                return fr === rt ? `${v} = ${rt}` : `${v} = ${fr} = ${rt}`;
            }),
            text: T('Делить можно: коэффициент при переменной не равен нулю.', 'That is allowed: the coefficient is not zero.'),
        }));
    }
    return { kind: 'roots', roots: [qRoot(r)], steps, type: 'linear' };
}

// ---------------------------------------------------------------- polynomial equations of degree ≥ 2

function solvePolyEquation(lhs, rhs, P, ctx) {
    const v = ctx.v;
    const steps = [];
    const rhsZero = isZeroNode(simpOr(rhs));
    const same = rhsZero && nodeKey(simpOr(lhs)) === nodeKey(P.toNode(v));
    if (!same) {
        steps.push(S(rhsZero ? T('Раскрываем скобки и приводим подобные', 'Expand the brackets and collect like terms') : T('Переносим всё в левую часть и приводим подобные', 'Move everything to the left and collect like terms'), {
            tex: byLang((l) => `${polyTex(P, v, l)} = 0`),
            text: rhsZero ? undefined : T('Слагаемые переходят через знак равенства с противоположным знаком.', 'Terms cross the equals sign with the opposite sign.'),
        }));
    }
    const res = solveAnyPoly(P, ctx);
    const Pp = P.primitive();
    for (const r of [...res.roots, ...res.cplx]) {
        if (r.minPoly && !r.approxOnly) r.mult = multOf(Pp, r.minPoly.primitive());
    }
    const roots = mergeRoots(res.roots);
    const cplx = mergeRoots(res.cplx);
    const all = ctx.domain === 'complex' ? [...roots, ...cplx] : roots;
    return {
        kind: all.length ? 'roots' : 'none',
        roots: all,
        complexRoots: ctx.domain === 'complex' ? [] : cplx,
        steps: [...steps, ...res.steps],
        numeric: !!res.numeric,
        type: P.degree === 2 ? 'quadratic' : 'polynomial',
    };
}

// ---------------------------------------------------------------- "a product equals zero"

function factorsOf(node, v) {
    const s = node.type === 'neg' ? node.arg : node;
    if (s.type === 'mul') return s.args.filter((f) => containsVar(f, v));
    if (s.type === 'pow' && containsVar(s.base, v)) {
        const e = numValue(s.exp);
        if (e && e.isInt() && e.gt(1)) return [s];
    }
    return null;
}

function productSplit(lhs, rhs, ctx) {
    const v = ctx.v;
    let side = null;
    if (isZeroNode(simpOr(rhs))) side = lhs;
    else if (isZeroNode(simpOr(lhs))) side = rhs;
    if (!side) return null;
    let fs = factorsOf(side, v);
    if (!fs) {
        const s = simp(side);
        fs = s && factorsOf(s, v);
    }
    if (!fs || !fs.length) return null;
    // a lone power of a polynomial is left to the polynomial route when it is the whole product
    const single = fs.length === 1;
    const bases = fs.map((f) => {
        if (f.type === 'pow') {
            const e = numValue(f.exp);
            if (e && e.isInt() && e.isPos()) return { node: f.base, mult: Number(e.n) };
        }
        return { node: f, mult: 1 };
    });
    if (single && bases[0].mult === 1) return null;
    if (bases.some((b) => b.node.type === 'div')) return null;
    const steps = [S(T('Произведение равно нулю', 'A product equals zero'), {
        text: T('Произведение равно нулю, когда хотя бы один из множителей равен нулю (а остальные при этом имеют смысл — это проверим в конце).', 'A product is zero when at least one factor is zero (and the others make sense there, which we check at the end).'),
        tex: byLang((l) => bases.map((b) => `${tex(b.node, l)} = 0`).join(` \\quad ${l === 'ru' ? '\\text{или}' : '\\text{or}'} \\quad `)),
    })];
    let roots = [];
    const families = [];
    let kind = 'none';
    let numeric = false;
    let set = null;
    const cplx = [];
    for (const b of bases) {
        const sub = solveCore(b.node, N0, { ...ctx, depth: ctx.depth + 1 });
        if (sub.kind === 'unsupported') return null;
        if (sub.kind === 'all') {
            kind = 'all';
            set = sub.set ?? null;
        }
        if (sub.kind === 'set') set = set ? set.union(sub.set) : sub.set;
        roots.push(...sub.roots.map((r) => ({ ...r, mult: (r.mult ?? 1) * b.mult })));
        if (sub.families) families.push(...sub.families);
        if (sub.complexRoots) cplx.push(...sub.complexRoots);
        if (sub.numeric) numeric = true;
        steps.push(partStep(byLang((l) => `${tex(b.node, l)} = 0`), { ...sub, roots: sub.families ? [] : sub.roots }, v));
        if (sub.families) steps[steps.length - 1].tex = byLang((l) => familiesTex(sub.families, v, l));
    }
    roots = mergeRoots(roots, true);
    if (kind === 'all') return { kind: 'all', roots: [], steps, type: 'product', set };
    if (set && !set.isFinite()) return { kind: 'set', roots, set: set.union(IntervalSet.points(roots.map((r) => r.node))), steps, type: 'product' };
    if (families.length) return { kind: 'roots', roots: familiesToRoots(mergeFamilies(families)), families: mergeFamilies(families), steps, type: 'trig', periodic: true };
    return { kind: roots.length ? 'roots' : 'none', roots, complexRoots: mergeRoots(cplx), steps, type: 'product', numeric };
}

// ---------------------------------------------------------------- rational equations

function polyLcm(A, B) {
    const g = A.gcd(B);
    return A.mul(B).divmod(g).q.monic();
}

/** Factored TeX of a polynomial: (x − 2)(x + 2). */
function factoredNode(P, v) {
    const f = P.factor();
    const parts = f.factors.map((x) => (x.mult > 1 ? pow(x.poly.toNode(v), num(x.mult)) : x.poly.toNode(v)));
    if (!f.constant.isOne()) parts.unshift(num(f.constant));
    return parts.length ? (parts.length === 1 ? parts[0] : mul(parts)) : num(f.constant);
}

function termsOfSum(n) {
    return n.type === 'add' ? n.args : [n];
}

/** f(x) = g(x) with polynomial fractions: common denominator, numerator = 0, poles excluded. */
function solveRational(lhs, rhs, E, ctx) {
    const v = ctx.v;
    const parts = [];
    for (const t of termsOfSum(E)) {
        let nd;
        try {
            nd = numDen(t);
        } catch {
            return null;
        }
        const Pn = Poly.fromNode(nd.num, v);
        const Pd = Poly.fromNode(nd.den, v);
        if (!Pn || !Pd || Pd.isZero()) return null;
        parts.push({ Pn, Pd });
    }
    if (!parts.some((p) => p.Pd.degree >= 1)) return null;
    let L = new Poly([Q.ONE]);
    for (const p of parts) L = polyLcm(L, p.Pd.monic());
    let N = new Poly([]);
    for (const p of parts) {
        const { q, r } = L.divmod(p.Pd);
        if (!r.isZero()) return null;
        N = N.add(p.Pn.mul(q));
    }
    const Lp = L.primitive();
    const k = Lp.lead.div(L.lead);
    N = N.scale(k);
    const steps = [];
    const Lnode = factoredNode(Lp, v);
    steps.push(S(T('Переносим всё влево и приводим к общему знаменателю', 'Move everything to the left and bring to a common denominator'), {
        tex: byLang((l) => `\\frac{${polyTex(N, v, l)}}{${tex(Lnode, l)}} = 0`),
        text: T('Дробь равна нулю, когда числитель равен нулю, а знаменатель — нет.', 'A fraction is zero when its numerator is zero and its denominator is not.'),
    }));
    const poles = Lp.degree >= 1 ? solveAnyPoly(Lp, { v, domain: 'real' }).roots : [];
    const res = N.degree >= 1 ? solveAnyPoly(N, { ...ctx }) : { kind: N.isZero() ? 'all' : 'none', roots: [], cplx: [], steps: [] };
    if (N.degree >= 1) steps.push(partStep(byLang((l) => `${polyTex(N, v, l)} = 0`), res, v));
    const Np = N.primitive();
    for (const r of res.roots ?? []) if (r.minPoly && !r.approxOnly) r.mult = multOf(Np, r.minPoly.primitive());
    let roots = mergeRoots(res.roots ?? []);
    const bad = roots.filter((r) => Math.abs(Lp.evalNumber(r.approx)) <= 1e-9 * Math.max(1, Math.abs(r.approx)) ** Lp.degree && (r.approxOnly || exactZero(substitute(Lp.toNode(v), { [v]: r.node })) !== false));
    if (bad.length) {
        reject(ctx, bad, 'pole');
        roots = roots.filter((r) => !bad.includes(r));
        steps.push(S(T('Исключаем корни, при которых знаменатель равен нулю', 'Drop the roots that make the denominator zero'), {
            tex: byLang((l) => bad.map((r) => `${v} = ${tex(r.node, l)}`).join(',\\ ')),
            text: T('При этих значениях знаменатель обращается в ноль — дробь не имеет смысла, поэтому это не корни.', 'At these values the denominator is zero and the fraction makes no sense, so they are not roots.'),
        }));
    }
    if (N.degree < 1) {
        if (N.isZero()) {
            const set = IntervalSet.all().minus(IntervalSet.points(poles.map((p) => p.node)));
            steps.push(S(T('Числитель тождественно равен нулю', 'The numerator is identically zero'), { text: T('Равенство верно при всех допустимых значениях переменной.', 'The equality holds for all admissible values.') }));
            return { kind: 'all', roots: [], set, steps, type: 'rational' };
        }
        steps.push(S(T('Числитель — ненулевое число', 'The numerator is a non-zero number'), { text: T('Дробь с ненулевым числителем нулю не равна — корней нет.', 'A fraction with a non-zero numerator is never zero: no roots.') }));
        return { kind: 'none', roots: [], steps, type: 'rational' };
    }
    return { kind: roots.length ? 'roots' : 'none', roots, complexRoots: mergeRoots(res.cplx ?? []), steps, numeric: !!res.numeric, type: 'rational' };
}

// ---------------------------------------------------------------- algebraic with irrational constant coefficients

function solveNodePoly(E, ctx) {
    const v = ctx.v;
    let ct;
    try {
        ct = collectTerms(E, v);
    } catch {
        return null;
    }
    if (!ct) return null;
    const degs = [...ct.keys()];
    if (!degs.length || degs.some((d) => !Number.isInteger(d) || d < 0 || d > 2)) return null;
    for (const c of ct.values()) if (!isConstNode(c)) return null;
    const c2 = ct.get(2) ?? N0;
    const c1 = ct.get(1) ?? N0;
    const c0 = ct.get(0) ?? N0;
    const steps = [S(T('Переносим всё в левую часть', 'Move everything to the left'), { tex: byLang((l) => `${tex(E, l)} = 0`) })];
    const cx = [c0, c1, c2].some(hasI);
    if (!ct.has(2)) {
        if (!ct.has(1)) return null;
        const q = div(neg(c0), c1);
        const r = simpOr(q, cx ? { complex: true } : undefined);
        const shown = cx && nodeKey(r) !== nodeKey(simpOr(q)) ? simpOr(q) : null;
        steps.push(S(T(`Выражаем $${v}$`, `Solve for $${v}$`), {
            tex: byLang((l) => `${v} = ${shown ? `${tex(shown, l)} = ` : ''}${tex(r, l)}`),
            text: shown ? T('Чтобы разделить на комплексное число, умножаем числитель и знаменатель на сопряжённое к знаменателю.', 'To divide by a complex number, multiply the numerator and the denominator by the conjugate of the denominator.') : undefined,
        }));
        const root = cx ? mkRootC(r) : mkRoot(r);
        if (root.complex && ctx.domain !== 'complex') {
            steps.push(S(T('Корень не действительный — действительных корней нет', 'The root is not real: no real roots')));
            return { kind: 'none', roots: [], complexRoots: [root], steps, type: 'linear' };
        }
        return { kind: 'roots', roots: [root], steps, type: 'linear' };
    }
    const res = nodeQuadRoots(c2, c1, c0, ctx);
    steps.push(...res.steps);
    const all = ctx.domain === 'complex' ? [...res.roots, ...res.cplx] : res.roots;
    return { kind: all.length ? 'roots' : 'none', roots: all, complexRoots: ctx.domain === 'complex' ? [] : res.cplx, steps, type: 'quadratic' };
}

// ---------------------------------------------------------------- tree helpers

/** Replace every subtree equal to `target` by `repl`. */
function replaceNode(node, target, repl) {
    const key = nodeKey(target);
    return mapNode(node, (n) => (nodeKey(n) === key ? repl : undefined));
}

/** Outermost nodes matching pred (not looking inside a match). */
function outermost(node, pred) {
    const out = [];
    const seen = new Set();
    const walk = (n) => {
        if (pred(n)) {
            const k = nodeKey(n);
            if (!seen.has(k)) {
                seen.add(k);
                out.push(n);
            }
            return;
        }
        for (const c of nodeChildren(n)) walk(c);
    };
    walk(node);
    return out;
}

/** Is the equation already "X = Y" (either way round)? */
function isolated(lhs, rhs, X, Y) {
    const l = nodeKey(simpOr(lhs));
    const r = nodeKey(simpOr(rhs));
    const x = nodeKey(simpOr(X));
    const y = nodeKey(simpOr(Y));
    return (l === x && r === y) || (l === y && r === x);
}

const TMP = '__u';
const TMP2 = '__w';

/** E = α·U + β in the placeholder U (α constant ≠ 0) → {alpha, beta} or null. */
function linearIn(E, name, v) {
    let ct;
    try {
        ct = collectTerms(E, name);
    } catch {
        return null;
    }
    if (!ct || ![...ct.keys()].every((d) => d === 0 || d === 1) || !ct.has(1)) return null;
    const alpha = ct.get(1);
    if (containsVar(alpha, v) || freeVars(alpha).length) return null;
    return { alpha, beta: ct.get(0) ?? N0 };
}

/** Remember roots dropped by a sub-solver (they are reported as extraneous with the reason). */
function reject(ctx, roots, reason) {
    if (!ctx.rejected) return;
    for (const r of roots) if (!ctx.rejected.some((x) => sameRoot(x, r))) ctx.rejected.push({ node: r.node, approx: r.approx, reason });
}

function subSolve(lhs, rhs, ctx) {
    return solveCore(lhs, rhs, { ...ctx, depth: ctx.depth + 1 });
}

const orTex = (l) => (l === 'ru' ? '\\quad\\text{или}\\quad' : '\\quad\\text{or}\\quad');

// ---------------------------------------------------------------- absolute value

function solveAbs(lhs, rhs, E, ctx) {
    const v = ctx.v;
    const A = outermost(E, (n) => n.type === 'fn' && n.name === 'abs' && containsVar(n, v));
    if (!A.length) return null;
    const steps = [];
    if (A.length === 1) {
        const f = A[0].args[0];
        const Eu = replaceNode(E, A[0], sym(TMP));
        const li = linearIn(Eu, TMP, v);
        if (li) {
            const g = simpOr(div(neg(li.beta), li.alpha));
            const absT = (l) => tex(A[0], l);
            if (!containsVar(g, v)) {
                const gv = approxOf(g);
                if (!isolated(lhs, rhs, A[0], g)) steps.push(S(T('Уединяем модуль', 'Isolate the absolute value'), { tex: byLang((l) => `${absT(l)} = ${tex(g, l)}`) }));
                if (gv < 0 && exactZero(g) !== true) {
                    steps.push(S(T('Модуль не бывает отрицательным — корней нет', 'An absolute value is never negative: no roots')));
                    return { kind: 'none', roots: [], steps, type: 'abs' };
                }
                if (exactZero(g) === true) {
                    const sub = subSolve(f, N0, ctx);
                    steps.push(partStep(byLang((l) => `${tex(f, l)} = 0`), sub, v));
                    return { ...sub, steps, type: 'abs' };
                }
                steps.push(S(T('Модуль равен положительному числу — два случая', 'The absolute value equals a positive number: two cases'), {
                    tex: byLang((l) => `${tex(f, l)} = ${tex(g, l)} ${orTex(l)} ${tex(f, l)} = ${tex(simpOr(neg(g)), l)}`),
                    text: T('Число на расстоянии $a$ от нуля — это $a$ или $-a$.', 'A number at distance $a$ from zero is $a$ or $-a$.'),
                }));
                let roots = [];
                for (const rhs2 of [g, simpOr(neg(g))]) {
                    const sub = subSolve(f, rhs2, ctx);
                    if (sub.kind === 'unsupported') return null;
                    roots.push(...sub.roots);
                    pushPart(steps, f, rhs2, sub, v);
                }
                roots = mergeRoots(roots);
                return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'abs' };
            }
            // |f| = g(x)
            if (!isolated(lhs, rhs, A[0], g)) steps.push(S(T('Уединяем модуль', 'Isolate the absolute value'), { tex: byLang((l) => `${absT(l)} = ${tex(g, l)}`) }));
            steps.push(S(T('Раскрываем модуль', 'Open the absolute value'), {
                tex: byLang((l) => `${tex(g, l)} \\ge 0,\\qquad ${tex(f, l)} = ${tex(g, l)} ${orTex(l)} ${tex(f, l)} = ${tex(simpOr(neg(g)), l)}`),
                text: T('Модуль неотрицателен, поэтому правая часть должна быть $\\ge 0$; тогда подмодульное выражение равно ей или противоположному числу.', 'An absolute value is non-negative, so the right side must be $\\ge 0$; then the inside equals it or its opposite.'),
            }));
            let cands = [];
            for (const rhs2 of [g, simpOr(neg(g))]) {
                const sub = subSolve(f, rhs2, ctx);
                if (sub.kind === 'unsupported') return null;
                if (sub.kind === 'all' || sub.kind === 'set') return absIntervals(E, A, ctx);
                cands.push(...sub.roots);
                pushPart(steps, f, rhs2, sub, v);
            }
            cands = mergeRoots(cands);
            const good = [];
            const bad = [];
            for (const r of cands) {
                const gv = approxOf(g, { [v]: r.approx });
                if (Number.isFinite(gv) && (gv >= -1e-12 || (!r.approxOnly && exactZero(substitute(g, { [v]: r.node })) === true))) good.push(r);
                else bad.push(r);
            }
            if (bad.length) {
                reject(ctx, bad, 'sign');
                steps.push(S(T(`Отбрасываем корни, при которых $${tex(g)} < 0$`, `Drop the roots where $${tex(g, 'en')} < 0$`), {
                    tex: byLang((l) => bad.map((r) => `${v} = ${tex(r.node, l)}`).join(',\\ ')),
                    text: T('Модуль не может равняться отрицательному числу.', 'An absolute value cannot equal a negative number.'),
                }));
            }
            return { kind: good.length ? 'roots' : 'none', roots: good, steps, type: 'abs' };
        }
    }
    if (A.length === 2 && E.type === 'add' && E.args.length === 2) {
        // α|f| + β|g| = 0 with α = −β: |f| = |g|
        const sp = E.args.map((t) => splitAbsTerm(t, v));
        if (sp.every(Boolean) && exactZero(add(sp[0].coef, sp[1].coef)) === true) {
            const f = sp[0].abs.args[0];
            const g = sp[1].abs.args[0];
            steps.push(S(T('Модули равны — выражения равны или противоположны', 'Equal absolute values: the expressions are equal or opposite'), {
                tex: byLang((l) => `${tex(f, l)} = ${tex(g, l)} ${orTex(l)} ${tex(f, l)} = ${tex(simpOr(neg(g)), l)}`),
            }));
            let roots = [];
            let ok = true;
            for (const rhs2 of [g, simpOr(neg(g))]) {
                const sub = subSolve(f, rhs2, ctx);
                if (sub.kind === 'unsupported' || sub.kind === 'all' || sub.kind === 'set') {
                    ok = false;
                    break;
                }
                roots.push(...sub.roots);
                pushPart(steps, f, rhs2, sub, v);
            }
            if (ok) {
                roots = mergeRoots(roots);
                return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'abs' };
            }
            steps.length = 0;
        }
    }
    return absIntervals(E, A, ctx);
}

function splitAbsTerm(t, v) {
    const isAbs = (n) => n.type === 'fn' && n.name === 'abs' && containsVar(n, v);
    if (isAbs(t)) return { coef: N1, abs: t };
    if (t.type !== 'mul') return null;
    const withV = t.args.filter((a) => containsVar(a, v));
    if (withV.length !== 1 || !isAbs(withV[0])) return null;
    const rest = t.args.filter((a) => !containsVar(a, v));
    return { coef: rest.length === 1 ? rest[0] : mul(rest), abs: withV[0] };
}

/** Method of intervals for several absolute values with polynomial insides. */
function absIntervals(E, A, ctx) {
    const v = ctx.v;
    let pts = [];
    for (const a of A) {
        const P = Poly.fromNode(a.args[0], v);
        if (!P) return null;
        if (P.degree >= 1) pts.push(...solveAnyPoly(P, { v, domain: 'real' }).roots);
    }
    pts = mergeRoots(pts);
    if (pts.length > 12) return null;
    const steps = [S(T('Отмечаем нули подмодульных выражений', 'Mark the zeros of the expressions inside the absolute values'), {
        tex: byLang((l) => (pts.length ? pts.map((p) => `${v} = ${tex(p.node, l)}`).join(';\\ ') : '\\varnothing')),
        text: T('Между этими точками каждое подмодульное выражение сохраняет знак, поэтому модули раскрываются однозначно.', 'Between these points every expression inside keeps its sign, so each absolute value opens in one way.'),
    })];
    const bounds = [null, ...pts, null];
    let roots = [];
    let set = IntervalSet.empty();
    for (let k = 0; k + 1 < bounds.length; k++) {
        const lo = bounds[k];
        const hi = bounds[k + 1];
        const t = lo === null && hi === null ? 0 : lo === null ? hi.approx - 1 : hi === null ? lo.approx + 1 : (lo.approx + hi.approx) / 2;
        const Ei = simpOr(mapNode(E, (n) => {
            if (n.type !== 'fn' || n.name !== 'abs' || !containsVar(n, v)) return undefined;
            const s = approxOf(n.args[0], { [v]: t });
            return s >= 0 ? n.args[0] : neg(n.args[0]);
        }));
        const where = byLang((l) => {
            if (lo === null && hi === null) return l === 'ru' ? 'При всех $x$' : 'For all $x$';
            const a = lo && tex(lo.node, l);
            const b = hi && tex(hi.node, l);
            const w = lo === null ? `${v} < ${b}` : hi === null ? `${v} \\ge ${a}` : `${a} \\le ${v} < ${b}`;
            return (l === 'ru' ? 'При ' : 'For ') + `$${w}$`;
        });
        const sub = subSolve(Ei, N0, ctx);
        if (sub.kind === 'unsupported') return null;
        const inside = (r) => typeof r.approx === 'number' && (lo === null || r.approx >= lo.approx - 1e-9) && (hi === null || r.approx <= hi.approx + 1e-9);
        let txt;
        if (sub.kind === 'all') {
            set = set.union(IntervalSet.interval(lo && lo.node, hi && hi.node, lo !== null, hi !== null));
            txt = T('Получилось верное равенство — подходит весь промежуток.', 'A true equality: the whole interval fits.');
        } else {
            const ok = sub.roots.filter(inside);
            const no = sub.roots.filter((r) => !inside(r));
            roots.push(...ok);
            txt = no.length
                ? T(`Не входит в промежуток: $${no.map((r) => tex(r.node)).join(';\\ ')}$.`, `Outside the interval: $${no.map((r) => tex(r.node, 'en')).join(',\\ ')}$.`)
                : ok.length ? T('Корень входит в промежуток.', 'The root lies in the interval.') : T('Корней на этом промежутке нет.', 'No roots on this interval.');
        }
        steps.push(S(where, {
            tex: byLang((l) => `${tex(Ei, l)} = 0 \\;\\Rightarrow\\; ${sub.kind === 'all' ? (l === 'ru' ? '\\text{верно всегда}' : '\\text{always true}') : rootsTex(sub.roots, v, l)}`),
            text: txt,
            sub: sub.steps,
        }));
    }
    roots = mergeRoots(roots);
    if (!set.isEmpty()) {
        const full = set.union(IntervalSet.points(roots.map((r) => r.node)));
        return { kind: 'set', roots, set: full, steps, type: 'abs' };
    }
    return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'abs' };
}

// ---------------------------------------------------------------- radicals (irrational equations)

const isRadical = (n, v) => n.type === 'pow' && containsVar(n.base, v) && (() => {
    const e = numValue(n.exp);
    return !!e && !e.isInt();
})();

const hasRadical = (node, v) => nodeSome(node, (n) => isRadical(n, v));

/** A term c·R with a constant c and a single radical factor R → {coef, R}. */
function splitRadicalTerm(t, v) {
    if (isRadical(t, v)) return { coef: N1, R: t };
    if (t.type !== 'mul') return null;
    const withV = t.args.filter((a) => containsVar(a, v));
    if (withV.length !== 1 || !isRadical(withV[0], v)) return null;
    const rest = t.args.filter((a) => !containsVar(a, v));
    return { coef: rest.length === 1 ? rest[0] : mul(rest), R: withV[0] };
}

function solveRadical(lhs, rhs, E, ctx) {
    const v = ctx.v;
    if (ctx.depth > 6) return null;
    const terms = termsOfSum(E);
    const rads = terms.filter((t) => hasRadical(t, v));
    if (!rads.length) return null;
    // prefer the radical that stands alone on a side of the original equation
    const alone = [lhs, rhs].map((s) => simpOr(s)).find((s) => isRadical(s, v));
    let pickT = alone && rads.find((t) => nodeKey(splitRadicalTerm(t, v)?.R ?? N0) === nodeKey(alone));
    pickT = pickT ?? rads.find((t) => splitRadicalTerm(t, v));
    if (!pickT) return null;
    const { coef, R } = splitRadicalTerm(pickT, v);
    const others = terms.filter((t) => t !== pickT);
    const g = simpOr(div(neg(sumNode(others)), coef));
    const e = numValue(R.exp);
    const p = e.n;
    const q = e.d;
    if (p < 0n || q > 6n || p > 6n) return null;
    const f = R.base;
    const steps = [];
    const eqRT = byLang((l) => `${tex(R, l)} = ${tex(g, l)}`);
    if (!isolated(lhs, rhs, R, g)) steps.push(S(T('Уединяем корень', 'Isolate the root'), { tex: eqRT }));
    const even = q % 2n === 0n;
    const gConst = !containsVar(g, v);
    if (even && gConst && approxOf(g) < 0 && exactZero(g) !== true) {
        steps.push(S(T('Корень чётной степени не бывает отрицательным — корней нет', 'An even root is never negative: no roots')));
        return { kind: 'none', roots: [], steps, type: 'radical' };
    }
    const qn2 = Number(q);
    const lhs2 = expd(p === 1n ? f : pow(f, num(p))) ?? f;
    const rhs2 = expd(pow(g, num(q))) ?? pow(g, num(q));
    const gNonNeg = !gConst && hasRadical(g, v) && termsOfSum(simpOr(g)).every((t) => isRadical(t, v) && numValue(t.exp).d % 2n === 0n);
    const powWord = qn2 === 2 ? T('в квадрат', 'squared') : qn2 === 3 ? T('в куб', 'cubed') : T(`в степень ${qn2}`, `to the power ${qn2}`);
    steps.push(S(T(`Возводим обе части ${powWord.ru}`, `Raise both sides: ${powWord.en}`), {
        tex: byLang((l) => `${tex(lhs2, l)} = ${tex(rhs2, l)}`),
        text: even
            ? (gConst || gNonNeg
                ? T('При возведении в чётную степень могут появиться посторонние корни — все найденные корни проверим подстановкой.', 'Raising to an even power may add extraneous roots, so we will check every root by substitution.')
                : T(`Корень чётной степени неотрицателен, поэтому нужно $${tex(g)} \\ge 0$. Возведение в квадрат может добавить посторонние корни (оно решает сразу и $${tex(R)} = ${tex(g)}$, и $${tex(R)} = -(${tex(g)})$) — их отсеем.`,
                    `An even root is non-negative, so we need $${tex(g, 'en')} \\ge 0$. Squaring may add extraneous roots (it solves both $${tex(R, 'en')} = ${tex(g, 'en')}$ and $${tex(R, 'en')} = -(${tex(g, 'en')})$), and we will weed them out.`))
            : T('Нечётная степень — преобразование равносильное, посторонних корней не появится.', 'An odd power is an equivalent transformation: no extraneous roots appear.'),
    }));
    const sub = subSolve(lhs2, rhs2, ctx);
    if (sub.kind === 'unsupported' || sub.periodic) return null;
    pushPart(steps, lhs2, rhs2, sub, v);
    if (sub.kind === 'all' || sub.kind === 'set') return null;
    let roots = sub.roots;
    if (even && !gConst) {
        const bad = [];
        const good = [];
        for (const r of roots) {
            const gv = approxOf(g, { [v]: r.approx });
            if (Number.isFinite(gv) && gv < -1e-9 && (r.approxOnly || exactZero(substitute(g, { [v]: r.node })) !== true)) bad.push(r);
            else good.push(r);
        }
        if (bad.length) {
            reject(ctx, bad, 'sign');
            steps.push(S(T(`Отбрасываем корни, при которых $${tex(g)} < 0$`, `Drop the roots where $${tex(g, 'en')} < 0$`), {
                tex: byLang((l) => bad.map((r) => `${v} = ${tex(r.node, l)}:\\ ${tex(substitute(g, { [v]: r.node }), l)} = ${tex(simpOr(substitute(g, { [v]: r.node })), l)} < 0`).join(';\\ ')),
                text: T('Это посторонние корни: корень чётной степени не может равняться отрицательному числу.', 'These are extraneous: an even root cannot equal a negative number.'),
            }));
        }
        roots = good;
    }
    return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'radical', numeric: sub.numeric };
}

// ---------------------------------------------------------------- powers of a common base

const E_SYM = sym('e');
const isE = (n) => n.type === 'sym' && n.name === 'e' && !n.var;

/** q = c^k with the smallest c > 1 (k integer, negative for q < 1); q > 0, q ≠ 1. */
function primitivePower(q) {
    if (q.lt(1)) {
        const [c, k] = primitivePower(q.inv());
        return [c, -k];
    }
    const bits = Math.max(q.n.toString(2).length, q.d.toString(2).length);
    for (let k = Math.min(bits, 64); k >= 2; k--) {
        const r = q.exactRoot(k);
        if (r && !r.isOne()) return [r, k];
    }
    return [q, 1];
}

/** base node → {c: Q | 'e', k: Q} with base = c^k, or null. */
function baseInfo(b) {
    if (b.type === 'num' && b.value.isPos() && !b.value.isOne()) {
        const [c, k] = primitivePower(b.value);
        return { c, k: new Q(BigInt(k)) };
    }
    if (isE(b)) return { c: 'e', k: Q.ONE };
    if (b.type === 'pow' && b.exp.type === 'num') {
        const inner = baseInfo(b.base);
        return inner && { c: inner.c, k: inner.k.mul(b.exp.value) };
    }
    return null;
}

const sameBase = (a, b) => (a === 'e' || b === 'e' ? a === b : a.eq(b));
const baseNode = (c) => (c === 'e' ? E_SYM : num(c));

/** R = c^r with rational r → r, else null. */
function exactPower(c, R) {
    const s = simpOr(R);
    if (s.type === 'num' && s.value.isOne()) return Q.ZERO;
    const bi = s.type === 'num' || isE(s) || s.type === 'pow' ? baseInfo(s) : null;
    if (bi && sameBase(bi.c, c)) return bi.k;
    return null;
}

/** log_c(x) node: ln, lg or log_c. */
function logNode(c, x) {
    if (c === 'e') return fn('ln', x);
    if (c instanceof Q && c.eq(10)) return fn('lg', x);
    return fn('log', c instanceof Q ? num(c) : c, x);
}

/** log with a base given as a node. */
function logNodeB(b, x) {
    if (isE(b)) return fn('ln', x);
    if (b.type === 'num' && b.value.eq(10)) return fn('lg', x);
    return fn('log', b, x);
}

// ---------------------------------------------------------------- exponential equations

function analyzeExp(E, v) {
    let c = null;
    let mixed = false;
    const terms = [];
    const constant = [];
    for (const t of termsOfSum(E)) {
        if (!containsVar(t, v)) {
            constant.push(t);
            continue;
        }
        const fs = t.type === 'mul' ? t.args : [t];
        const coefF = [];
        const gs = [];
        const pows = [];
        for (const f of fs) {
            if (!containsVar(f, v)) {
                coefF.push(f);
                continue;
            }
            if (f.type !== 'pow' || containsVar(f.base, v)) return null;
            const bi = baseInfo(f.base);
            if (!bi) return null;
            if (c === null) c = bi.c;
            else if (!sameBase(c, bi.c)) mixed = true;
            gs.push(simpOr(mul(num(bi.k), f.exp)));
            pows.push(f);
        }
        terms.push({ coef: coefF.length ? simpOr(coefF.length === 1 ? coefF[0] : mul(coefF)) : N1, g: gs.length === 1 ? gs[0] : simpOr(add(gs)), pows, t });
    }
    if (!terms.length) return null;
    return { c, terms, constant: simpOr(sumNode(constant)), mixed };
}

/** a^f · b^f → (ab)^f inside each term (numeric bases), or null when nothing merges. */
function mergeSameExponent(E, v) {
    let changed = false;
    const terms = termsOfSum(E).map((t) => {
        if (t.type !== 'mul') return t;
        const groups = new Map();
        const rest = [];
        for (const f of t.args) {
            if (f.type === 'pow' && f.base.type === 'num' && f.base.value.isPos() && containsVar(f.exp, v)) {
                const k = nodeKey(f.exp);
                const g = groups.get(k);
                if (g) {
                    g.base = g.base.mul(f.base.value);
                    g.n++;
                } else groups.set(k, { base: f.base.value, exp: f.exp, n: 1 });
            } else rest.push(f);
        }
        if (![...groups.values()].some((g) => g.n > 1)) return t;
        changed = true;
        return mul([...rest, ...[...groups.values()].map((g) => pow(num(g.base), g.exp))]);
    });
    return changed ? simpOr(sumNode(terms)) : null;
}

function solveExponential(lhs, rhs, E, ctx) {
    const v = ctx.v;
    const merged = mergeSameExponent(E, v);
    if (merged) {
        const r = solveExponential(lhs, rhs, merged, ctx);
        if (!r) return null;
        const pre = S(T('Перемножаем степени с одинаковыми показателями', 'Multiply the powers with equal exponents'), {
            tex: byLang((l) => `${tex(merged, l)} = 0`),
            text: T('$a^{f} \\cdot b^{f} = (ab)^{f}$.', '$a^{f} \\cdot b^{f} = (ab)^{f}$.'),
        });
        return { ...r, steps: [pre, ...r.steps] };
    }
    const info = analyzeExp(E, v);
    if (!info) return null;
    if (info.mixed) return solveExpMixed(info, ctx);
    const { c, terms, constant } = info;
    const cN = baseNode(c);
    const steps = [];
    const positive = T('Степень положительного числа всегда положительна — корней нет.', 'A power of a positive number is always positive: no roots.');
    if (terms.length === 1) {
        const { coef, g, pows } = terms[0];
        const R = simpOr(div(neg(constant), coef));
        const single = pows.length === 1;
        const b = single ? pows[0].base : cN;
        const f = single ? pows[0].exp : g;
        const left = single ? pows[0] : pow(cN, g);
        if (!isolated(lhs, rhs, left, R)) steps.push(S(T('Уединяем степень', 'Isolate the power'), { tex: byLang((l) => `${tex(left, l)} = ${tex(R, l)}`) }));
        const Rv = approxOf(R);
        if (!(Rv > 0) || exactZero(R) === true) {
            steps.push(S(T('Справа неположительное число', 'The right side is not positive'), { text: positive }));
            return { kind: 'none', roots: [], steps, type: 'exponential' };
        }
        const rb = single ? exactPower(baseInfo(b).c, R) : null;
        const kb = single ? baseInfo(b).k : Q.ONE;
        const rc = exactPower(c, R);
        let sub;
        if (rc !== null) {
            const rOwn = rc.div(kb); // R = b^(rc/kb)
            const rOwnOk = single && rb !== null;
            if (rOwnOk && (rOwn.isInt() || kb.isOne())) {
                steps.push(S(T(`Записываем правую часть как степень числа $${tex(b)}$`, `Write the right side as a power of $${tex(b, 'en')}$`), {
                    tex: byLang((l) => `${tex(left, l)} = ${tex(pow(b, num(rOwn)), l)}`),
                    text: T('Основания равны — значит, равны и показатели (показательная функция монотонна).', 'The bases are equal, so the exponents are equal too (an exponential function is monotonic).'),
                }));
                sub = subSolve(f, num(rOwn), ctx);
                pushPart(steps, f, num(rOwn), sub, v);
            } else {
                steps.push(S(T(`Приводим обе части к основанию $${tex(cN)}$`, `Write both sides as powers of $${tex(cN, 'en')}$`), {
                    tex: byLang((l) => `${tex(pow(cN, g), l)} = ${tex(pow(cN, num(rc)), l)}`),
                    text: T('Основания равны — приравниваем показатели.', 'The bases are equal, so we equate the exponents.'),
                }));
                sub = subSolve(g, num(rc), ctx);
                pushPart(steps, g, num(rc), sub, v);
            }
        } else {
            const Lg = logNodeB(b, R);
            steps.push(S(T(`Логарифмируем по основанию $${tex(b)}$`, `Take the logarithm to base $${tex(b, 'en')}$`), {
                tex: byLang((l) => `${tex(f, l)} = ${tex(Lg, l)}`),
                text: T(`По определению логарифма: $${tex(b)}^{y} = a \\Leftrightarrow y = ${tex(logNodeB(b, sym('a')))}$.`, `By the definition of the logarithm: $${tex(b, 'en')}^{y} = a \\Leftrightarrow y = ${tex(logNodeB(b, sym('a')), 'en')}$.`),
            }));
            sub = subSolve(f, Lg, ctx);
            pushPart(steps, f, Lg, sub, v);
        }
        if (sub.kind === 'unsupported') return null;
        return { ...sub, steps, type: 'exponential' };
    }
    if (terms.length === 2 && isZeroNode(constant)) {
        const K = simpOr(div(neg(terms[1].coef), terms[0].coef));
        const [g1, g2] = [terms[0].g, terms[1].g];
        const Kv = approxOf(K);
        if (!(Kv > 0)) {
            steps.push(S(T('Степени с разными знаками', 'Powers of opposite signs'), { text: positive }));
            return { kind: 'none', roots: [], steps, type: 'exponential' };
        }
        if (exactZero(add(K, num(-1))) === true) {
            steps.push(S(T(`Приводим обе части к основанию $${tex(cN)}$`, `Write both sides as powers of $${tex(cN, 'en')}$`), {
                tex: byLang((l) => `${tex(pow(cN, g1), l)} = ${tex(pow(cN, g2), l)}`),
                text: T('Основания равны — приравниваем показатели.', 'The bases are equal, so we equate the exponents.'),
            }));
            const sub = subSolve(g1, g2, ctx);
            if (sub.kind === 'unsupported') return null;
            pushPart(steps, g1, g2, sub, v);
            return { ...sub, steps, type: 'exponential' };
        }
        const g = simpOr(add(g1, neg(g2)));
        steps.push(S(T(`Делим обе части на $${tex(pow(cN, g2))}$`, `Divide both sides by $${tex(pow(cN, g2), 'en')}$`), {
            tex: byLang((l) => `${tex(pow(cN, g), l)} = ${tex(K, l)}`),
            text: T('Степень положительна, поэтому делить можно.', 'A power is positive, so the division is allowed.'),
        }));
        const sub = subSolve(pow(cN, g), K, ctx);
        if (sub.kind === 'unsupported') return null;
        steps.push(...sub.steps);
        return { ...sub, steps, type: 'exponential' };
    }
    // substitution t = c^(m·x)
    const lin = [];
    for (const t of terms) {
        const lf = linearForm(t.g, [v]);
        const k = numValue(t.coef);
        if (!lf || !k || lf.coeffs[v].isZero()) return null;
        lin.push({ m: lf.coeffs[v], s: lf.constant, k, t });
    }
    let m = lin[0].m.abs();
    for (const x of lin) m = qGcd(m, x.m.abs());
    const C0 = numValue(constant);
    if (!C0) return null;
    const coefs = new Map();
    let jmin = 0;
    for (const x of lin) {
        const j = x.m.div(m);
        if (!j.isInt()) return null;
        let cs;
        if (x.s.isZero()) cs = Q.ONE;
        else if (c !== 'e' && x.s.isInt()) cs = c.pow(x.s.n);
        else return null;
        const jj = Number(j.n);
        jmin = Math.min(jmin, jj);
        coefs.set(jj, (coefs.get(jj) ?? Q.ZERO).add(x.k.mul(cs)));
    }
    coefs.set(0, (coefs.get(0) ?? Q.ZERO).add(C0));
    const maxJ = Math.max(...coefs.keys());
    if (maxJ - jmin > 8) return null;
    const arr = new Array(maxJ - jmin + 1).fill(Q.ZERO);
    for (const [j, q] of coefs) arr[j - jmin] = arr[j - jmin].add(q);
    const Pt = new Poly(arr);
    if (Pt.degree < 1) return null;
    const Bq = c !== 'e' && m.isInt() ? c.pow(m.n) : null;
    const tNode = Bq ? pow(num(Bq), sym(v)) : pow(cN, simpOr(mul(num(m), sym(v))));
    const tTex = (l) => tex(tNode, l);
    const tSym = sym('t');
    const rewrites = (l) => lin.map((x) => {
        const j = x.m.div(m);
        const cs = x.s.isZero() ? Q.ONE : c.pow(x.s.n);
        const node = simpOr(mul(num(x.k.mul(cs)), pow(tSym, num(j))));
        return `${tex(x.t.t, l)} = ${tex(node, l)}`;
    }).join(l === 'ru' ? ';\\ ' : ',\\ ');
    steps.push(S(T(`Замена $t = ${tTex('ru')}$, где $t > 0$`, `Substitute $t = ${tTex('en')}$, where $t > 0$`), {
        tex: byLang((l) => `${polyTex(Pt, 't', l)} = 0`),
        text: T(`Все степени выражаются через $t$: $${rewrites('ru')}$${jmin < 0 ? `; умножили обе части на $t^{${-jmin}}$ (это не ноль)` : ''}.`, `Every power is expressed through $t$: $${rewrites('en')}$${jmin < 0 ? `; we multiplied both sides by $t^{${-jmin}}$ (it is not zero)` : ''}.`),
    }));
    const tr = solveAnyPoly(Pt, { v: 't', domain: 'real' });
    steps.push(partStep(byLang((l) => `${polyTex(Pt, 't', l)} = 0`), tr, 't'));
    const good = tr.roots.filter((r) => r.approx > 1e-12);
    const bad = tr.roots.filter((r) => !(r.approx > 1e-12));
    if (bad.length) {
        steps.push(S(T('Отбрасываем $t \\le 0$', 'Drop $t \\le 0$'), {
            tex: byLang((l) => bad.map((r) => `t = ${tex(r.node, l)}`).join(',\\ ')),
            text: T(`$${tTex('ru')} > 0$ при любом $${v}$.`, `$${tTex('en')} > 0$ for every $${v}$.`),
        }));
    }
    let roots = [];
    let numeric = !!tr.numeric;
    for (const r of good) {
        const sub = subSolve(tNode, r.node, ctx);
        if (sub.kind === 'unsupported') return null;
        roots.push(...sub.roots);
        if (sub.numeric) numeric = true;
        steps.push(partStep(byLang((l) => `${tTex(l)} = ${tex(r.node, l)}`), sub, v));
    }
    roots = mergeRoots(roots);
    return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'exponential', numeric };
}

/** a^f = K·b^g with different bases: take logarithms of both sides. */
function solveExpMixed(info, ctx) {
    const v = ctx.v;
    const { terms, constant } = info;
    if (terms.length !== 2 || !isZeroNode(constant) || terms.some((t) => t.pows.length !== 1)) return null;
    const [A, B] = terms;
    const K = simpOr(div(neg(B.coef), A.coef));
    const steps = [];
    const left = A.pows[0];
    const right = simpOr(mul(K, B.pows[0]));
    steps.push(S(T('Переносим степени в разные части', 'Put the powers on different sides'), { tex: byLang((l) => `${tex(left, l)} = ${tex(right, l)}`) }));
    if (!(approxOf(K) > 0)) {
        steps.push(S(T('Части разных знаков', 'The sides have opposite signs'), { text: T('Степени положительны, а коэффициент отрицателен — корней нет.', 'The powers are positive and the coefficient is negative: no roots.') }));
        return { kind: 'none', roots: [], steps, type: 'exponential' };
    }
    const lhs2 = mul(left.exp, fn('ln', left.base));
    const rhs2 = add(fn('ln', K), mul(B.pows[0].exp, fn('ln', B.pows[0].base)));
    const l2 = simpOr(lhs2);
    const r2 = simpOr(rhs2);
    steps.push(S(T('Логарифмируем обе части (натуральным логарифмом)', 'Take the natural logarithm of both sides'), {
        tex: byLang((l) => `${tex(l2, l)} = ${tex(r2, l)}`),
        text: T('Обе части положительны, поэтому логарифмировать можно; $\\ln a^{f} = f\\ln a$.', 'Both sides are positive, so we may take logarithms; $\\ln a^{f} = f\\ln a$.'),
    }));
    const E2 = simpOr(add(l2, neg(r2)));
    const sub = solveNodePoly(E2, ctx);
    if (!sub) return null;
    steps.push(...sub.steps);
    return { ...sub, steps, type: 'exponential' };
}

// ---------------------------------------------------------------- logarithmic equations

function logInfoOf(f, v) {
    if (f.type !== 'fn') return null;
    if (f.name === 'ln') return { c: 'e', k: Q.ONE, arg: f.args[0], base: E_SYM };
    if (f.name === 'lg') return { c: new Q(10n), k: Q.ONE, arg: f.args[0], base: num(10) };
    if (f.name !== 'log') return null;
    const b = f.args[0];
    if (containsVar(b, v)) return { varBase: true, arg: f.args[1], base: b };
    const bi = baseInfo(b);
    return bi && { c: bi.c, k: bi.k, arg: f.args[1], base: b };
}

function analyzeLog(E, v) {
    const vt = [];
    const constant = [];
    for (const t of termsOfSum(E)) {
        if (!containsVar(t, v)) {
            constant.push(t);
            continue;
        }
        const fs = t.type === 'mul' ? t.args : [t];
        const withV = fs.filter((f) => containsVar(f, v));
        if (withV.length !== 1) return null;
        let F = withV[0];
        let p = 1;
        if (F.type === 'pow') {
            const e = numValue(F.exp);
            if (!e || !e.isInt() || !e.isPos() || e.gt(6)) return null;
            p = Number(e.n);
            F = F.base;
        }
        const info = logInfoOf(F, v);
        if (!info || !containsVar(F, v)) return null;
        const rest = fs.filter((f) => !containsVar(f, v));
        vt.push({ coef: rest.length ? simpOr(rest.length === 1 ? rest[0] : mul(rest)) : N1, p, F, info, t });
    }
    if (!vt.length) return null;
    return { vt, constant };
}

/**
 * A common exponential factor: x²·2ˣ − 4·2ˣ = 0 → 2ˣ(x² − 4) = 0, and 2ˣ > 0 is never zero, so x² − 4 = 0.
 * Only when dividing it out leaves no power with the unknown in the exponent.
 */
function solveCommonExp(lhs, rhs, E, ctx) {
    const v = ctx.v;
    if (E.type !== 'add') return null;
    const varExp = (n) => n.type === 'pow' && !containsVar(n.base, v) && containsVar(n.exp, v) && ((n.base.type === 'num' && n.base.value.isPos() && !n.base.value.isOne()) || isE(n.base));
    const first = E.args[0].type === 'mul' ? E.args[0].args : [E.args[0]];
    for (const F of first.filter(varExp)) {
        const rest = expd(mul(E, pow(F, num(-1))));
        if (!rest || !containsVar(rest, v) || nodeSome(rest, (n) => n.type === 'pow' && containsVar(n.exp, v))) continue;
        const steps = [S(byLang((l) => (l === 'ru' ? `Выносим $${tex(F, l)}$ за скобки` : `Take $${tex(F, l)}$ out of the brackets`)), {
            tex: byLang((l) => `${tex(F, l)}\\left(${tex(rest, l)}\\right) = 0`),
            text: byLang((l) => (l === 'ru'
                ? `Показательная функция всегда положительна: $${tex(F, l)} > 0$, поэтому этот множитель нулю не равен и на него можно разделить: $${tex(rest, l)} = 0$.`
                : `An exponential is always positive: $${tex(F, l)} > 0$, so this factor is never zero and we may divide by it: $${tex(rest, l)} = 0$.`)),
        })];
        const sub = subSolve(rest, N0, ctx);
        if (sub.kind === 'unsupported' || sub.numeric) return null;
        steps.push(...sub.steps);
        return { ...sub, steps };
    }
    return null;
}

/**
 * A power with the unknown both in the base and in the exponent (x^(lg x) = 100x): take the logarithm of both
 * sides. The base is positive by the ОДЗ, so that side is positive and the other must be too; log turns
 * powers into products and products into sums. The roots are checked in the original equation afterwards.
 */
function solveTakeLog(lhs, rhs, E, ctx) {
    const v = ctx.v;
    const varPow = (n) => n.type === 'pow' && containsVar(n.base, v) && containsVar(n.exp, v);
    if (!nodeSome(E, varPow) && !nodeSome(lhs, varPow) && !nodeSome(rhs, varPow)) return null;
    // the logarithm the equation already speaks: lg, ln, log_a; lg by default
    let base = num(10);
    let lname = 'lg';
    const lf = outermost(add(lhs, rhs), (n) => n.type === 'fn' && (n.name === 'lg' || n.name === 'ln' || (n.name === 'log' && isConstNode(n.args[0]))))[0];
    if (lf?.name === 'ln') [base, lname] = [E_SYM, 'ln'];
    else if (lf?.name === 'log') [base, lname] = [lf.args[0], 'log'];
    const L = (x) => (lname === 'log' ? fn('log', base, x) : fn(lname, x));
    const positive = (n) => {
        if (n.type === 'num') return n.value.isPos();
        if (n.type === 'mul') return n.args.every(positive);
        if (n.type === 'pow') return (n.base.type === 'num' && n.base.value.isPos()) || (containsVar(n.base, v) && containsVar(n.exp, v)) || isE(n.base);
        return isE(n);
    };
    const logOf = (n) => {
        if (n.type === 'mul') {
            const parts = n.args.map(logOf);
            return parts.some((x) => !x) ? null : add(parts);
        }
        if (n.type === 'pow') {
            const b = logOf(n.base);
            return b && mul(n.exp, b);
        }
        if (n.type === 'num') return n.value.isPos() ? simpOr(L(n)) : null;
        return L(n);
    };
    const A = simpOr(lhs);
    const B = simpOr(rhs);
    if (!positive(A) && !positive(B)) return null;
    const LA = logOf(A);
    const LB = logOf(B);
    if (!LA || !LB) return null;
    const L1 = simpOr(expd(LA) ?? LA);
    const L2 = simpOr(expd(LB) ?? LB);
    const lt = (l) => (lname === 'ln' ? '\\ln' : lname === 'lg' ? (l === 'ru' ? '\\lg' : '\\log_{10}') : `\\log_{${tex(base, l)}}`);
    const steps = [S(T('Логарифмируем обе части', 'Take the logarithm of both sides'), {
        tex: byLang((l) => `${tex(L1, l)} = ${tex(L2, l)}`),
        text: T(`Основание степени с переменным показателем положительно (ОДЗ), значит, обе части положительны и от них можно взять $${lt('ru')}$. Логарифм степени — произведение: $${lt('ru')} a^{b} = b\\,${lt('ru')} a$, логарифм произведения — сумма.`,
            `The base of a power with a variable exponent is positive (the domain), so both sides are positive and we may take $${lt('en')}$ of them. The logarithm of a power is a product, $${lt('en')} a^{b} = b\\,${lt('en')} a$, and of a product a sum.`),
    })];
    const sub = subSolve(L1, L2, ctx);
    if (sub.kind === 'unsupported' || sub.numeric) return null;
    steps.push(...sub.steps);
    return { ...sub, steps, type: 'logarithmic' };
}

function solveLogarithmic(lhs, rhs, E, ctx) {
    const v = ctx.v;
    const an = analyzeLog(E, v);
    if (!an) return null;
    const { vt, constant } = an;
    const C = simpOr(sumNode(constant));
    const steps = [];
    const defText = T('По определению логарифма: $\\log_a b = c \\Leftrightarrow b = a^{c}$.', 'By the definition of the logarithm: $\\log_a b = c \\Leftrightarrow b = a^{c}$.');
    // a variable base: log_f(g) = R
    if (vt.some((x) => x.info.varBase)) {
        if (vt.length !== 1 || vt[0].p !== 1) return null;
        const { coef, info, F } = vt[0];
        const R = simpOr(div(neg(C), coef));
        if (!isConstNode(R)) return null;
        if (!isolated(lhs, rhs, F, R)) steps.push(S(T('Уединяем логарифм', 'Isolate the logarithm'), { tex: byLang((l) => `${tex(F, l)} = ${tex(R, l)}`) }));
        const l2 = expd(pow(info.base, R)) ?? pow(info.base, R);
        steps.push(S(T('Переходим к степени', 'Rewrite as a power'), { tex: byLang((l) => `${tex(l2, l)} = ${tex(info.arg, l)}`), text: defText }));
        const sub = subSolve(l2, info.arg, ctx);
        if (sub.kind === 'unsupported') return null;
        pushPart(steps, l2, info.arg, sub, v);
        return { ...sub, steps, type: 'logarithmic' };
    }
    const c = vt[0].info.c;
    if (vt.some((x) => !sameBase(x.info.c, c))) return null;
    const cN = baseNode(c);
    const args = new Set(vt.map((x) => nodeKey(x.info.arg)));
    const normalize = vt.some((x) => !x.info.k.isOne()) || new Set(vt.map((x) => nodeKey(x.info.base))).size > 1;
    // one argument: log_b(u) = R, or a polynomial in t = log_c(u)
    if (args.size === 1) {
        const u = vt[0].info.arg;
        if (vt.length === 1 && vt[0].p === 1) {
            const { coef, info, F } = vt[0];
            const R = simpOr(div(neg(C), coef));
            if (!isConstNode(R)) return null;
            if (!isolated(lhs, rhs, F, R)) steps.push(S(T('Уединяем логарифм', 'Isolate the logarithm'), { tex: byLang((l) => `${tex(F, l)} = ${tex(R, l)}`) }));
            const val = simpOr(pow(info.base, R));
            steps.push(S(T('Переходим от логарифма к степени', 'Go from the logarithm to a power'), {
                tex: byLang((l) => `${tex(u, l)} = ${tex(pow(info.base, R), l)}${nodeKey(val) !== nodeKey(pow(info.base, R)) ? ` = ${tex(val, l)}` : ''}`),
                text: defText,
            }));
            const sub = subSolve(u, val, ctx);
            if (sub.kind === 'unsupported') return null;
            pushPart(steps, u, val, sub, v);
            return { ...sub, steps, type: 'logarithmic' };
        }
        // polynomial in t
        const coefs = new Map();
        for (const x of vt) {
            const k = numValue(x.coef);
            if (!k) return null;
            const q = k.div(x.info.k.pow(x.p));
            coefs.set(x.p, (coefs.get(x.p) ?? Q.ZERO).add(q));
        }
        const C0 = numValue(C);
        if (!C0) return null;
        coefs.set(0, (coefs.get(0) ?? Q.ZERO).add(C0));
        const arr = new Array(Math.max(...coefs.keys()) + 1).fill(Q.ZERO);
        for (const [j, q] of coefs) arr[j] = q;
        const Pt = new Poly(arr);
        if (Pt.degree < 1) return null;
        const tN = logNode(c, u);
        steps.push(S(T(`Замена $t = ${tex(tN)}$`, `Substitute $t = ${tex(tN, 'en')}$`), {
            tex: byLang((l) => `${polyTex(Pt, 't', l)} = 0`),
            text: normalize ? T(`Логарифмы по разным основаниям переводим к основанию $${tex(cN)}$: $\\log_{a^k} u = \\frac{1}{k}\\log_a u$.`, `Logarithms to different bases are converted to base $${tex(cN, 'en')}$: $\\log_{a^k} u = \\frac{1}{k}\\log_a u$.`) : undefined,
        }));
        const tr = solveAnyPoly(Pt, { v: 't', domain: 'real' });
        steps.push(partStep(byLang((l) => `${polyTex(Pt, 't', l)} = 0`), tr, 't'));
        let roots = [];
        for (const r of tr.roots) {
            const val = simpOr(pow(cN, r.node));
            const sub = subSolve(u, val, ctx);
            if (sub.kind === 'unsupported') return null;
            roots.push(...sub.roots);
            steps.push(partStep(byLang((l) => `${tex(tN, l)} = ${tex(r.node, l)} \\quad\\Rightarrow\\quad ${tex(u, l)} = ${tex(val, l)}`), sub, v));
        }
        roots = mergeRoots(roots);
        return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'logarithmic' };
    }
    // several arguments: combine into one logarithm
    if (vt.some((x) => x.p !== 1)) return null;
    const ups = [];
    const downs = [];
    for (const x of vt) {
        const k = numValue(x.coef);
        if (!k) return null;
        const a = k.div(x.info.k);
        const piece = a.abs().isOne() ? x.info.arg : pow(x.info.arg, num(a.abs()));
        (a.isPos() ? ups : downs).push(piece);
    }
    // constant logarithms of the same base go to the right side as one logarithm
    const cUps = [];
    const cDowns = [];
    const rest = [];
    for (const t of constant) {
        const fs = t.type === 'mul' ? t.args : [t];
        const lg = fs.filter((f) => f.type === 'fn' && logInfoOf(f, v) && !logInfoOf(f, v).varBase);
        const k = numValue(simpOr(mul(fs.filter((f) => !lg.includes(f)).length ? fs.filter((f) => !lg.includes(f)) : [N1])));
        if (lg.length === 1 && k) {
            const info = logInfoOf(lg[0], v);
            if (sameBase(info.c, c)) {
                const a = k.div(info.k).neg();
                const piece = a.abs().isOne() ? info.arg : pow(info.arg, num(a.abs()));
                (a.isPos() ? cUps : cDowns).push(piece);
                continue;
            }
        }
        rest.push(t);
    }
    const R = simpOr(neg(sumNode(rest)));
    const prod = (xs) => (xs.length ? (xs.length === 1 ? xs[0] : mul(xs)) : N1);
    const F = downs.length ? div(prod(ups), prod(downs)) : prod(ups);
    const G = cDowns.length ? div(prod(cUps), prod(cDowns)) : prod(cUps);
    const Gs = simpOr(G);
    const hasG = !(Gs.type === 'num' && Gs.value.isOne());
    const K = simpOr(mul(Gs, pow(cN, R)));
    const logF = logNode(c, F);
    const rightT = (l) => (hasG ? (isZeroNode(R) ? tex(logNode(c, Gs), l) : `${tex(logNode(c, Gs), l)} ${approxOf(R) < 0 ? '' : '+'} ${tex(R, l)}`) : tex(R, l));
    const simpleEq = vt.length === 2 && !hasG && isZeroNode(R) && ups.length === 1 && downs.length === 1 && vt.every((x) => numValue(x.coef)?.abs().isOne() && x.info.k.isOne());
    if (simpleEq) {
        steps.push(S(T('Логарифмы с равными основаниями равны — равны и их аргументы', 'Equal logarithms to the same base: the arguments are equal'), {
            tex: byLang((l) => `${tex(ups[0], l)} = ${tex(downs[0], l)}`),
            text: T('Логарифмическая функция монотонна. Переход не учитывает ОДЗ — корни проверим по ней.', 'The logarithm is monotonic. This step ignores the domain, so we check the roots against it.'),
        }));
        const sub = subSolve(ups[0], downs[0], ctx);
        if (sub.kind === 'unsupported') return null;
        pushPart(steps, ups[0], downs[0], sub, v);
        return { ...sub, steps, type: 'logarithmic' };
    }
    steps.push(S(T('Собираем логарифмы в один', 'Combine the logarithms into one'), {
        tex: byLang((l) => `${tex(logF, l)} = ${rightT(l)}`),
        text: T(`Свойства: $\\log_a m + \\log_a n = \\log_a(mn)$, $\\log_a m - \\log_a n = \\log_a\\frac{m}{n}$, $k\\log_a m = \\log_a m^{k}$. Они верны при $m, n > 0$, поэтому корни потом сверим с ОДЗ.${normalize ? ` Логарифмы переведены к основанию $${tex(cN)}$.` : ''}`,
            `The rules $\\log_a m + \\log_a n = \\log_a(mn)$, $\\log_a m - \\log_a n = \\log_a\\frac{m}{n}$, $k\\log_a m = \\log_a m^{k}$ hold for $m, n > 0$, so we check the roots against the domain later.${normalize ? ` All logarithms are converted to base $${tex(cN, 'en')}$.` : ''}`),
    }));
    steps.push(S(T('Переходим от логарифма к аргументам', 'Pass from the logarithms to their arguments'), {
        tex: byLang((l) => `${tex(F, l)} = ${tex(K, l)}`),
        text: defText,
    }));
    const sub = subSolve(F, K, ctx);
    if (sub.kind === 'unsupported') return null;
    pushPart(steps, F, K, sub, v);
    return { ...sub, steps, type: 'logarithmic' };
}

// ---------------------------------------------------------------- trigonometric equations

const TRIG_FN = ['sin', 'cos', 'tan', 'cot'];
const PH = { sin: '__s', cos: '__c', tan: '__t', cot: '__k' };
const N_SYM = sym('n');
const ZZ = (l) => (l === 'ru' ? ',\\ n \\in \\mathbb{Z}' : ',\\ n \\in \\mathbb{Z}');

/** u = k·x + s with rational k ≠ 0 and a constant s → {k, s}. */
function linArg(u, v) {
    let ct;
    try {
        ct = collectTerms(u, v);
    } catch {
        return null;
    }
    if (!ct || !ct.has(1) || ![...ct.keys()].every((d) => d === 0 || d === 1)) return null;
    const k = numValue(ct.get(1));
    if (!k || k.isZero()) return null;
    const s = ct.get(0) ?? N0;
    return isConstNode(s) ? { k, s } : null;
}

/** A family x = base + period·n; gid groups families that are printed together. */
function mkFamily(base, period, gid = null) {
    const b = simpOr(base);
    const p = simpOr(period);
    return { base: b, period: p, b: approxOf(b), p: approxOf(p), gid };
}

/** "a + b" of already simplified terms (zeros dropped), printed without re-simplifying. */
function plusTex(nodes, lang) {
    const ns = nodes.filter((n) => !isZeroNode(n));
    if (!ns.length) return '0';
    return tex(ns.length === 1 ? ns[0] : add(ns), lang);
}

const signedTex = (t) => (t.startsWith('-') ? ` ${t}` : ` + ${t}`);
const periodN = (p) => simpOr(mul(p, N_SYM));

function familyTex(f, v, lang) {
    return `${v} = ${plusTex([f.base, periodN(f.period)], lang)}`;
}

/** Answer lines for a list of families: the group's school form when intact, else one line per family. */
function familiesTex(fams, v, lang, sep) {
    const lines = [];
    const done = new Set();
    for (const f of fams) {
        if (f.group && !done.has(f.group)) {
            const members = fams.filter((g) => g.group === f.group);
            if (members.length === f.group.size) {
                lines.push(pick(f.group.tex, lang));
                done.add(f.group);
                continue;
            }
        }
        if (f.group && done.has(f.group)) continue;
        lines.push(familyTex(f, v, lang));
    }
    return lines.join(sep ?? (lang === 'ru' ? ';\\quad ' : ',\\quad ')) + ZZ(lang);
}

function familiesToRoots(fams) {
    return fams.map((f) => ({ node: simpOr(add(f.base, mul(f.period, N_SYM))), approx: f.b, mult: 1, family: { base: f.base, period: f.period, param: 'n' } }));
}

/** Is family a (base a, period p) contained in family b? */
function famSubset(a, b) {
    const r = a.p / b.p;
    if (Math.abs(r - Math.round(r)) > 1e-9 || Math.round(r) < 1) return false;
    const d = (a.b - b.b) / b.p;
    return Math.abs(d - Math.round(d)) <= 1e-9;
}

/** Drop families contained in others; join m families with a common period into one with period/m. */
function mergeFamilies(fams) {
    let out = [];
    for (const f of fams) {
        if (out.some((g) => famSubset(f, g))) continue;
        out = out.filter((g) => !famSubset(g, f));
        out.push(f);
    }
    // join: two families with equal period P whose bases differ by an odd multiple of P/2
    let changed = true;
    while (changed) {
        changed = false;
        for (let i = 0; i < out.length && !changed; i++) {
            for (let j = i + 1; j < out.length && !changed; j++) {
                const f = out[i];
                const g = out[j];
                if (Math.abs(f.p - g.p) > 1e-12 * Math.max(1, f.p)) continue;
                const d = (g.b - f.b) / (f.p / 2);
                const r = Math.round(d);
                if (Math.abs(d - r) > 1e-9 || r % 2 === 0) continue;
                const first = Math.abs(g.b) < Math.abs(f.b) - 1e-12 ? g : f;
                const nf = mkFamily(first.base, div(first.period, num(2)));
                out = out.filter((x) => x !== f && x !== g);
                out.push(nf);
                changed = true;
            }
        }
    }
    return out.sort((a, b) => a.p - b.p || a.b - b.b);
}

const TRIG_NAME = { sin: T('синус', 'sine'), cos: T('косинус', 'cosine'), tan: T('тангенс', 'tangent'), cot: T('котангенс', 'cotangent') };

/** F(u) = a for u = kx + s → {families, steps}. */
function basicTrig(F, u, a, ctx) {
    const v = ctx.v;
    const la = linArg(u, v);
    if (!la) return null;
    const aS = simpOr(a);
    const av = approxOf(aS);
    if (!Number.isFinite(av)) return null;
    const eqT = (l) => `${tex(fn(F, u), l)} = ${tex(aS, l)}`;
    const title = byLang((l) => (l === 'ru' ? `Решаем $${eqT(l)}$` : `Solve $${eqT(l)}$`));
    if ((F === 'sin' || F === 'cos') && Math.abs(av) > 1 + 1e-12) {
        return {
            families: [],
            steps: [S(title, { text: T(`${F === 'sin' ? 'Синус' : 'Косинус'} принимает значения только от $-1$ до $1$, а $|${tex(aS)}| > 1$ — корней нет.`, `The ${TRIG_NAME[F].en} only takes values from $-1$ to $1$, and $|${tex(aS, 'en')}| > 1$: no roots.`) })],
        };
    }
    const is = (x) => Math.abs(av - x) < 1e-12 && exactZero(add(aS, num(-x))) !== false;
    const twoPi = mul(num(2), PI);
    const halfPi = mul(num(Q.HALF), PI);
    let uf;
    let A = null;
    let rule;
    let general = false;
    if (F === 'sin') {
        if (is(0)) [uf, rule] = [[[N0, PI]], T('Частный случай: $\\sin t = 0 \\Leftrightarrow t = \\pi n$.', 'A special case: $\\sin t = 0 \\Leftrightarrow t = \\pi n$.')];
        else if (is(1)) [uf, rule] = [[[halfPi, twoPi]], T('Частный случай: $\\sin t = 1 \\Leftrightarrow t = \\frac{\\pi}{2} + 2\\pi n$.', 'A special case: $\\sin t = 1 \\Leftrightarrow t = \\frac{\\pi}{2} + 2\\pi n$.')];
        else if (is(-1)) [uf, rule] = [[[neg(halfPi), twoPi]], T('Частный случай: $\\sin t = -1 \\Leftrightarrow t = -\\frac{\\pi}{2} + 2\\pi n$.', 'A special case: $\\sin t = -1 \\Leftrightarrow t = -\\frac{\\pi}{2} + 2\\pi n$.')];
        else {
            A = simpOr(fn('asin', aS));
            uf = [[A, twoPi], [add(PI, neg(A)), twoPi]];
            general = true;
            rule = T('Формула корней: $\\sin t = a \\Leftrightarrow t = (-1)^n \\arcsin a + \\pi n$ (при $|a| \\le 1$).', 'The root formula: $\\sin t = a \\Leftrightarrow t = \\arcsin a + 2\\pi n$ or $t = \\pi - \\arcsin a + 2\\pi n$ (for $|a| \\le 1$).');
        }
    } else if (F === 'cos') {
        if (is(0)) [uf, rule] = [[[halfPi, PI]], T('Частный случай: $\\cos t = 0 \\Leftrightarrow t = \\frac{\\pi}{2} + \\pi n$.', 'A special case: $\\cos t = 0 \\Leftrightarrow t = \\frac{\\pi}{2} + \\pi n$.')];
        else if (is(1)) [uf, rule] = [[[N0, twoPi]], T('Частный случай: $\\cos t = 1 \\Leftrightarrow t = 2\\pi n$.', 'A special case: $\\cos t = 1 \\Leftrightarrow t = 2\\pi n$.')];
        else if (is(-1)) [uf, rule] = [[[PI, twoPi]], T('Частный случай: $\\cos t = -1 \\Leftrightarrow t = \\pi + 2\\pi n$.', 'A special case: $\\cos t = -1 \\Leftrightarrow t = \\pi + 2\\pi n$.')];
        else {
            A = simpOr(fn('acos', aS));
            uf = [[A, twoPi], [neg(A), twoPi]];
            general = true;
            rule = T('Формула корней: $\\cos t = a \\Leftrightarrow t = \\pm\\arccos a + 2\\pi n$ (при $|a| \\le 1$).', 'The root formula: $\\cos t = a \\Leftrightarrow t = \\pm\\arccos a + 2\\pi n$ (for $|a| \\le 1$).');
        }
    } else if (F === 'tan') {
        A = simpOr(fn('atan', aS));
        uf = [[A, PI]];
        rule = T('Формула корней: $\\operatorname{tg} t = a \\Leftrightarrow t = \\operatorname{arctg} a + \\pi n$.', 'The root formula: $\\tan t = a \\Leftrightarrow t = \\arctan a + \\pi n$.');
    } else {
        A = simpOr(fn('acot', aS));
        uf = [[A, PI]];
        rule = T('Формула корней: $\\operatorname{ctg} t = a \\Leftrightarrow t = \\operatorname{arcctg} a + \\pi n$.', 'The root formula: $\\cot t = a \\Leftrightarrow t = \\operatorname{arccot} a + \\pi n$.');
    }
    // arctg(2 − √3) = π/12 and the like: a rational multiple of π with a small denominator
    let recognized = null;
    if (A && A.type !== 'num' && !(A.type === 'mul' && A.args.some((f) => f.type === 'sym' && f.name === 'pi')) && !(A.type === 'sym' && A.name === 'pi')) {
        const r = approxOf(A) / Math.PI;
        for (let d = 1; d <= 24 && Number.isFinite(r); d++) {
            const n = Math.round(r * d);
            // …and F of that angle really is a (arctg 10¹⁰ is within 1e-10 of π/2, but tg(π/2) is not 10¹⁰)
            const Fv = approxOf(fn(F, mul(num(new Q(BigInt(n), BigInt(d))), PI)));
            if (Math.abs(r * d - n) < 1e-10 && Number.isFinite(Fv) && Math.abs(Fv - av) <= 1e-9 * Math.max(1, Math.abs(av))) {
                const B = simpOr(mul(num(new Q(BigInt(n), BigInt(d))), PI));
                recognized = { from: A, to: B };
                uf = uf.map(([b, P]) => [replaceNode(b, A, B), P]);
                A = B;
                break;
            }
        }
    }
    if (recognized) {
        const f = recognized;
        rule = T(`${rule.ru} Здесь $${tex(f.from)} = ${tex(f.to)}$.`, `${rule.en} Here $${tex(f.from, 'en')} = ${tex(f.to, 'en')}$.`);
    }
    const k = la.k;
    const s = la.s;
    const kn = num(k);
    const fams = uf.map(([b, P]) => mkFamily(div(add(b, neg(s)), kn), div(P, num(k.abs()))));
    const isX = k.isOne() && isZeroNode(simpOr(s));
    // display: the school form for u, then for x
    const shift = simpOr(div(neg(s), kn));
    const group = { size: fams.length, tex: null };
    const xTex = (l) => {
        if (general && F === 'sin' && l === 'ru') {
            let Ak = simpOr(div(A, kn));
            let sgn = '(-1)^{n}';
            if (approxOf(Ak) < 0) {
                Ak = simpOr(neg(Ak));
                sgn = '(-1)^{n+1}';
            }
            return `${v} = ${sgn}${tex(Ak, l)}${signedTex(plusTex([shift, periodN(simpOr(div(PI, num(k.abs()))))], l))}`;
        }
        if (general && F === 'cos') {
            const Ak = simpOr(div(A, num(k.abs())));
            return `${v} = \\pm ${tex(Ak, l)}${signedTex(plusTex([shift, periodN(fams[0].period)], l))}`;
        }
        return fams.map((f) => familyTex(f, v, l)).join(l === 'ru' ? ';\\quad ' : ',\\quad ');
    };
    group.tex = byLang(xTex);
    for (const f of fams) f.group = group;
    const uTex = (l) => {
        const us = tex(u, l);
        if (general && F === 'sin' && l === 'ru') return `${us} = (-1)^{n}${tex(A, l)} + \\pi n`;
        if (general && F === 'cos') return `${us} = \\pm ${tex(A, l)} + 2\\pi n`;
        return uf.map(([b, P]) => `${us} = ${plusTex([simpOr(b), periodN(simpOr(P))], l)}`).join(l === 'ru' ? ';\\quad ' : ',\\quad ');
    };
    const texLines = byLang((l) => (isX ? xTex(l) : `${uTex(l)} \\;\\Rightarrow\\; ${xTex(l)}`) + ZZ(l));
    return { families: fams, steps: [S(title, { tex: texLines, text: rule })] };
}

/** Coefficients of a polynomial in one placeholder: Map degree → constant node, or null. */
function coeffsIn(P, name, v, allowOthers = false) {
    let ct;
    try {
        ct = collectTerms(P, name);
    } catch {
        return null;
    }
    if (!ct) return null;
    for (const [d, c] of ct) {
        if (!Number.isInteger(d) || d < 0 || d > 8) return null;
        if (containsVar(c, v) || (!allowOthers && freeVars(c).some((x) => x.startsWith('__')))) return null;
    }
    return ct;
}

/** Map "i,j" → coefficient for a polynomial in two placeholders. */
function coeffs2(P, a, b, v) {
    const ca = coeffsIn(expd(P) ?? P, a, v, true);
    if (!ca) return null;
    const out = new Map();
    for (const [i, c] of ca) {
        const cb = coeffsIn(c, b, v);
        if (!cb) return null;
        for (const [j, cc] of cb) if (!isConstNode(cc)) return null;
        for (const [j, cc] of cb) out.set(`${i},${j}`, cc);
    }
    return out;
}

/** Polynomial with constant node coefficients (Map degree → node) → roots {roots, steps} or null. */
function rootsOfNodePoly(ct, name) {
    const deg = Math.max(...ct.keys());
    const qs = [];
    let allQ = true;
    for (let d = 0; d <= deg; d++) {
        const q = numValue(ct.get(d) ?? N0);
        if (!q) allQ = false;
        qs.push(q);
    }
    if (allQ) {
        const P = new Poly(qs);
        const r = solveAnyPoly(P, { v: name, domain: 'real' });
        return { roots: r.roots, steps: r.steps, poly: P };
    }
    if (deg === 1) {
        const r = simpOr(div(neg(ct.get(0) ?? N0), ct.get(1)));
        return { roots: [mkRoot(r)], steps: [] };
    }
    if (deg === 2) {
        const r = nodeQuadRoots(ct.get(2), ct.get(1) ?? N0, ct.get(0) ?? N0, { v: name, domain: 'real' });
        return { roots: r.roots, steps: r.steps };
    }
    return null;
}

function polyNodeFrom(ct, name) {
    const terms = [...ct.entries()].sort((a, b) => b[0] - a[0]).map(([d, c]) => simpOr(mul(c, d === 0 ? N1 : pow(sym(name), num(d)))));
    return simpOr(sumNode(terms));
}

/** A polynomial in t = F(u): solve for t, keep |t| ≤ 1 for sin/cos, then the basic equations. */
function trigPolyOne(P, F, u, ctx, extraText) {
    const v = ctx.v;
    const ct = coeffsIn(expd(P) ?? P, PH[F], v);
    if (!ct || !ct.size) return null;
    const deg = Math.max(...ct.keys());
    if (deg < 1) return null;
    const steps = [];
    let families = [];
    if (deg === 1) {
        const a = simpOr(div(neg(ct.get(0) ?? N0), ct.get(1)));
        const b = basicTrig(F, u, a, ctx);
        if (!b) return null;
        if (extraText) steps.push(S(extraText.title, { tex: byLang((l) => `${tex(fn(F, u), l)} = ${tex(a, l)}`), text: extraText.text }));
        steps.push(...b.steps);
        return { families: b.families, steps };
    }
    const tName = 't';
    const polyT = polyNodeFrom(ct, tName);
    const Fu = (l) => tex(fn(F, u), l);
    steps.push(S(byLang((l) => (l === 'ru' ? `Замена $t = ${Fu(l)}$` : `Substitute $t = ${Fu(l)}$`)), {
        tex: byLang((l) => `${tex(polyT, l)} = 0`),
        text: extraText ? extraText.text : (F === 'sin' || F === 'cos' ? T('Уравнение стало алгебраическим относительно $t$; помним, что $-1 \\le t \\le 1$.', 'The equation is now algebraic in $t$; remember that $-1 \\le t \\le 1$.') : T('Уравнение стало алгебраическим относительно $t$.', 'The equation is now algebraic in $t$.')),
    }));
    const rr = rootsOfNodePoly(ct, tName);
    if (!rr) return null;
    steps.push(S(byLang((l) => (l === 'ru' ? `Решаем $${tex(polyT, l)} = 0$` : `Solve $${tex(polyT, l)} = 0$`)), { tex: byLang((l) => rootsTex(rr.roots, 't', l)), sub: rr.steps }));
    for (const t of rr.roots) {
        if ((F === 'sin' || F === 'cos') && Math.abs(t.approx) > 1 + 1e-12) {
            steps.push(S(byLang((l) => `$t = ${tex(t.node, l)}$`), { text: T(`Не подходит: $|${F === 'sin' ? '\\sin' : '\\cos'} x| \\le 1$.`, `Rejected: $|${F === 'sin' ? '\\sin' : '\\cos'} x| \\le 1$.`) }));
            continue;
        }
        const b = basicTrig(F, u, t.node, ctx);
        if (!b) return null;
        families.push(...b.families);
        steps.push(...b.steps);
    }
    return { families, steps };
}

function trigCore(E, ctx) {
    return trigCore0(E, ctx) ?? trigFraction(E, ctx);
}

/**
 * A fraction with trigonometric functions in a denominator that is not a plain power (sin x/(1 − cos x) = 0):
 * the numerator is zero and the denominator is not — solve the numerator, the ОДЗ check of the families then
 * drops the points where the denominator vanishes (x = πn → x = π + 2πn).
 */
function trigFraction(E, ctx) {
    const v = ctx.v;
    if (ctx.trigFrac) return null;
    let nd;
    try {
        nd = numDen(E);
    } catch {
        return null;
    }
    if (!nd || !containsVar(nd.den, v) || !containsVar(nd.num, v)) return null;
    if (splitCoeff(nd.num).coef.isNeg()) nd = { num: simpOr(neg(nd.num)), den: nd.den };
    const r = trigCore(nd.num, { ...ctx, trigFrac: true });
    if (!r) return null;
    const steps = [S(T('Дробь равна нулю, когда числитель равен нулю, а знаменатель — нет', 'A fraction is zero when its numerator is zero and its denominator is not'), {
        tex: byLang((l) => `${tex(nd.num, l)} = 0,\\qquad ${tex(nd.den, l)} \\ne 0`),
        text: T('Решаем уравнение «числитель = 0», а корни, при которых знаменатель обращается в ноль, отбросим по ОДЗ.', 'Solve "numerator = 0"; the roots where the denominator vanishes are dropped by the domain.'),
    })];
    return { families: r.families, steps: [...steps, ...r.steps] };
}

function trigCore0(E, ctx) {
    const v = ctx.v;
    const tn = outermost(E, (n) => n.type === 'fn' && TRIG_FN.includes(n.name) && containsVar(n, v));
    if (!tn.length) return null;
    let rest = E;
    tn.forEach((t, i) => {
        rest = replaceNode(rest, t, sym(`__p${i}`));
    });
    if (containsVar(rest, v)) return null;
    const args = new Map();
    for (const t of tn) args.set(nodeKey(t.args[0]), t.args[0]);
    if (args.size > 1) return trigMultiArg(E, tn, [...args.values()], ctx);
    const u = tn[0].args[0];
    if (!linArg(u, v)) return null;
    const names0 = [...new Set(tn.map((t) => t.name))].sort();
    let P = E;
    for (const name of names0) P = replaceNode(P, fn(name, u), sym(PH[name]));
    const pre = [];
    const nameSet = new Set(names0);
    const Uf = (f) => (l) => tex(fn(f, u), l);
    // tg and ctg next to sin and cos: tg = sin/cos, ctg = cos/sin
    if ((nameSet.has('sin') || nameSet.has('cos')) && (nameSet.has('tan') || nameSet.has('cot'))) {
        P = replaceNode(P, sym(PH.tan), div(sym(PH.sin), sym(PH.cos)));
        P = replaceNode(P, sym(PH.cot), div(sym(PH.cos), sym(PH.sin)));
        nameSet.delete('tan');
        nameSet.delete('cot');
        nameSet.add('sin');
        nameSet.add('cos');
        pre.push(S(T('Выражаем тангенс и котангенс через синус и косинус', 'Write the tangent and cotangent through sine and cosine'), {
            text: T('$\\operatorname{tg} t = \\frac{\\sin t}{\\cos t}$, $\\operatorname{ctg} t = \\frac{\\cos t}{\\sin t}$.', '$\\tan t = \\frac{\\sin t}{\\cos t}$, $\\cot t = \\frac{\\cos t}{\\sin t}$.'),
        }));
    }
    // trig functions in denominators: multiply by their powers (not zero by the ОДЗ)
    for (const name of [...nameSet]) {
        let ct;
        try {
            ct = collectTerms(expd(P) ?? P, PH[name]);
        } catch {
            ct = null;
        }
        if (!ct) return null;
        const mn = Math.min(0, ...ct.keys());
        if (mn < 0) {
            const k = -mn;
            P = expd(mul(P, pow(sym(PH[name]), num(k))));
            if (!P) return null;
            pre.push(S(T(`Умножаем обе части на $${Uf(name)('ru')}${k > 1 ? `^{${k}}` : ''}$`, `Multiply both sides by $${Uf(name)('en')}${k > 1 ? `^{${k}}` : ''}$`), {
                tex: byLang((l) => `${tex(simpOr(replaceNode(replaceNode(replaceNode(replaceNode(P, sym(PH.sin), fn('sin', u)), sym(PH.cos), fn('cos', u)), sym(PH.tan), fn('tan', u)), sym(PH.cot), fn('cot', u))), l)} = 0`),
                text: T('Он стоит в знаменателе, поэтому по ОДЗ не равен нулю — равносильность не нарушается.', 'It stands in a denominator, so by the domain it is not zero and the equation stays equivalent.'),
            }));
        }
    }
    const names = [...nameSet].sort();
    const res = trigSingle(P, names, u, ctx);
    return res && { families: res.families, steps: [...pre, ...res.steps] };
}

function trigSingle(P, names, u, ctx) {
    const v = ctx.v;
    const done = (r, extra = []) => r && { families: r.families, steps: [...extra, ...r.steps] };
    if (names.length === 1) return done(trigPolyOne(P, names[0], u, ctx));
    const key = names.join(',');
    const Ut = (f) => (l) => tex(fn(f, u), l);
    if (key === 'cos,sin') {
        const bv = coeffs2(P, '__s', '__c', v);
        if (!bv) return null;
        return sinCosCore(bv, u, ctx, 0);
    }
    if (key === 'cot,tan') {
        const bv = coeffs2(P, '__t', '__k', v);
        if (!bv) return null;
        const ij = [...bv.keys()].map((k) => k.split(',').map(Number));
        const mj = Math.max(...ij.map(([, j]) => j));
        const ct = new Map();
        for (const [i, j] of ij) {
            const d = i - j + mj;
            ct.set(d, simpOr(add(ct.get(d) ?? N0, bv.get(`${i},${j}`))));
        }
        for (const [d, c] of [...ct]) if (isZeroNode(c)) ct.delete(d);
        if (!ct.size) return null;
        const polyT = polyNodeFrom(ct, PH.tan);
        const pre = S(T(`Заменяем $\\operatorname{ctg} = \\frac{1}{\\operatorname{tg}}$ и умножаем на $\\operatorname{tg}${mj > 1 ? `^${mj}` : ''}$`, `Replace $\\cot = \\frac{1}{\\tan}$ and multiply by $\\tan${mj > 1 ? `^${mj}` : ''}$`), {
            tex: byLang((l) => `${tex(simpOr(replaceNode(polyT, sym(PH.tan), fn('tan', u))), l)} = 0`),
            text: T('Раз котангенс определён, $\\operatorname{tg} \\ne 0$ — умножать можно, но корень $\\operatorname{tg} = 0$ придётся отбросить.', 'Since the cotangent is defined, $\\tan \\ne 0$: the multiplication is fine, but a root $\\tan = 0$ must be dropped.'),
        });
        const r = trigPolyOne(polyT, 'tan', u, ctx);
        if (!r) return null;
        r.families = r.families.filter((f) => Math.abs(Math.tan(f.b * linArg(u, v).k.toNumber() + approxOf(linArg(u, v).s))) > 1e-9);
        return done(r, [pre]);
    }
    return null;
}

function bvNode(bv, u) {
    const terms = [...bv.entries()].map(([k, c]) => {
        const [i, j] = k.split(',').map(Number);
        return simpOr(mul(c, pow(fn('sin', u), num(i)), pow(fn('cos', u), num(j))));
    });
    return simpOr(sumNode(terms));
}

/** A polynomial in sin u and cos u given as Map "i,j" → coefficient. */
function sinCosCore(bv, u, ctx, depth) {
    const v = ctx.v;
    if (depth > 3) return null;
    for (const [k, c] of [...bv]) if (isZeroNode(simpOr(c))) bv.delete(k);
    if (!bv.size) return null;
    const Ut = (f) => (l) => tex(fn(f, u), l);
    const done = (r, extra = []) => r && { families: r.families, steps: [...extra, ...r.steps] };
    const ij0 = [...bv.keys()].map((k) => k.split(',').map(Number));
    for (const [F, idx] of [['sin', 1], ['cos', 0]]) {
        if (!ij0.every((p) => p[idx] === 0)) continue;
        const node = simpOr(sumNode([...bv.entries()].map(([k, c]) => mul(c, pow(sym(PH[F]), num(Number(k.split(',')[1 - idx])))))));
        return trigPolyOne(node, F, u, ctx);
    }
    const a = Math.min(...ij0.map((p) => p[0]));
    const b = Math.min(...ij0.map((p) => p[1]));
    if (a > 0 || b > 0) {
        const red = new Map();
        for (const [k, c] of bv) {
            const [i, j] = k.split(',').map(Number);
            red.set(`${i - a},${j - b}`, c);
        }
        const fac = simpOr(mul(pow(fn('sin', u), num(a)), pow(fn('cos', u), num(b))));
        const redNode = bvNode(red, u);
        const steps = [S(T('Выносим общий множитель за скобки', 'Take the common factor out of the brackets'), {
            tex: byLang((l) => `${tex(fac, l)}\\left(${tex(redNode, l)}\\right) = 0`),
            text: T('Произведение равно нулю, когда один из множителей равен нулю.', 'A product is zero when one of the factors is zero.'),
        })];
        const families = [];
        if (a > 0) {
            const r = basicTrig('sin', u, N0, ctx);
            if (!r) return null;
            families.push(...r.families);
            steps.push(...r.steps);
        }
        if (b > 0) {
            const r = basicTrig('cos', u, N0, ctx);
            if (!r) return null;
            families.push(...r.families);
            steps.push(...r.steps);
        }
        if ([...red.keys()].some((k) => k !== '0,0')) {
            const r = sinCosCore(red, u, ctx, depth + 1);
            if (!r) return null;
            families.push(...r.families);
            steps.push(...r.steps);
        }
        return { families, steps };
    }
    const ij = [...bv.keys()].map((k) => k.split(',').map(Number));
    const nonConst = ij.filter(([i, j]) => i + j > 0);
    // only even powers of one function: use sin² + cos² = 1
    for (const [F, G, idx] of [['cos', 'sin', 0], ['sin', 'cos', 1]]) {
        if (!ij.every((p) => p[idx] % 2 === 0)) continue;
        const other = PH[F];
        const terms = [...bv.entries()].map(([k, c]) => {
            const [i, j] = k.split(',').map(Number);
            const g = idx === 0 ? i : j;
            const f = idx === 0 ? j : i;
            return mul(c, pow(add(N1, neg(pow(sym(other), num(2)))), num(g / 2)), pow(sym(other), num(f)));
        });
        const P2 = expd(sumNode(terms));
        if (!P2) return null;
        const r = trigPolyOne(P2, F, u, ctx);
        const pre = S(T(`Заменяем $${Ut(G)('ru')}^2$ на $1 - ${Ut(F)('ru')}^2$`, `Replace $${Ut(G)('en')}^2$ with $1 - ${Ut(F)('en')}^2$`), {
            tex: byLang((l) => `${tex(simpOr(replaceNode(P2, sym(other), fn(F, u))), l)} = 0`),
            text: T('Основное тригонометрическое тождество: $\\sin^2 t + \\cos^2 t = 1$. Теперь в уравнении одна функция.', 'The Pythagorean identity $\\sin^2 t + \\cos^2 t = 1$ leaves one function in the equation.'),
        });
        return done(r, [pre]);
    }
    const degs = new Set(nonConst.map(([i, j]) => i + j));
    const c0 = bv.get('0,0');
    if (degs.size === 1 && (!c0 || [...degs][0] === 2)) {
        const d = [...degs][0];
        const h = new Map();
        for (const [i, j] of nonConst) h.set(i, bv.get(`${i},${j}`));
        const pre = [];
        if (c0) {
            h.set(2, simpOr(add(h.get(2) ?? N0, c0)));
            h.set(0, simpOr(add(h.get(0) ?? N0, c0)));
            pre.push(S(T('Записываем число как $a(\\sin^2 + \\cos^2)$', 'Write the number as $a(\\sin^2 + \\cos^2)$'), {
                tex: byLang((l) => `${tex(simpOr(sumNode([...h.entries()].filter(([, c]) => !isZeroNode(c)).map(([i, c]) => mul(c, pow(fn('sin', u), num(i)), pow(fn('cos', u), num(d - i)))))), l)} = 0`),
                text: T('Так все слагаемые получают одинаковую степень — уравнение становится однородным.', 'Now every term has the same degree: the equation becomes homogeneous.'),
            }));
        }
        for (const [i, c] of [...h]) if (isZeroNode(simpOr(c))) h.delete(i);
        const maxI = Math.max(...h.keys());
        const m = d - maxI; // cos^m is a common factor
        let families = [];
        const steps = [...pre];
        if (m > 0) {
            steps.push(S(T(`Выносим $\\cos${m > 1 ? `^${m}` : ''}$ за скобки`, `Take $\\cos${m > 1 ? `^${m}` : ''}$ out of the brackets`), {
                text: T(`Одна из возможностей: $${Ut('cos')('ru')} = 0$.`, `One possibility: $${Ut('cos')('en')} = 0$.`),
            }));
            const b = basicTrig('cos', u, N0, ctx);
            if (!b) return null;
            families.push(...b.families);
            steps.push(...b.steps);
        }
        const dd = maxI;
        if (dd > 0) {
            const ct = new Map();
            for (const [i, c] of h) ct.set(i, c);
            const polyT = polyNodeFrom(ct, PH.tan);
            steps.push(S(T(`Однородное уравнение: делим на $\\cos${dd > 1 ? `^${dd}` : ''} ${tex(u).length > 1 ? `(${tex(u)})` : tex(u)}$`, `A homogeneous equation: divide by $\\cos${dd > 1 ? `^${dd}` : ''} ${tex(u, 'en').length > 1 ? `(${tex(u, 'en')})` : tex(u, 'en')}$`), {
                tex: byLang((l) => `${tex(simpOr(replaceNode(polyT, sym(PH.tan), fn('tan', u))), l)} = 0`),
                text: T(`Делить можно: если $${Ut('cos')('ru')} = 0$, то $${Ut('sin')('ru')} = \\pm 1$, и уравнение даёт $${tex(h.get(dd))} = 0$ — неверно.`, `This is allowed: if $${Ut('cos')('en')} = 0$ then $${Ut('sin')('en')} = \\pm 1$ and the equation gives $${tex(h.get(dd), 'en')} = 0$, which is false.`),
            }));
            const r = trigPolyOne(polyT, 'tan', u, ctx);
            if (!r) return null;
            families.push(...r.families);
            steps.push(...r.steps);
        }
        return { families, steps };
    }
    // a sin u + b cos u = c: the auxiliary angle
    if (ij.every(([i, j]) => i + j <= 1) && bv.has('1,0') && bv.has('0,1')) {
        const a = bv.get('1,0');
        const b = bv.get('0,1');
        const cRight = simpOr(neg(c0 ?? N0));
        const R = simpOr(pow(add(pow(a, num(2)), pow(b, num(2))), num(Q.HALF)));
        const cosPhi = simpOr(div(a, R));
        let phi = simpOr(fn('acos', cosPhi));
        if (approxOf(b) < 0) phi = simpOr(neg(phi));
        const u2 = simpOr(add(u, phi));
        const rhs2 = simpOr(div(cRight, R));
        const pre = S(T('Метод вспомогательного угла', 'The auxiliary angle method'), {
            tex: byLang((l) => `${tex(simpOr(add(mul(a, fn('sin', u)), mul(b, fn('cos', u)))), l)} = ${tex(R, l)}\\sin\\left(${tex(u2, l)}\\right)`),
            text: T(`$a\\sin t + b\\cos t = R\\sin(t + \\varphi)$, где $R = \\sqrt{a^2 + b^2} = ${tex(R)}$, $\\cos\\varphi = \\frac{a}{R}$, $\\sin\\varphi = \\frac{b}{R}$; здесь $\\varphi = ${tex(phi)}$.`,
                `$a\\sin t + b\\cos t = R\\sin(t + \\varphi)$ with $R = \\sqrt{a^2 + b^2} = ${tex(R, 'en')}$, $\\cos\\varphi = \\frac{a}{R}$, $\\sin\\varphi = \\frac{b}{R}$; here $\\varphi = ${tex(phi, 'en')}$.`),
        });
        const r = basicTrig('sin', u2, rhs2, ctx);
        return done(r, [pre]);
    }
    return null;
}

/** c·F(u) with a rational c → {c, F, u}. */
function trigTerm(t, v) {
    const fs = t.type === 'mul' ? t.args : [t];
    const withV = fs.filter((f) => containsVar(f, v));
    if (withV.length !== 1 || withV[0].type !== 'fn' || !TRIG_FN.includes(withV[0].name)) return null;
    const c = numValue(simpOr(fs.length === 1 ? N1 : mul(fs.filter((f) => f !== withV[0]))));
    return c && { c, F: withV[0].name, u: withV[0].args[0] };
}

/** sin a ± sin b, cos a ± cos b = 0 → a product of two factors. */
function sumToProduct(E, ctx) {
    const v = ctx.v;
    if (E.type !== 'add' || E.args.length !== 2) return null;
    const [A, B] = E.args.map((t) => trigTerm(t, v));
    if (!A || !B || A.F !== B.F || (A.F !== 'sin' && A.F !== 'cos') || !A.c.abs().eq(B.c.abs())) return null;
    const plus = A.c.eq(B.c);
    const half = (x) => {
        let s = simpOr(div(x, num(2)));
        const la = linArg(s, v);
        if (la && la.k.isNeg()) s = simpOr(neg(s));
        return s;
    };
    const sum = half(add(A.u, B.u));
    const dif = half(add(A.u, neg(B.u)));
    if (!linArg(sum, v) || !linArg(dif, v)) return null;
    const [G1, G2] = A.F === 'sin' ? (plus ? ['sin', 'cos'] : ['cos', 'sin']) : plus ? ['cos', 'cos'] : ['sin', 'sin'];
    const name = A.F === 'sin' ? (plus ? T('Сумма синусов', 'A sum of sines') : T('Разность синусов', 'A difference of sines')) : plus ? T('Сумма косинусов', 'A sum of cosines') : T('Разность косинусов', 'A difference of cosines');
    const lhsT = (l) => `${tex(fn(A.F, A.u), l)} ${plus ? '+' : '-'} ${tex(fn(B.F, B.u), l)}`;
    const prodT = (l) => `${A.F === 'cos' && !plus ? '-' : ''}2${tex(fn(G1, sum), l)}${tex(fn(G2, dif), l)}`;
    const steps = [S(T(`${name.ru}: переходим к произведению`, `${name.en}: turn it into a product`), {
        tex: byLang((l) => `${lhsT(l)} = ${prodT(l)} = 0`),
        text: T('Произведение равно нулю, когда один из множителей равен нулю.', 'A product is zero when one of the factors is zero.'),
    })];
    const families = [];
    for (const [G, w] of [[G1, sum], [G2, dif]]) {
        const b = basicTrig(G, w, N0, ctx);
        if (!b) return null;
        families.push(...b.families);
        steps.push(...b.steps);
    }
    return { families, steps };
}

/**
 * F(A) = ±G(B) with different arguments: tg 3x = tg x ⇔ 3x = x + πn; sin A = cos B ⇔ A = π/2 − B + 2πn or
 * A = π/2 + B + 2πn; tg A = ctg B ⇔ A = π/2 − B + πn. (sin/sin and cos/cos go through sumToProduct.)
 * Points where a side is undefined are dropped later by the ОДЗ check of the families.
 */
function equalTrig(E, ctx) {
    const v = ctx.v;
    if (E.type !== 'add' || E.args.length !== 2) return null;
    let [P, R] = E.args.map((t) => trigTerm(t, v));
    if (!P || !R) return null;
    const sgn = P.c.eq(R.c.neg()) ? 1 : P.c.eq(R.c) ? -1 : 0;
    if (!sgn) return null;
    const key = `${P.F},${R.F}`;
    const half = mul(num(Q.HALF), PI);
    const twoPi = mul(num(2), PI);
    // X = c + σ·Y + period·n, X and Y being the arguments A and B (or B and A)
    const A = P.u;
    const B = R.u;
    let rels;
    let rule;
    const pm = sgn > 0 ? '' : '-';
    if (key === 'tan,tan' || key === 'cot,cot') {
        rels = [{ X: A, Y: B, c: N0, s: sgn, P: PI }];
        const f = key === 'tan,tan' ? 'tg' : 'ctg';
        rule = byLang((l) => {
            const F = l === 'ru' ? `\\operatorname{${f}}` : key === 'tan,tan' ? '\\tan' : '\\cot';
            return l === 'ru'
                ? `$${F} a = ${F} b \\Leftrightarrow a = b + \\pi n$ (там, где обе части определены — это проверим по ОДЗ).${sgn < 0 ? ` Здесь $-${F} b = ${F}(-b)$.` : ''}`
                : `$${F} a = ${F} b \\Leftrightarrow a = b + \\pi n$ (where both sides are defined, which the domain check takes care of).${sgn < 0 ? ` Here $-${F} b = ${F}(-b)$.` : ''}`;
        });
    } else if (key === 'tan,cot' || key === 'cot,tan') {
        const [X, Y] = key === 'tan,cot' ? [A, B] : [B, A];
        rels = [{ X, Y, c: half, s: -sgn, P: PI }];
        rule = T('$\\operatorname{ctg} b = \\operatorname{tg}\\left(\\frac{\\pi}{2} - b\\right)$, а $\\operatorname{tg} a = \\operatorname{tg} c \\Leftrightarrow a = c + \\pi n$.', '$\\cot b = \\tan\\left(\\frac{\\pi}{2} - b\\right)$, and $\\tan a = \\tan c \\Leftrightarrow a = c + \\pi n$.');
    } else if (key === 'sin,cos' || key === 'cos,sin') {
        const [X, Y] = key === 'sin,cos' ? [A, B] : [B, A];
        rels = sgn > 0
            ? [{ X, Y, c: half, s: -1, P: twoPi }, { X, Y, c: half, s: 1, P: twoPi }]
            : [{ X, Y, c: neg(half), s: 1, P: twoPi }, { X, Y, c: mul(num(new Q(3n, 2n)), PI), s: -1, P: twoPi }];
        rule = sgn > 0
            ? T('$\\cos b = \\sin\\left(\\frac{\\pi}{2} - b\\right)$, а $\\sin a = \\sin c \\Leftrightarrow a = c + 2\\pi n$ или $a = \\pi - c + 2\\pi n$.', '$\\cos b = \\sin\\left(\\frac{\\pi}{2} - b\\right)$, and $\\sin a = \\sin c \\Leftrightarrow a = c + 2\\pi n$ or $a = \\pi - c + 2\\pi n$.')
            : T('$-\\cos b = \\sin\\left(b - \\frac{\\pi}{2}\\right)$, а $\\sin a = \\sin c \\Leftrightarrow a = c + 2\\pi n$ или $a = \\pi - c + 2\\pi n$.', '$-\\cos b = \\sin\\left(b - \\frac{\\pi}{2}\\right)$, and $\\sin a = \\sin c \\Leftrightarrow a = c + 2\\pi n$ or $a = \\pi - c + 2\\pi n$.');
    } else return null;
    const families = [];
    const lines = [];
    for (const r of rels) {
        const lx = linArg(r.X, v);
        const ly = linArg(r.Y, v);
        if (!lx || !ly) return null;
        const K = lx.k.sub(ly.k.mul(r.s));
        if (K.isZero()) return null;
        // (kX − σkY)·x = c − sX + σ·sY + P·n
        const base = simpOr(div(add(r.c, neg(lx.s), mul(num(r.s), ly.s)), num(K)));
        families.push(mkFamily(base, div(r.P, num(K.abs()))));
        const t = simpOr(add(r.c, mul(num(r.s), r.Y)));
        lines.push((l) => `${tex(r.X, l)} = ${plusTex([...(t.type === 'add' ? t.args : [t]), periodN(simpOr(r.P))], l)}`);
    }
    const eqT = (l) => `${tex(fn(P.F, A), l)} = ${pm}${tex(fn(R.F, B), l)}`;
    const steps = [
        S(byLang((l) => (l === 'ru' ? `Приравниваем аргументы: $${eqT(l)}$` : `Compare the arguments: $${eqT(l)}$`)), {
            tex: byLang((l) => lines.map((f) => f(l)).join(`${orTex(l)} `) + ZZ(l)),
            text: rule,
        }),
        S(T(`Выражаем $${v}$`, `Solve for $${v}$`), { tex: byLang((l) => families.map((f) => familyTex(f, v, l)).join(l === 'ru' ? ';\\quad ' : ',\\quad ') + ZZ(l)) }),
    ];
    return { families, steps };
}

function trigMultiArg(E, tn, args, ctx) {
    const sp = sumToProduct(E, ctx);
    if (sp) return sp;
    // the textbook double-angle route first (sin 2x = cos x), then comparing the arguments (sin 3x = cos x)
    return doubleAngle(E, tn, args, ctx) ?? equalTrig(E, ctx);
}

function doubleAngle(E, tn, args, ctx) {
    const v = ctx.v;
    if (ctx.trigDepth) return null;
    const las = args.map((u) => ({ u, la: linArg(u, v) }));
    if (las.some((x) => !x.la)) return null;
    las.sort((a, b) => a.la.k.abs().cmp(b.la.k.abs()));
    const u0 = las[0];
    for (const x of las.slice(1)) {
        if (!x.la.k.eq(u0.la.k.mul(2)) || exactZero(add(x.la.s, mul(num(-2), u0.la.s))) !== true) return null;
    }
    const k0 = nodeKey(u0.u);
    const at0 = tn.filter((t) => nodeKey(t.args[0]) === k0).map((t) => t.name);
    const onlySin = at0.length > 0 && at0.every((n) => n === 'sin');
    const onlyCos = at0.length > 0 && at0.every((n) => n === 'cos');
    const u = u0.u;
    const S_ = fn('sin', u);
    const C_ = fn('cos', u);
    const reps = [];
    let E2 = E;
    for (const t of tn) {
        if (nodeKey(t.args[0]) === k0) continue;
        let r;
        if (t.name === 'sin') r = mul(num(2), S_, C_);
        else if (t.name === 'cos') r = onlyCos ? add(mul(num(2), pow(C_, num(2))), num(-1)) : onlySin ? add(N1, mul(num(-2), pow(S_, num(2)))) : add(pow(C_, num(2)), neg(pow(S_, num(2))));
        else return null;
        reps.push([t, r]);
        E2 = replaceNode(E2, t, r);
    }
    const E3 = expd(E2);
    if (!E3) return null;
    const pre = S(T('Формулы двойного угла', 'Double-angle formulas'), {
        tex: byLang((l) => reps.map(([t, r]) => `${tex(t, l)} = ${tex(r, l)}`).join(';\\quad ') + `\\;\\Rightarrow\\; ${tex(E3, l)} = 0`),
        text: T('Переходим к одному аргументу.', 'Now there is a single argument.'),
    });
    const r = trigCore(E3, { ...ctx, trigDepth: 1 });
    return r && { families: r.families, steps: [pre, ...r.steps] };
}

// ---------------------------------------------------------------- numeric fallback

const rangeTex = (a, b, lang) => `[${a};${lang === 'ru' ? '\\,' : '\\ '}${b}]`.replace(';\\ ', ',\\ ');

function solveNumeric(E, ctx) {
    const v = ctx.v;
    let f;
    try {
        f = compile(E, [v]);
    } catch {
        return { kind: 'unsupported', roots: [], steps: [], reason: T('Не умею решать такое уравнение.', 'I cannot solve this kind of equation.') };
    }
    const trig = nodeSome(E, (n) => n.type === 'fn' && TRIG_FN.includes(n.name) && containsVar(n, v));
    let range = trig ? [-2 * Math.PI, 2 * Math.PI] : [-10, 10];
    let rangeT = trig ? byLang((l) => rangeTex('-2\\pi', '2\\pi', l)) : byLang((l) => rangeTex('-10', '10', l));
    let rs = [];
    try {
        rs = numFindRoots(f, range[0], range[1], { samples: 4000 });
    } catch {
        rs = [];
    }
    if (!rs.length && !trig) {
        try {
            rs = numFindRoots(f, -100, 100, { samples: 20000 });
            range = [-100, 100];
            rangeT = byLang((l) => rangeTex('-100', '100', l));
        } catch {
            rs = [];
        }
    }
    let run = 0;
    let maxRun = 0;
    for (let k = 0; k <= 800; k++) {
        const y = f(range[0] + ((range[1] - range[0]) * k) / 800);
        run = Number.isFinite(y) && Math.abs(y) < 1e-12 ? run + 1 : 0;
        maxRun = Math.max(maxRun, run);
    }
    if (maxRun >= 3) {
        return UNSUP(T('Похоже, равенство выполняется на целых промежутках — точным методом такое уравнение здесь не решается.', 'The equality seems to hold on whole intervals; this equation is not solved exactly here.'));
    }
    const roots = rs.filter((r) => Number.isFinite(r.x)).map((r) => ({ node: approxNode(r.x), approx: r.x, mult: r.multiplicity ?? 1, approxOnly: true }));
    const steps = [S(T('Точного метода для такого уравнения нет — ищем корни численно', 'No exact method applies here, so we look for the roots numerically'), {
        text: T(`Рассматриваем $f(${v})$ = левая часть − правая часть на отрезке $${pick(rangeT, 'ru')}$: ищем, где $f$ меняет знак или касается нуля, и уточняем корни. Ответ приближённый${trig ? '; уравнение периодическое, поэтому корни за пределами отрезка тоже могут быть' : ''}.`,
            `We take $f(${v})$ = left side − right side on $${pick(rangeT, 'en')}$, look for sign changes and touching points, and refine the roots. The answer is approximate${trig ? '; the equation is periodic, so there may be roots outside the interval too' : ''}.`),
        tex: roots.length ? byLang((l) => rootsTex(roots, v, l)) : undefined,
    })];
    if (!roots.length) {
        return {
            kind: 'unsupported',
            roots: [],
            steps,
            numeric: true,
            range,
            rangeTex: rangeT,
            reason: T(`Точного метода нет, а на отрезке $${pick(rangeT, 'ru')}$ корней не нашлось.`, `There is no exact method, and no roots were found on $${pick(rangeT, 'en')}$.`),
        };
    }
    return { kind: 'roots', roots, steps, numeric: true, range, rangeTex: rangeT, type: 'numeric' };
}

// ---------------------------------------------------------------- dispatcher

const UNSUP = (reason, steps = []) => ({ kind: 'unsupported', roots: [], steps, reason });

function solveCore(lhs, rhs, ctx) {
    const v = ctx.v;
    if (ctx.depth > 8) return UNSUP(T('Слишком много вложенных преобразований.', 'Too many nested transformations.'));
    let E;
    try {
        E = simplify(add(lhs, neg(rhs)));
    } catch (e) {
        return UNSUP(e instanceof MathError ? e.msg : T('Не удалось упростить уравнение.', 'Could not simplify the equation.'));
    }
    if (!containsVar(E, v)) {
        const A = containsVar(lhs, v) || containsVar(rhs, v) ? Poly.fromNode(lhs, v) : null;
        const B = A && Poly.fromNode(rhs, v);
        if (A && B && Math.max(A.degree, B.degree) >= 1) return solveLinearSchool(lhs, rhs, A, B, ctx);
        const z = exactZero(E) ?? Math.abs(approxOf(E)) < 1e-12;
        if (z) {
            return {
                kind: 'all',
                roots: [],
                type: 'identity',
                steps: [S(T('Переменная сокращается, получается верное равенство', 'The variable cancels and a true equality remains'), {
                    tex: byLang((l) => `${tex(E, l)} = 0`),
                    text: T('Равенство верно при любом допустимом значении переменной.', 'The equality holds for every admissible value.'),
                })],
            };
        }
        return {
            kind: 'none',
            roots: [],
            type: 'identity',
            steps: [S(T('Переменная сокращается, получается неверное равенство', 'The variable cancels and a false equality remains'), {
                tex: byLang((l) => `${tex(E, l)} = 0`),
                text: T('Корней нет.', 'There are no roots.'),
            })],
        };
    }
    try {
        const ps = productSplit(lhs, rhs, ctx);
        if (ps) return ps;
        const P = Poly.fromNode(rel('=', lhs, rhs), v);
        if (P && P.degree >= 1) {
            if (P.degree === 1) {
                const A = Poly.fromNode(lhs, v);
                const B = Poly.fromNode(rhs, v);
                if (A && B) return solveLinearSchool(lhs, rhs, A, B, ctx);
            }
            return solvePolyEquation(lhs, rhs, P, ctx);
        }
        const tries = [
            () => solveRational(lhs, rhs, E, ctx),
            () => (nodeSome(E, (n) => n.type === 'fn' && n.name === 'abs') ? solveAbs(lhs, rhs, E, ctx) : null),
            () => {
                const r = trigCore(E, ctx);
                if (!r) return null;
                const fams = mergeFamilies(r.families);
                return { kind: fams.length ? 'roots' : 'none', roots: familiesToRoots(fams), families: fams, steps: r.steps, type: 'trig', periodic: true };
            },
            () => (hasRadical(E, v) ? solveRadical(lhs, rhs, E, ctx) : null),
            () => solveCommonExp(lhs, rhs, E, ctx),
            () => solveExponential(lhs, rhs, E, ctx),
            () => solveLogarithmic(lhs, rhs, E, ctx),
            () => solveTakeLog(lhs, rhs, E, ctx),
            () => solveNodePoly(E, ctx),
            () => solveFractionZero(E, ctx),
        ];
        for (const t of tries) {
            const r = t();
            if (r) return r;
        }
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
    }
    return solveNumeric(E, ctx);
}

/** A fraction with a non-polynomial denominator equals zero: (x² − 1)/√x = 0, 1/ln x − 1 = 0 → the numerator is zero. */
function solveFractionZero(E, ctx) {
    const v = ctx.v;
    let nd;
    try {
        nd = numDen(E);
    } catch {
        return null;
    }
    if (!nd || !containsVar(nd.den, v) || !containsVar(nd.num, v)) return null;
    const r = solveCore(nd.num, N0, { ...ctx, depth: ctx.depth + 1 });
    if (!r || (r.kind !== 'roots' && r.kind !== 'none') || r.families?.length || r.roots?.some((x) => x.approxOnly)) return null;
    const dropped = [];
    const roots = (r.roots ?? []).filter((x) => {
        const d = approxOf(nd.den, { [v]: x.approx ?? approxOf(x.node) });
        const ok = !(Math.abs(d) <= 1e-12); // NaN (outside the domain) is left to the domain check
        if (!ok) dropped.push(x);
        return ok;
    });
    const steps = [S(T('Дробь равна нулю, когда числитель равен нулю, а знаменатель — нет', 'A fraction is zero when its numerator is zero and its denominator is not'), {
        tex: byLang((l) => `${tex(nd.num, l)} = 0,\\qquad ${tex(nd.den, l)} \\ne 0`),
    }), ...r.steps];
    if (dropped.length) steps.push(S(T('Отбрасываем корни, где знаменатель равен нулю', 'Drop the roots where the denominator is zero'), { tex: byLang((l) => dropped.map((x) => `${v} = ${tex(x.node, l)}`).join(',\\ ')) }));
    return { kind: roots.length ? 'roots' : 'none', roots, steps, type: r.type ?? 'fraction' };
}

// ---------------------------------------------------------------- ОДЗ step

const OP_OF = { ne0: '!=', ge0: '>=', gt0: '>' };

function odzInfo(conds, v) {
    let set = IntervalSet.all();
    let partial = false;
    const excl = [];
    for (const c of conds) {
        if (c.kind === 'cos' || c.kind === 'sin') {
            const b = basicTrig(c.kind, c.expr, N0, { v });
            if (b) excl.push(...b.families);
            partial = true;
            continue;
        }
        const s = signSet(c.expr, OP_OF[c.kind], v);
        if (!s) {
            partial = true;
            continue;
        }
        set = set.intersect(s);
    }
    const whys = [...new Set(conds.flatMap((c) => [...c.whys]))];
    const lines = (l) => conds.map((c) => condTex(c, l));
    const texOf = (l) => {
        const ls = lines(l);
        let t = ls.length > 1 ? `\\begin{cases} ${ls.join(' \\\\ ')} \\end{cases}` : ls[0];
        const tail = [];
        if (!set.isAll() || !partial) tail.push(`${v} \\in ${intervalTex(set, l)}`);
        for (const f of mergeFamilies(excl)) tail.push(`${v} \\ne ${plusTex([f.base, periodN(f.period)], l)}`);
        if (tail.length) t += ` \\;\\Rightarrow\\; ${tail.join(',\\ ')}${excl.length ? ZZ(l) : ''}`;
        return t;
    };
    const tx = byLang(texOf);
    const text = T(`Условия: ${whys.map((w) => WHY[w].ru).join('; ')}.`, `Conditions: ${whys.map((w) => WHY[w].en).join('; ')}.`);
    return {
        conds,
        set: partial && set.isAll() ? null : set,
        partial,
        exclusions: excl,
        tex: tx,
        text,
        step: S(T('Область допустимых значений (ОДЗ)', 'The domain (admissible values)'), { tex: tx, text }),
    };
}

// ---------------------------------------------------------------- trig families against the domain

function famPointOk(node, v, conds, x) {
    const root = { node: null, approx: x, approxOnly: true };
    if (!conds.every((c) => condHolds(c, v, root))) return false;
    const l = approxOf(node.lhs, { [v]: x });
    const r = approxOf(node.rhs, { [v]: x });
    return Number.isFinite(l) && Number.isFinite(r) && Math.abs(l - r) <= 1e-7 * Math.max(1, Math.abs(l), Math.abs(r)) + roundingSpread(node, v, x);
}

/**
 * How much the two sides move when x moves by a few units in the last place: the part of |lhs − rhs| that is
 * just rounding of x (tg x near a pole: tg(arctg 10¹⁰) comes out as 9 999 993 049).
 */
function roundingSpread(node, v, x) {
    if (typeof x !== 'number' || !Number.isFinite(x)) return 0;
    const h = 4 * Number.EPSILON * Math.max(1, Math.abs(x));
    let s = 0;
    for (const side of [node.lhs, node.rhs]) {
        if (!containsVar(side, v)) continue;
        const a = approxOf(side, { [v]: x - h });
        const b = approxOf(side, { [v]: x + h });
        if (Number.isFinite(a) && Number.isFinite(b)) s += Math.abs(b - a);
    }
    return 16 * s;
}

function filterFamilies(fams, node, v, conds) {
    const kept = [];
    const dropped = [];
    const checks = [];
    const okAll = (b, p) => {
        const res = [];
        for (let n = -3; n <= 3; n++) res.push(famPointOk(node, v, conds, b + p * n));
        return res;
    };
    for (const f of fams) {
        const res = okAll(f.b, f.p);
        for (let n = -2; n <= 2; n++) checks.push({ family: f, n, x: f.b + f.p * n, ok: res[n + 3] });
        if (res.every(Boolean)) {
            kept.push(f);
            continue;
        }
        if (!res.some(Boolean)) {
            dropped.push(f);
            continue;
        }
        let split = null;
        for (let m = 2; m <= 12 && !split; m++) {
            const subs = [];
            let clean = true;
            for (let j = 0; j < m; j++) {
                const r = okAll(f.b + f.p * j, f.p * m);
                if (r.every(Boolean)) subs.push(mkFamily(add(f.base, mul(num(j), f.period)), mul(num(m), f.period)));
                else if (r.some(Boolean)) {
                    clean = false;
                    break;
                }
            }
            if (clean) split = subs;
        }
        if (split) {
            kept.push(...split);
            dropped.push(f);
        } else kept.push(f);
    }
    return { kept, dropped, checks };
}

// ---------------------------------------------------------------- answers

function approxText(z, lang) {
    const f = (x) => {
        const t = String(Number(x.toFixed(4)));
        return lang === 'ru' ? t.replace('.', ',') : t;
    };
    if (typeof z === 'number') return f(z);
    if (Math.abs(z.im) < 1e-12) return f(z.re);
    return `${f(z.re)} ${z.im < 0 ? '-' : '+'} ${f(Math.abs(z.im))}i`;
}

function answerOf(res, v) {
    const none = T('\\text{корней нет}', '\\text{no roots}');
    switch (res.kind) {
        case 'none':
            return { tex: none, text: T('Корней нет.', 'No roots.') };
        case 'all':
        case 'set': {
            const set = res.set;
            if (!set || set.isAll()) {
                return res.kind === 'all' && res.odzPartial
                    ? { tex: T(`${v} \\text{ — любое из ОДЗ}`, `\\text{any } ${v} \\text{ in the domain}`), text: T('Любое число из ОДЗ.', 'Any number in the domain.') }
                    : { tex: `${v} \\in \\mathbb{R}`, text: T('Любое число.', 'Any number.') };
            }
            return { tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`), text: byLang((l) => intervalText(set, l)) };
        }
        case 'roots':
            if (res.families) {
                return {
                    tex: byLang((l) => familiesTex(res.families, v, l)),
                    text: byLang((l) => `${res.families.map((f) => `${v} = ${toText(simpOr(add(f.base, mul(f.period, N_SYM))), { lang: l })}`).join('; ')}, n ∈ Z`),
                };
            }
            return { tex: byLang((l) => rootsTex(res.roots, v, l)), text: byLang((l) => res.roots.map((r) => (r.approxOnly ? `≈ ${approxText(r.approx, l)}` : toText(r.node, { lang: l }))).join(l === 'ru' ? '; ' : ', ')) };
        default:
            return { tex: '', text: res.reason ?? T('Не удалось решить.', 'Could not solve.') };
    }
}

function toIntervalOpt(iv, lang = 'ru') {
    if (!iv) return null;
    let set;
    if (iv instanceof IntervalSet) set = iv;
    else if (Array.isArray(iv)) set = IntervalSet.interval(iv[0], iv[1], true, true);
    else if (typeof iv === 'string') set = parseIntervalSet(iv, lang);
    else return null;
    if (set.parts.length !== 1 || set.parts[0].lo === null || set.parts[0].hi === null) return null;
    return set;
}

/** Roots of the families that lie in a bounded interval (exact nodes, ascending). */
function rootsOnInterval(fams, set) {
    const p = set.parts[0];
    const lo = p.lo.x;
    const hi = p.hi.x;
    const out = [];
    for (const f of fams) {
        if (!(f.p > 0)) continue;
        const n0 = Math.ceil((lo - f.b) / f.p - 1e-9);
        const n1 = Math.floor((hi - f.b) / f.p + 1e-9);
        if (n1 - n0 > 400) return null;
        for (let n = n0; n <= n1; n++) {
            const node = simpOr(add(f.base, mul(num(n), f.period)));
            const x = approxOf(node);
            if (set.contains(node)) out.push({ node, approx: x, mult: 1 });
        }
    }
    return mergeRoots(out);
}

// ---------------------------------------------------------------- solveEquation

function relOf(input, v) {
    let node = typeof input === 'string' ? parse(input, { vars: v && v.length > 1 ? [v] : [] }) : input;
    if (!node || typeof node.type !== 'string') throw new TypeError('solveEquation: expected a string or a node');
    if (node.type !== 'rel' && node.type !== 'chain' && node.type !== 'list') node = rel('=', node, N0);
    return node;
}

function pickVar(node, v) {
    const vars = freeVars(node);
    if (vars.includes(v) || !vars.length) return v;
    if (vars.length === 1) return vars[0];
    return v;
}

/**
 * Solve an equation in one variable with steps.
 * input: text or a rel node ('='); an expression means "= 0". opts: {steps: true, domain: 'real'|'complex',
 * interval: "[0; 2pi]" | [a, b] | IntervalSet — list the roots of a trig equation there, lang: 'ru' (for reading
 * the interval)}.
 * → {kind: 'roots'|'none'|'all'|'set'|'unsupported', roots: [{node, approx, mult, approxOnly?, family?}],
 *    steps, check: [{root, ok, reason, tex, text}], odz?: {tex, text, set}, answer: {tex, text}, type,
 *    families?, inInterval?, complexRoots?, set?, numeric?, range?, reason?}
 */
export function solveEquation(input, v = 'x', opts = {}) {
    let node = relOf(input, v);
    const withSteps = opts.steps !== false;
    if (node.type === 'list') return finish({ ...UNSUP(T('Это система уравнений — для неё есть отдельный решатель.', 'This is a system of equations: it has its own solver.')) }, v, withSteps);
    if (node.type === 'chain' || node.op !== '=') return finish({ ...UNSUP(T('Это неравенство, а не уравнение.', 'This is an inequality, not an equation.')) }, v, withSteps);
    v = pickVar(node, v);
    const others = freeVars(node).filter((x) => x !== v);
    if (others.length) {
        return finish(UNSUP(T(`Кроме $${v}$ в уравнении есть другие буквы (${others.join(', ')}) — уравнения с параметрами решатель пока не решает.`, `Besides $${v}$ the equation has other letters (${others.join(', ')}); equations with parameters are not supported yet.`)), v, withSteps);
    }
    if (opts.onlyTrig && !nodeSome(node, (n) => n.type === 'fn' && TRIG_FN.includes(n.name))) {
        return finish(UNSUP(T('В уравнении нет тригонометрических функций.', 'There are no trigonometric functions in the equation.')), v, withSteps);
    }
    const ctx = { v, domain: opts.domain === 'complex' ? 'complex' : 'real', depth: 0, rejected: [] };
    const steps = [];
    const conds = collectConds(node, v);
    let odz = null;
    if (conds.length) {
        odz = odzInfo(conds, v);
        steps.push(odz.step);
        if (odz.set && odz.set.isEmpty()) {
            steps.push(S(T('ОДЗ пустая — уравнение не имеет смысла ни при каком значении', 'The domain is empty: the equation makes no sense for any value')));
            return finish({ kind: 'none', roots: [], steps, odz, type: 'domain' }, v, withSteps);
        }
    }
    // simplify applies the reduction formulas (sin(x + π/2) → cos x) silently: say so before solving
    const red = reductionStep(node);
    if (red) steps.push(red);
    let core;
    try {
        core = solveCore(node.lhs, node.rhs, ctx);
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        core = UNSUP(e.msg);
    }
    steps.push(...core.steps);
    const res = { ...core, steps, odz, check: [] };
    if (core.kind === 'roots' && core.periodic) {
        const f = filterFamilies(core.families, node, v, conds);
        res.check = f.checks.map((c) => ({ root: approxNode(c.x), approx: c.x, n: c.n, ok: c.ok }));
        if (f.dropped.length) {
            steps.push(S(T('Отбрасываем серии, не входящие в ОДЗ', 'Drop the series outside the domain'), {
                tex: byLang((l) => f.dropped.map((x) => familyTex(x, v, l)).join(';\\quad ')),
                text: T('В этих точках одна из частей уравнения не определена.', 'At these points a side of the equation is not defined.'),
            }));
        }
        const fams = mergeFamilies(f.kept);
        res.families = fams;
        res.roots = familiesToRoots(fams);
        if (!fams.length) res.kind = 'none';
        else {
            steps.push(S(T('Проверка', 'Check'), {
                text: f.checks.every((c) => c.ok || f.dropped.includes(c.family))
                    ? T('Подставили в уравнение несколько значений из каждой серии ($n = -2, \\ldots, 2$) — равенство выполняется.', 'We substituted several values from each series ($n = -2, \\ldots, 2$): the equality holds.')
                    : T('Некоторые значения не подошли и были исключены.', 'Some values did not fit and were excluded.'),
            }));
        }
        const iv = toIntervalOpt(opts.interval, opts.lang);
        if (iv && fams.length) {
            const sel = rootsOnInterval(fams, iv);
            if (sel) {
                res.inInterval = sel;
                steps.push(S(byLang((l) => (l === 'ru' ? `Отбираем корни на промежутке $${intervalTex(iv, l)}$` : `Pick the roots in $${intervalTex(iv, l)}$`)), {
                    tex: byLang((l) => (sel.length ? sel.map((r) => tex(r.node, l)).join(l === 'ru' ? ';\\ ' : ',\\ ') : '\\varnothing')),
                    text: T('Перебираем целые $n$, при которых значение попадает в промежуток.', 'We go through the integers $n$ that put the value into the interval.'),
                }));
            }
        }
    } else if (core.kind === 'roots') {
        const kept = [];
        const bad = [];
        const sub = [];
        for (const r of core.roots) {
            const complex = typeof r.approx !== 'number' || (!r.approxOnly && !!r.node && hasI(r.node)) || (ctx.domain === 'complex' && hasI(node));
            const ch = checkRel(node, v, r, { conds: complex ? [] : conds, complex });
            res.check.push({ root: r.node, approx: r.approx, ok: ch.ok, reason: ch.reason, tex: ch.tex, text: ch.text });
            sub.push(...ch.steps);
            if (ch.ok) kept.push(r);
            else bad.push({ r, ch });
        }
        const needCheck = !['linear', 'quadratic', 'polynomial'].includes(core.type) || bad.length || conds.length;
        if (sub.length) {
            steps.push(S(T('Проверка подстановкой', 'Check by substitution'), {
                sub,
                text: bad.length
                    ? T(`Посторонние корни: $${bad.map(({ r }) => tex(r.node)).join(';\\ ')}$ — ${bad.some((b) => b.ch.reason === 'odz' || b.ch.reason === 'undefined') ? 'не входят в ОДЗ или не удовлетворяют уравнению' : 'не удовлетворяют исходному уравнению'}.`,
                        `Extraneous roots: $${bad.map(({ r }) => tex(r.node, 'en')).join(',\\ ')}$: ${bad.some((b) => b.ch.reason === 'odz' || b.ch.reason === 'undefined') ? 'outside the domain or not satisfying the equation' : 'they do not satisfy the original equation'}.`)
                    : needCheck ? T('Все найденные корни подходят.', 'All the roots found fit.') : T('Корни подходят.', 'The roots fit.'),
            }));
        }
        res.roots = kept;
        res.extraneous = [...ctx.rejected, ...bad.map(({ r, ch }) => ({ node: r.node, approx: r.approx, reason: ch.reason }))]
            .filter((x, k, all) => typeof x.approx !== 'number' || all.findIndex((y) => typeof y.approx === 'number' && close(y.approx, x.approx, 1e-9)) === k)
            .filter((x) => !kept.some((r) => sameRoot(r, x)))
            .sort((a, b) => (typeof a.approx === 'number' && typeof b.approx === 'number' ? a.approx - b.approx : 0));
        if (!kept.length) res.kind = 'none';
    } else if (core.kind === 'all' || core.kind === 'set') {
        let set = core.set ?? IntervalSet.all();
        if (odz?.set) set = set.intersect(odz.set);
        res.set = set;
        res.odzPartial = !!odz?.partial;
        if (set.isEmpty()) res.kind = 'none';
    }
    return finish(res, v, withSteps);
}

function finish(res, v, withSteps) {
    const out = { roots: [], steps: [], check: [], ...res, v };
    out.answer = answerOf(out, v);
    if (out.kind !== 'unsupported' && out.kind !== undefined) {
        out.steps.push(S(T('Ответ', 'Answer'), { tex: out.answer.tex, final: true }));
    } else if (out.reason) {
        out.steps.push(S(T('Не удалось решить точно', 'Could not solve exactly'), { text: out.reason, final: true }));
    }
    if (out.odz) out.odz = { tex: out.odz.tex, text: out.odz.text, set: out.odz.set, conditions: out.odz.conds.map((c) => ({ kind: c.kind, expr: c.expr, tex: byLang((l) => condTex(c, l)) })) };
    if (!withSteps) out.steps = [];
    return out;
}

// The reduction formulas simplify applies to what was typed: sin(π − x) = sin x, cos(x + π/2) = −sin x, …
function reductionStep(node) {
    const pairs = [];
    const seen = new Set();
    const walk = (n) => {
        if (n.type === 'fn' && ['sin', 'cos', 'tan', 'cot', 'sec', 'csc'].includes(n.name)) {
            try {
                const a = simplify(n.args[0]);
                const shifted = a.type === 'add' && a.args.some((t) => (t.type === 'sym' && t.name === 'pi' && !t.var) || (t.type === 'mul' && t.args.length === 2 && t.args[0].type === 'num' && t.args[1].type === 'sym' && t.args[1].name === 'pi' && !t.args[1].var));
                if (shifted) {
                    const canon = fn(n.name, a);
                    const after = simplify(canon);
                    const k = nodeKey(canon);
                    if (nodeKey(after) !== k && !seen.has(k)) {
                        seen.add(k);
                        pairs.push([n, after]); // as typed: cos(π/2 − x) = sin x
                    }
                }
            } catch {
                /* left for the solver to report */
            }
        }
        for (const c of nodeChildren(n)) walk(c);
    };
    walk(node);
    if (!pairs.length) return null;
    return S(T('Формулы приведения', 'Reduction formulas'), {
        tex: byLang((l) => pairs.map(([b, a]) => `${tex(b, l)} = ${tex(a, l)}`).join(',\\quad ')),
        text: T('Сдвиг аргумента на целое число полуоборотов π или четвертей π/2 убираем по формулам приведения: функция меняется на кофункцию при сдвиге на нечётное число π/2, знак — как у исходной функции в той четверти.',
            'A shift of the argument by a multiple of π/2 is removed by the reduction formulas: an odd multiple of π/2 turns the function into its cofunction, and the sign is that of the original function in that quadrant.'),
        rule: 'reduction',
    });
}

/**
 * Trigonometric equations: sin/cos/tg/ctg of a linear argument = a, polynomial in one function, homogeneous,
 * a·sin + b·cos = c, double angles. Same result shape as solveEquation (roots are families x = base + period·n,
 * `families` holds them, `answer` prints the school form); opts.interval lists the roots in [α; β].
 */
export function solveTrig(input, v = 'x', opts = {}) {
    return solveEquation(input, v, { ...opts, onlyTrig: true });
}

// ---------------------------------------------------------------- sign charts (the method of intervals)

/** Sum of polynomial fractions → {N, L} with E = N / L (L primitive, no cancelling), or null. */
function ratParts(E, v) {
    const parts = [];
    for (const t of termsOfSum(E)) {
        let nd;
        try {
            nd = numDen(t);
        } catch {
            return null;
        }
        const Pn = Poly.fromNode(nd.num, v);
        const Pd = Poly.fromNode(nd.den, v);
        if (!Pn || !Pd || Pd.isZero()) return null;
        parts.push({ Pn, Pd });
    }
    let L = new Poly([Q.ONE]);
    for (const p of parts) L = polyLcm(L, p.Pd.monic());
    let N = new Poly([]);
    for (const p of parts) {
        const { q, r } = L.divmod(p.Pd);
        if (!r.isZero()) return null;
        N = N.add(p.Pn.mul(q));
    }
    const Lp = L.primitive();
    return { N: N.scale(Lp.lead.div(L.lead)), L: Lp };
}

/** Distinct real roots with multiplicities (square-free decomposition, so numeric roots get them right too). */
function realRootsMult(P, v) {
    if (P.degree < 1) return [];
    const out = [];
    for (const { poly, mult } of P.squareFree()) {
        const r = solveAnyPoly(poly, { v, domain: 'real' });
        for (const x of r.roots) out.push({ ...x, mult });
    }
    return mergeRoots(out, true);
}

function testPoint(a, b) {
    if (a === null && b === null) return Q.ZERO;
    if (a === null) return Q.of(Math.floor(b.approx) - 1);
    if (b === null) return Q.of(Math.ceil(a.approx) + 1);
    const m = (a.approx + b.approx) / 2;
    return Q.of(Number(m.toPrecision(15)).toString());
}

/** Sign chart of N/L: {points: [{node, approx, kind, mN, mL, approxOnly}], signs: [+1|-1, …]} */
function chartOf(N, L, v) {
    const zn = realRootsMult(N, v);
    const zl = L ? realRootsMult(L, v) : [];
    const pts = [];
    for (const r of zn) pts.push({ node: r.node, approx: r.approx, approxOnly: r.approxOnly, mN: r.mult, mL: 0 });
    for (const r of zl) {
        const p = pts.find((x) => sameRoot(x, r));
        if (p) p.mL = r.mult;
        else pts.push({ node: r.node, approx: r.approx, approxOnly: r.approxOnly, mN: 0, mL: r.mult });
    }
    pts.sort((a, b) => a.approx - b.approx);
    const signs = [];
    for (let k = 0; k <= pts.length; k++) {
        const t = testPoint(k ? pts[k - 1] : null, k < pts.length ? pts[k] : null);
        const a = N.evalAt(t).sign();
        const b = L ? L.evalAt(t).sign() : 1;
        signs.push(a * b);
    }
    for (const p of pts) p.kind = p.mL > 0 ? 'pole' : 'zero';
    return { points: pts, signs };
}

/** The set where N/L op 0 (op: > >= < <= != =) from its chart. */
function setFromChart(chart, op) {
    const { points: pts, signs } = chart;
    const want = op === '>' || op === '>=' ? 1 : op === '<' || op === '<=' ? -1 : null;
    const parts = [];
    for (let k = 0; k <= pts.length; k++) {
        const s = signs[k];
        if ((want !== null && s === want) || (op === '!=' && s !== 0)) {
            parts.push({ lo: k ? endOfPoint(pts[k - 1]) : null, hi: k < pts.length ? endOfPoint(pts[k]) : null, loC: false, hiC: false });
        }
    }
    if (op === '>=' || op === '<=' || op === '=') {
        for (const p of pts) if (p.kind === 'zero') {
            const e = endOfPoint(p);
            parts.push({ lo: e, hi: e, loC: true, hiC: true });
        }
    }
    for (const p of pts) p.included = (op === '>=' || op === '<=' || op === '=') && p.kind === 'zero';
    return new IntervalSet(parts);
}

/** Endpoint of a chart point: exact, or a short decimal marked approx. */
function endOfPoint(p) {
    if (!p.approxOnly) return endOf(p.node);
    return Object.freeze({ node: approxNode(p.approx, 5), x: p.approx, q: null, approx: true });
}

/** Public chart shape for widgets. */
function chartOut(chart) {
    return {
        points: chart.points.map((p) => ({ x: p.approx, tex: p.approxOnly ? texB(approxNode(p.approx, 5), { decimals: true }) : texB(p.node), kind: p.kind, included: !!p.included, mult: p.kind === 'pole' ? p.mL : p.mN, approx: !!p.approxOnly })),
        signs: chart.signs.map((s) => (s > 0 ? '+' : s < 0 ? '-' : '0')),
    };
}

/** Silent: the set where expr op 0 for rational expr (null when not rational). */
function signSet(expr, op, v) {
    const s = simp(expr);
    if (!s) return null;
    if (!containsVar(s, v)) {
        const x = approxOf(s);
        if (!Number.isFinite(x)) return null;
        return relHoldsNum(op, x, 0) ? IntervalSet.all() : IntervalSet.empty();
    }
    const rp = ratParts(s, v);
    if (!rp || rp.N.isZero()) return rp && rp.N.isZero() ? (op === '>=' || op === '<=' || op === '=' ? IntervalSet.all() : IntervalSet.empty()).minus(IntervalSet.points(realRootsMult(rp.L, v).map((r) => r.node))) : null;
    return setFromChart(chartOf(rp.N, rp.L.degree >= 1 ? rp.L : null, v), op);
}

// ---------------------------------------------------------------- inequalities

const OP_TEX = { '<': '<', '<=': '\\le', '>': '>', '>=': '\\ge', '!=': '\\ne', '=': '=' };
const OP_FLIP = { '<': '>', '<=': '>=', '>': '<', '>=': '<=', '!=': '!=', '=': '=' };
const strictOf = (op) => op === '<' || op === '>';

function ineqTexB(l, op, r) {
    return byLang((lang) => `${typeof l === 'string' ? l : tex(l, lang)} ${OP_TEX[op]} ${typeof r === 'string' ? r : tex(r, lang)}`);
}

const pointsListTex = (pts, v, l) => pts.map((p) => `${v} = ${tex(p.node, l)}${p.mult > 1 || p.mN > 1 ? `\\ (${l === 'ru' ? '\\text{кратность }' : '\\text{multiplicity }'}${p.mult ?? p.mN})` : ''}`).join(';\\ ');

function signsTex(chart, l) {
    const pts = chart.points;
    const iv = (k) => {
        const a = k ? tex(pts[k - 1].node, l) : '-\\infty';
        const b = k < pts.length ? tex(pts[k].node, l) : '+\\infty';
        return `(${a}${l === 'ru' ? ';\\,' : ',\\ '}${b})`;
    };
    return chart.signs.map((s, k) => `${iv(k)}\\!:\\ ${s > 0 ? '+' : s < 0 ? '-' : '0'}`).join(';\\quad ');
}

/** Method of intervals for N/L op 0 with steps. */
function intervalMethod(N, L, op, ctx, pre = []) {
    const v = ctx.v;
    const steps = [...pre];
    const hasL = L && L.degree >= 1;
    const chart = chartOf(N, hasL ? L : null, v);
    const zeros = chart.points.filter((p) => p.mN > 0);
    const poles = chart.points.filter((p) => p.mL > 0);
    steps.push(S(T('Отмечаем нули числителя на числовой прямой', 'Mark the zeros of the numerator on the number line'), {
        tex: byLang((l) => (zeros.length ? pointsListTex(zeros.map((p) => ({ ...p, mult: p.mN })), v, l) : '\\varnothing')),
        text: strictOf(op)
            ? T('Неравенство строгое — эти точки в ответ не входят (выколотые).', 'The inequality is strict, so these points are not included (open dots).')
            : T('Неравенство нестрогое — эти точки входят в ответ (закрашенные).', 'The inequality is not strict, so these points are included (filled dots).'),
    }));
    if (poles.length) {
        steps.push(S(T('Отмечаем нули знаменателя — они всегда выколотые', 'Mark the zeros of the denominator: they are always excluded'), {
            tex: byLang((l) => pointsListTex(poles.map((p) => ({ ...p, mult: p.mL })), v, l)),
            text: T('На ноль делить нельзя.', 'Division by zero is not allowed.'),
        }));
    }
    const set = setFromChart(chart, op);
    const even = chart.points.filter((p) => (p.mN + p.mL) % 2 === 0);
    steps.push(S(T('Расставляем знаки на промежутках', 'Put the signs on the intervals'), {
        tex: byLang((l) => signsTex(chart, l)),
        text: even.length
            ? T(`Знак проверяем подстановкой точки из промежутка. При переходе через точку чётной кратности (${even.map((p) => `$${tex(p.node)}$`).join(', ')}) знак не меняется.`, `Check the sign by substituting a point from the interval. At points of even multiplicity (${even.map((p) => `$${tex(p.node, 'en')}$`).join(', ')}) the sign does not change.`)
            : T('Знак проверяем подстановкой точки из промежутка; при переходе через корень нечётной кратности знак меняется.', 'Check the sign by substituting a point from the interval; it changes at every root of odd multiplicity.'),
    }));
    const want = op === '>' || op === '>=' ? T('«+»', '“+”') : T('«−»', '“−”');
    steps.push(S(T(`Выбираем промежутки со знаком ${want.ru}`, `Take the intervals with ${want.en}`), {
        tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`),
        text: !strictOf(op) && zeros.some((p) => set.contains(p.node) && !set.parts.some((q) => q.lo && q.hi && cmpEnd(q.lo, q.hi) !== 0 && (q.lo && cmpEnd(q.lo, endOf(p.node)) === 0 || q.hi && cmpEnd(q.hi, endOf(p.node)) === 0)))
            ? T('Нули числителя добавляем — неравенство нестрогое (отдельные точки тоже входят в ответ).', 'The zeros of the numerator are added since the inequality is not strict (isolated points count too).')
            : undefined,
    }));
    return { set, steps, chart: chartOut(chart), approx: chart.points.some((p) => p.approxOnly) };
}

function linearIneq(lhs, op, rhs, A, B, ctx) {
    const v = ctx.v;
    const steps = [];
    let den = 1n;
    for (const q of [...A.c, ...B.c]) den = bigLcm(den, q.d);
    let A1 = A;
    let B1 = B;
    const eqT = (P1, P2, o) => byLang((l) => `${polyTex(P1, v, l)} ${OP_TEX[o]} ${polyTex(P2, v, l)}`);
    if (den > 1n) {
        A1 = A.scale(new Q(den));
        B1 = B.scale(new Q(den));
        steps.push(S(T(`Умножаем обе части на $${den}$`, `Multiply both sides by $${den}$`), {
            tex: eqT(A1, B1, op),
            text: T('Число положительное — знак неравенства не меняется.', 'The number is positive, so the sign stays the same.'),
        }));
    } else if (nodeKey(simpOr(lhs)) !== nodeKey(A.toNode(v)) || nodeKey(simpOr(rhs)) !== nodeKey(B.toNode(v))) {
        steps.push(S(T('Раскрываем скобки и приводим подобные', 'Expand the brackets and collect like terms'), { tex: eqT(A1, B1, op) }));
    }
    const a = A1.coeff(1).sub(B1.coeff(1));
    const b = B1.coeff(0).sub(A1.coeff(0));
    steps.push(S(T(`Переносим слагаемые с $${v}$ влево, числа — вправо`, `Move the $${v}$ terms to the left and the numbers to the right`), {
        tex: ineqTexB(monoNode(a, v), op, num(b)),
    }));
    if (a.isZero()) {
        const ok = relHoldsNum(op, 0, b.toNumber());
        steps.push(S(ok ? T('Получилось верное числовое неравенство', 'A true numeric inequality') : T('Получилось неверное числовое неравенство', 'A false numeric inequality'), {
            tex: ineqTexB('0', op, num(b)),
            text: ok ? T('Подходит любое число.', 'Every number fits.') : T('Решений нет.', 'No solutions.'),
        }));
        return { set: ok ? IntervalSet.all() : IntervalSet.empty(), steps, type: 'linear' };
    }
    const r = b.div(a);
    const op2 = a.isNeg() ? OP_FLIP[op] : op;
    if (!a.isOne()) {
        steps.push(S(a.isNeg() ? T(`Делим на $${tex(num(a))}$ — число отрицательное, знак неравенства меняется`, `Divide by $${tex(num(a), 'en')}$: a negative number, so the sign flips`) : T(`Делим на $${tex(num(a))}$ — знак не меняется`, `Divide by $${tex(num(a), 'en')}$: the sign stays`), {
            tex: ineqTexB(v, op2, num(r)),
        }));
    }
    const set = relToSet(op2, endOf(num(r)));
    const chart = chartOf(new Poly([r.neg(), Q.ONE]).scale(a.isNeg() ? Q.MINUS_ONE : Q.ONE), null, v);
    setFromChart(chart, op);
    return { set, steps, chart: chartOut(chart), type: 'linear' };
}

function quadIneq(P0, op0, ctx, pre) {
    const v = ctx.v;
    const steps = [...pre];
    let P = P0;
    let op = op0;
    if (P.lead.isNeg()) {
        P = P.neg();
        op = OP_FLIP[op];
        steps.push(S(T('Умножаем на $-1$ и меняем знак неравенства', 'Multiply by $-1$ and flip the sign'), {
            tex: byLang((l) => `${polyTex(P, v, l)} ${OP_TEX[op]} 0`),
            text: T('Так старший коэффициент станет положительным.', 'Now the leading coefficient is positive.'),
        }));
    }
    const q = quadSolve(P, ctx);
    const roots = q.roots;
    steps.push(S(byLang((l) => (l === 'ru' ? `Корни трёхчлена: решаем $${polyTex(P, v, l)} = 0$` : `Roots of the trinomial: solve $${polyTex(P, v, l)} = 0$`)), {
        tex: byLang((l) => rootsTex(roots, v, l)),
        sub: q.steps,
    }));
    const chart = chartOf(P, null, v);
    const set = setFromChart(chart, op);
    const up = T('ветви вверх', 'opening upwards');
    let text;
    if (roots.length === 2) text = T(`Парабола $y = ${polyTex(P, v, 'ru')}$, ${up.ru}: она ниже оси $O${v}$ между корнями и выше — вне отрезка между ними.`, `The parabola $y = ${polyTex(P, v, 'en')}$ is ${up.en}: it is below the $${v}$-axis between the roots and above it outside.`);
    else if (roots.length === 1) text = T(`Парабола $y = ${polyTex(P, v, 'ru')}$, ${up.ru}, касается оси в одной точке и больше нигде не опускается ниже неё.`, `The parabola $y = ${polyTex(P, v, 'en')}$, ${up.en}, touches the axis at one point and is above it everywhere else.`);
    else text = T(`Корней нет: парабола $y = ${polyTex(P, v, 'ru')}$, ${up.ru}, целиком выше оси $O${v}$ — трёхчлен положителен при всех $${v}$.`, `No roots: the parabola $y = ${polyTex(P, v, 'en')}$, ${up.en}, lies entirely above the $${v}$-axis, so the trinomial is positive for all $${v}$.`);
    steps.push(S(T('Смотрим на параболу', 'Look at the parabola'), { text, tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    return { set, steps, chart: chartOut(chart), type: 'quadratic' };
}

function ineqConst(E, op, steps) {
    const x = approxOf(E);
    const z = exactZero(E);
    const val = z === true ? 0 : x;
    const ok = relHoldsNum(op, val, 0);
    steps.push(S(ok ? T('Переменная сокращается, получается верное неравенство', 'The variable cancels and a true inequality remains') : T('Переменная сокращается, получается неверное неравенство', 'The variable cancels and a false inequality remains'), {
        tex: ineqTexB(E, op, N0),
    }));
    return { set: ok ? IntervalSet.all() : IntervalSet.empty(), steps, type: 'identity' };
}

/** f op g with steps → {set, steps, chart?, type} or {set: null, reason}. */
function ineqCore(lhs, op, rhs, ctx) {
    const v = ctx.v;
    if (ctx.depth > 6) return { set: null, steps: [], reason: T('Слишком сложное неравенство.', 'The inequality is too complex.') };
    let E;
    try {
        E = simplify(add(lhs, neg(rhs)));
    } catch (e) {
        return { set: null, steps: [], reason: e instanceof MathError ? e.msg : T('Не удалось упростить.', 'Could not simplify.') };
    }
    if (!containsVar(E, v)) return ineqConst(E, op, []);
    const P = Poly.fromNode(rel('=', lhs, rhs), v);
    if (P && P.degree >= 1) {
        if (P.degree === 1) {
            const A = Poly.fromNode(lhs, v);
            const B = Poly.fromNode(rhs, v);
            if (A && B) return linearIneq(lhs, op, rhs, A, B, ctx);
        }
        const pre = [];
        const rhsZero = isZeroNode(simpOr(rhs));
        if (!(rhsZero && nodeKey(simpOr(lhs)) === nodeKey(P.toNode(v)))) {
            pre.push(S(T('Переносим всё в левую часть и приводим подобные', 'Move everything to the left and collect like terms'), { tex: byLang((l) => `${polyTex(P, v, l)} ${OP_TEX[op]} 0`) }));
        }
        if (P.degree === 2) return quadIneq(P, op, ctx, pre);
        const fz = factoredNode(P, v);
        if (nodeKey(fz) !== nodeKey(P.toNode(v))) pre.push(S(T('Раскладываем на множители', 'Factor'), { tex: byLang((l) => `${tex(fz, l)} ${OP_TEX[op]} 0`) }));
        return { ...intervalMethod(P, null, op, ctx, pre), type: 'polynomial' };
    }
    const rp = ratParts(E, v);
    if (rp && rp.L.degree >= 1) {
        const pre = [S(T('Переносим всё в левую часть и приводим к общему знаменателю', 'Move everything to the left and bring to a common denominator'), {
            tex: byLang((l) => `\\frac{${tex(rp.N.degree >= 1 ? factoredNode(rp.N, v) : rp.N.toNode(v), l)}}{${tex(factoredNode(rp.L, v), l)}} ${OP_TEX[op]} 0`),
            text: T('Умножать на знаменатель нельзя — его знак неизвестен. Решаем методом интервалов.', 'We may not multiply by the denominator (its sign is unknown), so we use the method of intervals.'),
        })];
        if (rp.N.isZero()) {
            const set = (op === '>=' || op === '<=' ? IntervalSet.all() : IntervalSet.empty()).minus(IntervalSet.points(realRootsMult(rp.L, v).map((r) => r.node)));
            return { set, steps: pre, type: 'rational' };
        }
        return { ...intervalMethod(rp.N, rp.L, op, ctx, pre), type: 'rational' };
    }
    const tries = [
        () => (nodeSome(E, (n) => n.type === 'fn' && n.name === 'abs') ? absIneq(E, op, ctx) : null),
        () => expIneq(E, op, ctx),
        () => logIneq(lhs, op, rhs, E, ctx),
        () => (hasRadical(E, v) ? radIneq(E, op, ctx) : null),
        () => nodeLinearIneq(E, op, ctx),
        () => rootsIneq(lhs, op, rhs, E, ctx),
    ];
    for (const t of tries) {
        const r = t();
        if (r) return r;
    }
    return { set: null, steps: [], reason: T('Такие неравенства решатель пока не решает.', 'This kind of inequality is not supported yet.') };
}

/** A single even root against a constant: √f op c. */
function radIneq(E, op, ctx) {
    const v = ctx.v;
    const terms = termsOfSum(E);
    const rads = terms.filter((t) => hasRadical(t, v));
    if (rads.length !== 1) return null;
    const sp = splitRadicalTerm(rads[0], v);
    if (!sp) return null;
    const e = numValue(sp.R.exp);
    if (e.n !== 1n) return null;
    const q = e.d;
    const kv = approxOf(sp.coef);
    if (!Number.isFinite(kv) || kv === 0) return null;
    const c = simpOr(div(neg(sumNode(terms.filter((t) => t !== rads[0]))), sp.coef));
    if (containsVar(c, v)) return null;
    const op2 = kv < 0 ? OP_FLIP[op] : op;
    const f = sp.R.base;
    const cv = approxOf(c);
    const steps = [S(T('Уединяем корень', 'Isolate the root'), { tex: ineqTexB(sp.R, op2, c) })];
    const sub = (l2, o2, r2) => ineqCore(l2, o2, r2, { ...ctx, depth: ctx.depth + 1 });
    const even = q % 2n === 0n;
    if (!even) {
        const cq = simpOr(pow(c, num(q)));
        steps.push(S(T('Возводим в нечётную степень — знак сохраняется', 'Raise to an odd power: the sign stays'), { tex: ineqTexB(f, op2, cq) }));
        const r = sub(f, op2, cq);
        if (!r.set) return null;
        return { set: r.set, steps: [...steps, ...r.steps], chart: r.chart, type: 'radical' };
    }
    const dom = sub(f, '>=', N0);
    if (!dom.set) return null;
    const cz = exactZero(c) === true;
    let set;
    if (op2 === '<' || op2 === '<=') {
        if (cv < 0 || (cz && op2 === '<')) {
            steps.push(S(T('Корень не бывает отрицательным', 'A root is never negative'), { text: T('Решений нет.', 'No solutions.') }));
            return { set: IntervalSet.empty(), steps, type: 'radical' };
        }
        const cq = simpOr(pow(c, num(q)));
        steps.push(S(T('Обе части неотрицательны — возводим в степень, добавляя условие существования корня', 'Both sides are non-negative: raise to the power and keep the radicand non-negative'), {
            tex: byLang((l) => casesTex([`${tex(f, l)} \\ge 0`, `${tex(f, l)} ${OP_TEX[op2]} ${tex(cq, l)}`])),
        }));
        const r = sub(f, op2, cq);
        if (!r.set) return null;
        set = r.set.intersect(dom.set);
    } else {
        if (cv < 0 || (cz && op2 === '>=')) {
            steps.push(S(T('Корень неотрицателен — неравенство верно везде, где корень определён', 'A root is non-negative: the inequality holds wherever the root is defined'), { tex: byLang((l) => `${tex(f, l)} \\ge 0`) }));
            set = dom.set;
        } else {
            const cq = simpOr(pow(c, num(q)));
            steps.push(S(T('Обе части неотрицательны — возводим в степень', 'Both sides are non-negative: raise to the power'), { tex: ineqTexB(f, op2, cq), text: T('Условие $f \\ge 0$ выполнится само: $f$ больше положительного числа.', 'The condition $f \\ge 0$ holds automatically: $f$ exceeds a positive number.') }));
            const r = sub(f, op2, cq);
            if (!r.set) return null;
            set = r.set.intersect(dom.set);
        }
    }
    steps.push(S(T('Ответ этого шага', 'The result of this step'), { tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    return { set, steps, type: 'radical' };
}

/** a·x + b op 0 with constant (possibly irrational) node coefficients. */
function nodeLinearIneq(E, op, ctx) {
    const v = ctx.v;
    let ct;
    try {
        ct = collectTerms(E, v);
    } catch {
        return null;
    }
    if (!ct || !ct.has(1) || ![...ct.keys()].every((d) => d === 0 || d === 1)) return null;
    const a = ct.get(1);
    const b = ct.get(0) ?? N0;
    if (!isConstNode(a) || !isConstNode(b)) return null;
    const av = approxOf(a);
    if (!Number.isFinite(av) || av === 0) return null;
    const r = simpOr(div(neg(b), a));
    const op2 = av < 0 ? OP_FLIP[op] : op;
    const steps = [S(T(`Выражаем $${v}$`, `Solve for $${v}$`), {
        tex: ineqTexB(v, op2, r),
        text: av < 0 ? T('Делим на отрицательное число — знак неравенства меняется.', 'Dividing by a negative number flips the sign.') : undefined,
    })];
    return { set: relToSet(op2, endOf(r)), steps, type: 'linear' };
}

function absIneq(E, op, ctx) {
    const v = ctx.v;
    const A = outermost(E, (n) => n.type === 'fn' && n.name === 'abs' && containsVar(n, v));
    const steps = [];
    if (A.length === 1) {
        const f = A[0].args[0];
        const li = linearIn(replaceNode(E, A[0], sym(TMP)), TMP, v);
        if (li && !containsVar(li.beta, v)) {
            const av = approxOf(li.alpha);
            const c = simpOr(div(neg(li.beta), li.alpha));
            const op2 = av < 0 ? OP_FLIP[op] : op;
            const cv = approxOf(c);
            const cz = exactZero(c) === true;
            steps.push(S(T('Уединяем модуль', 'Isolate the absolute value'), { tex: ineqTexB(A[0], op2, c) }));
            const sub = (l2, o2, r2) => ineqCore(l2, o2, r2, { ...ctx, depth: ctx.depth + 1 });
            if (op2 === '<' || op2 === '<=') {
                if (cv < 0 || (cz && op2 === '<')) {
                    steps.push(S(T('Модуль не бывает меньше отрицательного числа (или нуля)', 'An absolute value is never below a negative number (or zero)'), { text: T('Решений нет.', 'No solutions.') }));
                    return { set: IntervalSet.empty(), steps, type: 'abs' };
                }
                if (cz) {
                    steps.push(S(T('Модуль не больше нуля, только когда он равен нулю', 'An absolute value is at most zero only when it is zero'), { tex: byLang((l) => `${tex(f, l)} = 0`) }));
                    const r = solveCore(f, N0, { ...ctx, depth: ctx.depth + 1 });
                    const set = r.kind === 'roots' ? IntervalSet.points(r.roots.map((x) => x.node)) : r.kind === 'all' ? IntervalSet.all() : IntervalSet.empty();
                    return { set, steps: [...steps, ...r.steps], type: 'abs' };
                }
                steps.push(S(T('Двойное неравенство', 'A double inequality'), {
                    tex: byLang((l) => `${tex(simpOr(neg(c)), l)} ${OP_TEX[op2]} ${tex(f, l)} ${OP_TEX[op2]} ${tex(c, l)}`),
                    text: T('Расстояние от нуля меньше $c$ — значит, число между $-c$ и $c$.', 'The distance from zero is less than $c$, so the number lies between $-c$ and $c$.'),
                }));
                const r1 = sub(f, OP_FLIP[op2], simpOr(neg(c)));
                const r2 = sub(f, op2, c);
                if (!r1.set || !r2.set) return null;
                const set = r1.set.intersect(r2.set);
                steps.push(S(byLang((l) => `$${tex(f, l)} ${OP_TEX[OP_FLIP[op2]]} ${tex(simpOr(neg(c)), l)}$`), { tex: byLang((l) => `${v} \\in ${intervalTex(r1.set, l)}`), sub: r1.steps }));
                steps.push(S(byLang((l) => `$${tex(f, l)} ${OP_TEX[op2]} ${tex(c, l)}$`), { tex: byLang((l) => `${v} \\in ${intervalTex(r2.set, l)}`), sub: r2.steps }));
                steps.push(S(T('Пересекаем', 'Intersect'), { tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`) }));
                return { set, steps, type: 'abs' };
            }
            // > and >=
            if (cv < 0 || (cz && op2 === '>=')) {
                steps.push(S(T('Модуль всегда неотрицателен', 'An absolute value is always non-negative'), { text: T('Неравенство верно при любом $x$.', 'The inequality holds for every $x$.') }));
                return { set: IntervalSet.all(), steps, type: 'abs' };
            }
            if (cz) {
                steps.push(S(T('Модуль больше нуля везде, кроме нуля подмодульного выражения', 'An absolute value is positive except where the inside is zero'), { tex: byLang((l) => `${tex(f, l)} \\ne 0`) }));
                const r = solveCore(f, N0, { ...ctx, depth: ctx.depth + 1 });
                const set = r.kind === 'roots' ? IntervalSet.all().minus(IntervalSet.points(r.roots.map((x) => x.node))) : r.kind === 'all' ? IntervalSet.empty() : IntervalSet.all();
                return { set, steps: [...steps, ...r.steps], type: 'abs' };
            }
            steps.push(S(T('Совокупность двух неравенств', 'Two alternatives'), {
                tex: byLang((l) => `${tex(f, l)} ${OP_TEX[OP_FLIP[op2]]} ${tex(simpOr(neg(c)), l)} ${orTex(l)} ${tex(f, l)} ${OP_TEX[op2]} ${tex(c, l)}`),
                text: T('Расстояние от нуля больше $c$ — число левее $-c$ или правее $c$.', 'The distance from zero is more than $c$: the number is left of $-c$ or right of $c$.'),
            }));
            const r1 = sub(f, OP_FLIP[op2], simpOr(neg(c)));
            const r2 = sub(f, op2, c);
            if (!r1.set || !r2.set) return null;
            const set = r1.set.union(r2.set);
            steps.push(S(byLang((l) => `$${tex(f, l)} ${OP_TEX[OP_FLIP[op2]]} ${tex(simpOr(neg(c)), l)}$`), { tex: byLang((l) => `${v} \\in ${intervalTex(r1.set, l)}`), sub: r1.steps }));
            steps.push(S(byLang((l) => `$${tex(f, l)} ${OP_TEX[op2]} ${tex(c, l)}$`), { tex: byLang((l) => `${v} \\in ${intervalTex(r2.set, l)}`), sub: r2.steps }));
            steps.push(S(T('Объединяем', 'Take the union'), { tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`) }));
            return { set, steps, type: 'abs' };
        }
    }
    // several absolute values (or |f| against an expression): intervals by the zeros of the insides
    let pts = [];
    for (const a of A) {
        const P = Poly.fromNode(a.args[0], v);
        if (!P) return null;
        if (P.degree >= 1) pts.push(...solveAnyPoly(P, { v, domain: 'real' }).roots);
    }
    pts = mergeRoots(pts);
    if (pts.length > 12) return null;
    steps.push(S(T('Отмечаем нули подмодульных выражений', 'Mark the zeros of the expressions inside the absolute values'), {
        tex: byLang((l) => (pts.length ? pts.map((p) => `${v} = ${tex(p.node, l)}`).join(';\\ ') : '\\varnothing')),
        text: T('На каждом промежутке между ними модули раскрываются однозначно.', 'On each interval between them the absolute values open in one way.'),
    }));
    const bounds = [null, ...pts, null];
    let set = IntervalSet.empty();
    for (let k = 0; k + 1 < bounds.length; k++) {
        const lo = bounds[k];
        const hi = bounds[k + 1];
        const t = lo === null && hi === null ? 0 : lo === null ? hi.approx - 1 : hi === null ? lo.approx + 1 : (lo.approx + hi.approx) / 2;
        const Ei = simpOr(mapNode(E, (n) => {
            if (n.type !== 'fn' || n.name !== 'abs' || !containsVar(n, v)) return undefined;
            return approxOf(n.args[0], { [v]: t }) >= 0 ? n.args[0] : neg(n.args[0]);
        }));
        const piece = IntervalSet.interval(lo && lo.node, hi && hi.node, lo !== null, false);
        const sub = ineqCore(Ei, op, N0, { ...ctx, depth: ctx.depth + 1 });
        if (!sub.set) return null;
        const part = sub.set.intersect(piece);
        set = set.union(part);
        steps.push(S(byLang((l) => (l === 'ru' ? `На $${intervalTex(piece, l)}$` : `On $${intervalTex(piece, l)}$`)), {
            tex: byLang((l) => `${tex(Ei, l)} ${OP_TEX[op]} 0 \\;\\Rightarrow\\; ${v} \\in ${intervalTex(part, l)}`),
            sub: sub.steps,
        }));
    }
    steps.push(S(T('Объединяем', 'Take the union'), { tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    return { set, steps, type: 'abs' };
}

/** Map a set of t-values through a monotonic increasing map t → x (fn gets an endpoint node, returns a node or null = ±∞). */
function mapSet(set, f) {
    return new IntervalSet(set.parts.map((p) => ({
        lo: p.lo === null ? null : f(p.lo.node, 'lo'),
        hi: p.hi === null ? null : f(p.hi.node, 'hi'),
        loC: p.loC,
        hiC: p.hiC,
    })).map((p) => ({ ...p, lo: p.lo && endOf(p.lo), hi: p.hi && endOf(p.hi) })));
}

// p·b^f − q·b^g op 0 with q/p a power of b: b^f op b^(g + m) → f op g + m (by the monotonicity of b^t)
function twoPowersIneq(E, op, ctx) {
    const v = ctx.v;
    const ts = termsOfSum(E);
    if (ts.length !== 2) return null;
    const parts = ts.map((t) => {
        const { coef, rest } = splitCoeff(t);
        const r = rest ?? N1;
        if (r.type !== 'pow' || containsVar(r.base, v) || !containsVar(r.exp, v)) return null;
        const bi = baseInfo(r.base);
        return bi && { coef, base: r.base, exp: r.exp, bi };
    });
    if (parts.some((x) => !x) || !sameBase(parts[0].bi.c, parts[1].bi.c)) return null;
    let [P1, P2] = parts;
    let op1 = op;
    if (P1.coef.isNeg()) {
        [P1, P2] = [P2, P1];
    }
    if (!P1.coef.isPos() || !P2.coef.isNeg()) return null;
    // P1.coef·b1^f + P2.coef·b2^g op 0  ⇔  b1^f op (−P2.coef/P1.coef)·b2^g
    const k = P2.coef.neg().div(P1.coef);
    const m = exactPower(P1.bi.c, num(k));
    if (m === null) return null;
    // everything as powers of the primitive base c: b1^f = c^(k1 f)
    const c = P1.bi.c;
    const cN = baseNode(c);
    const left = simpOr(mul(num(P1.bi.k), P1.exp));
    const right = simpOr(add(mul(num(P2.bi.k), P2.exp), num(m)));
    const dec = approxOf(cN) < 1;
    const op3 = dec ? OP_FLIP[op1] : op1;
    const steps = [S(T('Приводим обе части к одному основанию', 'Bring both sides to one base'), {
        tex: byLang((l) => `${tex(pow(cN, left), l)} ${OP_TEX[op1]} ${tex(pow(cN, right), l)}`),
        text: T(`Переносим степень в правую часть и записываем $${num(k).value.toTex('ru')} = ${tex(pow(cN, num(m)))}$; $a^x \\cdot a^y = a^{x+y}$.`, `Move one power to the right and write $${num(k).value.toTex('en')} = ${tex(pow(cN, num(m)), 'en')}$; $a^x \\cdot a^y = a^{x+y}$.`),
    }), S(dec ? T(`Основание $${tex(cN)}$ меньше 1 — функция убывает, знак меняется`, `The base $${tex(cN, 'en')}$ is below 1: the function decreases, so the sign flips`) : T(`Основание $${tex(cN)}$ больше 1 — функция возрастает, знак сохраняется`, `The base $${tex(cN, 'en')}$ is above 1: the function increases, so the sign stays`), { tex: ineqTexB(left, op3, right) })];
    const r = ineqCore(left, op3, right, { ...ctx, depth: ctx.depth + 1 });
    if (!r.set) return null;
    return { set: r.set, steps: [...steps, ...r.steps], chart: r.chart, type: 'exponential' };
}

function expIneq(E, op, ctx) {
    const v = ctx.v;
    const tp = twoPowersIneq(E, op, ctx);
    if (tp) return tp;
    const info = analyzeExp(E, v);
    if (!info || info.mixed) return null;
    const { c, terms, constant } = info;
    const cN = baseNode(c);
    const steps = [];
    const sub = (l2, o2, r2) => ineqCore(l2, o2, r2, { ...ctx, depth: ctx.depth + 1 });
    if (terms.length === 1 && terms[0].pows.length === 1) {
        const { coef, pows } = terms[0];
        const kv = approxOf(coef);
        if (!Number.isFinite(kv) || kv === 0) return null;
        const op2 = kv < 0 ? OP_FLIP[op] : op;
        const R = simpOr(div(neg(constant), coef));
        const b = pows[0].base;
        const f = pows[0].exp;
        steps.push(S(T('Уединяем степень', 'Isolate the power'), { tex: ineqTexB(pows[0], op2, R), text: kv < 0 ? T('Делили на отрицательное число — знак поменялся.', 'We divided by a negative number, so the sign flipped.') : undefined }));
        const Rv = approxOf(R);
        if (!(Rv > 0) || exactZero(R) === true) {
            const all = op2 === '>' || op2 === '>=';
            steps.push(S(T('Степень положительного числа всегда положительна', 'A power of a positive number is always positive'), { text: all ? T('Неравенство верно при любом $x$.', 'It holds for every $x$.') : T('Решений нет.', 'No solutions.') }));
            return { set: all ? IntervalSet.all() : IntervalSet.empty(), steps, type: 'exponential' };
        }
        const bv = approxOf(b);
        const dec = bv < 1;
        const op3 = dec ? OP_FLIP[op2] : op2;
        const bi = baseInfo(b);
        const r = exactPower(bi.c, R);
        const rhsN = r !== null ? num(r.div(bi.k)) : logNodeB(b, R);
        const rDisp = r !== null ? pow(b, rhsN) : null;
        steps.push(S(dec ? T(`Основание $${tex(b)}$ меньше 1 — функция убывает, знак неравенства меняется`, `The base $${tex(b, 'en')}$ is below 1: the function decreases, so the sign flips`) : T(`Основание $${tex(b)}$ больше 1 — функция возрастает, знак сохраняется`, `The base $${tex(b, 'en')}$ is above 1: the function increases, so the sign stays`), {
            tex: byLang((l) => (rDisp ? `${tex(pows[0], l)} ${OP_TEX[op2]} ${tex(rDisp, l)} \\;\\Rightarrow\\; ` : '') + `${tex(f, l)} ${OP_TEX[op3]} ${tex(rhsN, l)}`),
        }));
        const r2 = sub(f, op3, rhsN);
        if (!r2.set) return null;
        steps.push(...r2.steps);
        return { set: r2.set, steps, chart: r2.chart, type: 'exponential' };
    }
    // polynomial in t = c^(m x)
    const lin = [];
    for (const t of terms) {
        const lf = linearForm(t.g, [v]);
        const k = numValue(t.coef);
        if (!lf || !k || lf.coeffs[v].isZero()) return null;
        lin.push({ m: lf.coeffs[v], s: lf.constant, k, t });
    }
    let m = lin[0].m.abs();
    for (const x of lin) m = qGcd(m, x.m.abs());
    if (lin.some((x) => x.m.isNeg())) return null;
    const C0 = numValue(constant);
    if (!C0 || c === 'e') return null;
    const coefs = new Map([[0, C0]]);
    for (const x of lin) {
        const j = x.m.div(m);
        if (!j.isInt() || !x.s.isInt()) return null;
        const jj = Number(j.n);
        coefs.set(jj, (coefs.get(jj) ?? Q.ZERO).add(x.k.mul(c.pow(x.s.n))));
    }
    const maxJ = Math.max(...coefs.keys());
    if (maxJ > 6) return null;
    const arr = new Array(maxJ + 1).fill(Q.ZERO);
    for (const [j, q] of coefs) arr[j] = q;
    const Pt = new Poly(arr);
    const tNode = m.isInt() ? pow(num(c.pow(m.n)), sym(v)) : pow(cN, simpOr(mul(num(m), sym(v))));
    steps.push(S(T(`Замена $t = ${tex(tNode)}$, $t > 0$`, `Substitute $t = ${tex(tNode, 'en')}$, $t > 0$`), { tex: byLang((l) => `${polyTex(Pt, 't', l)} ${OP_TEX[op]} 0`) }));
    const tr = ineqCore(Pt.toNode('t'), op, N0, { ...ctx, v: 't', depth: ctx.depth + 1 });
    if (!tr.set) return null;
    const tset = tr.set.intersect(IntervalSet.above(0, false));
    steps.push(S(T('Решаем неравенство относительно $t$ (с условием $t > 0$)', 'Solve for $t$ (with $t > 0$)'), { tex: byLang((l) => `t \\in ${intervalTex(tset, l)}`), sub: tr.steps }));
    const mq = m;
    const back = (node) => {
        const tv = approxOf(node);
        if (!(tv > 0)) return null;
        const r = exactPower(c, node);
        return r !== null ? num(r.div(mq)) : simpOr(div(logNode(c, node), num(mq)));
    };
    const parts = tset.parts.map((p) => ({ lo: p.lo === null || p.lo.x <= 0 ? null : endOf(back(p.lo.node)), hi: p.hi === null ? null : endOf(back(p.hi.node)), loC: p.lo !== null && p.lo.x > 0 && p.loC, hiC: p.hiC }));
    const set = new IntervalSet(parts);
    steps.push(S(T('Обратная замена', 'Substitute back'), {
        tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`),
        text: T(`Функция $t = ${tex(tNode)}$ возрастает, поэтому границы переходят в границы.`, `The function $t = ${tex(tNode, 'en')}$ increases, so the bounds map to bounds.`),
    }));
    return { set, steps, chart: tr.chart, type: 'exponential' };
}

function logIneq(lhs, op, rhs, E, ctx) {
    const v = ctx.v;
    const an = analyzeLog(E, v);
    if (!an || an.vt.some((x) => x.info.varBase)) return null;
    const { vt, constant } = an;
    const steps = [];
    const sub = (l2, o2, r2) => ineqCore(l2, o2, r2, { ...ctx, depth: ctx.depth + 1 });
    const C = simpOr(sumNode(constant));
    let odz = IntervalSet.all();
    for (const x of vt) {
        const s = sub(x.info.arg, '>', N0);
        if (!s.set) return null;
        odz = odz.intersect(s.set);
    }
    steps.push(S(T('ОДЗ: под логарифмами — положительные числа', 'Domain: the arguments of the logarithms are positive'), {
        tex: byLang((l) => `${vt.map((x) => `${tex(x.info.arg, l)} > 0`).join(',\\ ')} \\;\\Rightarrow\\; ${v} \\in ${intervalTex(odz, l)}`),
    }));
    const monotone = (b) => {
        const dec = approxOf(b) < 1;
        return {
            dec,
            step: dec ? T(`Основание $${tex(b)}$ меньше 1 — логарифм убывает, знак неравенства меняется`, `The base $${tex(b, 'en')}$ is below 1: the logarithm decreases, so the sign flips`) : T(`Основание $${tex(b)}$ больше 1 — логарифм возрастает, знак сохраняется`, `The base $${tex(b, 'en')}$ is above 1: the logarithm increases, so the sign stays`),
        };
    };
    let res;
    if (vt.length === 1 && vt[0].p === 1) {
        const { coef, info, F } = vt[0];
        const kv = approxOf(coef);
        if (!Number.isFinite(kv) || kv === 0) return null;
        const op2 = kv < 0 ? OP_FLIP[op] : op;
        const R = simpOr(div(neg(C), coef));
        if (!isConstNode(R)) return null;
        const val = simpOr(pow(info.base, R));
        const mono = monotone(info.base);
        const op3 = mono.dec ? OP_FLIP[op2] : op2;
        steps.push(S(T('Уединяем логарифм', 'Isolate the logarithm'), { tex: ineqTexB(F, op2, R) }));
        steps.push(S(mono.step, { tex: byLang((l) => `${tex(F, l)} ${OP_TEX[op2]} ${tex(logNodeB(info.base, val), l)} \\;\\Rightarrow\\; ${tex(info.arg, l)} ${OP_TEX[op3]} ${tex(val, l)}`), text: T(`Число $${tex(R)}$ записали как логарифм: $${tex(R)} = ${tex(logNodeB(info.base, val))}$.`, `We wrote $${tex(R, 'en')}$ as a logarithm: $${tex(R, 'en')} = ${tex(logNodeB(info.base, val), 'en')}$.`) }));
        res = sub(info.arg, op3, val);
    } else if (vt.length === 2 && isZeroNode(C) && vt.every((x) => x.p === 1 && x.info.k.isOne()) && nodeKey(vt[0].info.base) === nodeKey(vt[1].info.base)) {
        const k0 = numValue(vt[0].coef);
        const k1 = numValue(vt[1].coef);
        if (!k0 || !k1 || !k0.add(k1).isZero()) return null;
        const [pos, negT] = k0.isPos() ? [vt[0], vt[1]] : [vt[1], vt[0]];
        const mono = monotone(pos.info.base);
        const op3 = mono.dec ? OP_FLIP[op] : op;
        steps.push(S(mono.step, { tex: byLang((l) => `${tex(pos.info.arg, l)} ${OP_TEX[op3]} ${tex(negT.info.arg, l)}`) }));
        res = sub(pos.info.arg, op3, negT.info.arg);
    } else if (vt.length >= 2 && vt.every((x) => x.p === 1 && nodeKey(x.info.base) === nodeKey(vt[0].info.base) && numValue(x.coef)?.isInt())) {
        // Σ cᵢ·log_b fᵢ + C op 0 → log_b(Π fᵢ^cᵢ) op −C: on the domain every fᵢ > 0, so the rules hold
        const b = vt[0].info.base;
        const up = [];
        const down = [];
        for (const x of vt) {
            const c = numValue(x.coef);
            (c.isNeg() ? down : up).push(c.abs().isOne() ? x.info.arg : pow(x.info.arg, num(c.abs())));
        }
        const prod = down.length ? div(up.length ? mul(up) : N1, mul(down)) : mul(up);
        const R = simpOr(neg(C));
        if (!isConstNode(R)) return null;
        const val = simpOr(pow(b, R));
        const mono = monotone(b);
        const op3 = mono.dec ? OP_FLIP[op] : op;
        steps.push(S(T('Записываем сумму логарифмов одним логарифмом', 'Write the sum of logarithms as one logarithm'), {
            tex: ineqTexB(logNodeB(b, prod), op, R),
            text: T('На ОДЗ все аргументы положительны, поэтому $\\log_a x + \\log_a y = \\log_a(xy)$, $\\log_a x - \\log_a y = \\log_a \\frac{x}{y}$, $k\\log_a x = \\log_a x^k$.', 'On the domain every argument is positive, so $\\log_a x + \\log_a y = \\log_a(xy)$, $\\log_a x - \\log_a y = \\log_a \\frac{x}{y}$, $k\\log_a x = \\log_a x^k$.'),
        }));
        steps.push(S(mono.step, { tex: byLang((l) => `${tex(prod, l)} ${OP_TEX[op3]} ${tex(val, l)}`), text: T(`Число $${tex(R)}$ записали как логарифм: $${tex(R)} = ${tex(logNodeB(b, val))}$.`, `We wrote $${tex(R, 'en')}$ as a logarithm: $${tex(R, 'en')} = ${tex(logNodeB(b, val), 'en')}$.`) }));
        res = sub(prod, op3, val);
    } else if (vt.every((x) => nodeKey(x.F) === nodeKey(vt[0].F)) && vt.some((x) => x.p >= 2)) {
        // a polynomial in one logarithm: the substitution t = log_b f
        const F = vt[0].F;
        const tv = v === 't' ? 'u' : 't';
        const T0 = sym(tv);
        const poly = simpOr(add([...vt.map((x) => mul(x.coef, x.p === 1 ? T0 : pow(T0, num(x.p)))), ...constant]));
        const rt = ineqCore(poly, op, N0, { ...ctx, v: tv, depth: ctx.depth + 1 });
        if (!rt.set) return null;
        steps.push(S(T(`Замена $${tv} = ${tex(F)}$`, `Substitute $${tv} = ${tex(F, 'en')}$`), { tex: ineqTexB(poly, op, N0) }));
        steps.push(...rt.steps);
        steps.push(S(T(`Получили $${tv} \\in ${intervalTex(rt.set, 'ru')}$`, `We got $${tv} \\in ${intervalTex(rt.set, 'en')}$`)));
        let back = IntervalSet.empty();
        const backSteps = [];
        for (const part of rt.set.parts) {
            let piece = IntervalSet.all();
            const conds = [];
            if (part.lo && part.hi && cmpEnd(part.lo, part.hi) === 0) conds.push(['=', part.lo.node]);
            else {
                if (part.lo) conds.push([part.loC ? '>=' : '>', part.lo.node]);
                if (part.hi) conds.push([part.hiC ? '<=' : '<', part.hi.node]);
            }
            for (const [o, c] of conds) {
                let r;
                if (o === '=') {
                    const e = solveEquation(rel('=', F, c), v, { steps: true });
                    if (e.kind !== 'roots' || e.families?.length || e.roots.some((x) => x.approxOnly)) return null;
                    r = { set: IntervalSet.points(e.roots.map((x) => x.node)), steps: e.steps.slice(0, -1) };
                } else r = sub(F, o, c);
                if (!r.set) return null;
                piece = piece.intersect(r.set);
                backSteps.push(S(byLang((l) => `$${tex(F, l)} ${OP_TEX[o]} ${tex(c, l)}$`), { tex: byLang((l) => `${v} \\in ${intervalTex(r.set, l)}`), sub: r.steps }));
            }
            back = back.union(piece);
        }
        steps.push(S(T(`Возвращаемся к $${v}$`, `Back to $${v}$`), { tex: byLang((l) => `${v} \\in ${intervalTex(back, l)}`), sub: backSteps }));
        res = { set: back, steps: [] };
    } else return null;
    if (!res.set) return null;
    steps.push(...res.steps);
    const set = res.set.intersect(odz);
    steps.push(S(T('Учитываем ОДЗ', 'Take the domain into account'), { tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    return { set, steps, chart: res.chart, type: 'logarithmic' };
}

/** The domain of a node in v as an IntervalSet (trigonometric conditions are not handled) → {D, odz} or null. */
function domainOf(node, v, ctx = { v, domain: 'real', depth: 0 }) {
    const conds = collectConds(node, v);
    if (conds.some((c) => c.kind === 'cos' || c.kind === 'sin')) return null;
    const odz = conds.length ? odzInfo(conds, v) : null;
    // conditions that are not rational (√x ≠ 0, ln x ≠ 0) are solved here one by one
    let D = IntervalSet.all();
    for (const c of conds) {
        let cs = signSet(c.expr, OP_OF[c.kind], v);
        if (!cs && c.kind === 'ne0') {
            const e = solveEquation(rel('=', c.expr, N0), v, { steps: false });
            if (e.kind === 'none') cs = IntervalSet.all();
            else if (e.kind === 'roots' && !e.families?.length && !e.roots.some((x) => x.approxOnly)) cs = IntervalSet.all().minus(IntervalSet.points(e.roots.map((x) => x.node)));
        } else if (!cs) cs = ineqCore(c.expr, OP_OF[c.kind], N0, { ...ctx, v, depth: (ctx.depth ?? 0) + 1 }).set;
        if (!cs) return null;
        D = D.intersect(cs);
    }
    return { D, odz };
}

/** The set where a function of one variable is defined (null when it cannot be found exactly). */
export function domainSet(input, v = 'x') {
    const node = typeof input === 'string' ? parse(input) : input;
    return domainOf(node, v)?.D ?? null;
}

/**
 * The generalised method of intervals: f(x) = lhs − rhs is continuous on the domain, so its sign can change only at
 * its zeros and at the ends of the domain. The zeros come from solveEquation (exact, finite); the sign on every
 * interval is checked at several points, and any disagreement (a zero the equation solver missed) refuses.
 */
function rootsIneq(lhs, op, rhs, E, ctx) {
    const v = ctx.v;
    const JUMPY = new Set(['sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'floor', 'ceil', 'frac', 'sign', 'round', 'mod']);
    if (nodeSome(E, (n) => n.type === 'fn' && JUMPY.has(n.name))) return null;
    const node = rel(op, lhs, rhs);
    const dom = domainOf(node, v, ctx);
    if (!dom) return null;
    const { D, odz } = dom;
    const eq = solveEquation(rel('=', lhs, rhs), v, { steps: true });
    let roots;
    if (eq.kind === 'none') roots = [];
    else if (eq.kind === 'roots' && !eq.families?.length && !eq.roots.some((x) => x.approxOnly)) roots = eq.roots.map((x) => x.node).filter((x) => D.contains(x));
    else return null;
    const f = (x) => approxOf(E, { [v]: x });
    const ends = [];
    const addEnd = (n) => {
        const e = endOf(n);
        if (Number.isFinite(e.x) && !ends.some((o) => cmpEnd(o, e) === 0)) ends.push(e);
    };
    roots.forEach(addEnd);
    for (const p of D.parts) {
        if (p.lo) addEnd(p.lo.node);
        if (p.hi) addEnd(p.hi.node);
    }
    ends.sort((a, b) => cmpEnd(a, b));
    const good = (y) => (op === '>' ? y > 0 : op === '>=' ? y >= 0 : op === '<' ? y < 0 : y <= 0);
    const parts = [];
    const signs = [];
    for (let k = 0; k <= ends.length; k++) {
        const a = k > 0 ? ends[k - 1] : null;
        const b = k < ends.length ? ends[k] : null;
        let xs;
        if (a && b) xs = [1, 2, 3, 4, 5].map((j) => a.x + ((b.x - a.x) * j) / 6);
        else if (b) xs = [0.05, 0.5, 2, 10, 100].map((d) => b.x - d * (1 + Math.abs(b.x)));
        else if (a) xs = [0.05, 0.5, 2, 10, 100].map((d) => a.x + d * (1 + Math.abs(a.x)));
        else xs = [-100, -3, 0.5, 3, 100];
        const inside = xs.map((x) => D.contains(x));
        if (inside.every((z) => !z)) continue;
        if (!inside.every(Boolean)) return null;
        const ys = xs.map(f);
        if (ys.some((y) => Number.isNaN(y))) return null; // ±∞ from an overflow still has a sign
        const sg = ys.filter((y) => Math.abs(y) > 1e-12).map(Math.sign);
        if (!sg.length || sg.some((z) => z !== sg[0])) return null;
        signs.push({ a, b, sign: sg[0] });
        if (good(sg[0])) parts.push({ lo: a, hi: b, loC: false, hiC: false });
    }
    for (const e of ends) {
        if (!D.contains(e.node)) continue;
        const isRoot = roots.some((r) => cmpEnd(endOf(r), e) === 0);
        const y = isRoot ? 0 : f(e.x);
        if (Number.isFinite(y) && (isRoot ? !strictOf(op) : good(y))) parts.push({ lo: e, hi: e, loC: true, hiC: true });
    }
    const set = new IntervalSet(parts).intersect(D);
    const steps = [];
    // solveInequality shows the domain itself unless there are logarithms
    if (odz && (odz.partial || nodeSome(node, (n) => n.type === 'fn' && (n.name === 'log' || n.name === 'ln' || n.name === 'lg')))) {
        steps.push(S(T('Область допустимых значений (ОДЗ)', 'The domain (admissible values)'), { tex: byLang((l) => `${odz.conds.map((c) => condTex(c, l)).join(',\\ ')} \\;\\Rightarrow\\; ${v} \\in ${intervalTex(D, l)}`), text: odz.text }));
    }
    const fNode = isZeroNode(simpOr(rhs)) ? lhs : add(lhs, neg(rhs));
    steps.push(S(T('Обобщённый метод интервалов', 'The generalised method of intervals'), {
        tex: byLang((l) => `f(${v}) = ${tex(fNode, l)}`),
        text: T('Функция непрерывна на ОДЗ, поэтому знак она может сменить только в своих нулях и на границах ОДЗ.', 'The function is continuous on its domain, so it can change sign only at its zeros and at the ends of the domain.'),
    }));
    steps.push(S(T('Нули функции: решаем уравнение', 'The zeros: solve the equation'), { tex: eq.answer?.tex, sub: eq.steps.slice(0, -1) }));
    const ivTex = (s, l) => {
        const p = new IntervalSet([{ lo: s.a, hi: s.b, loC: false, hiC: false }]);
        return `${intervalTex(p, l)}\\!:\\ ${s.sign > 0 ? '+' : '-'}`;
    };
    steps.push(S(T('Знаки на промежутках', 'The signs on the intervals'), {
        tex: byLang((l) => signs.map((s) => ivTex(s, l)).join(';\\quad ')),
        text: T('Знак на каждом промежутке проверяем подстановкой точек из него.', 'The sign on each interval is checked by substituting points from it.'),
    }));
    const want = op === '>' || op === '>=' ? T('«+»', '“+”') : T('«−»', '“−”');
    steps.push(S(T(`Выбираем промежутки со знаком ${want.ru}`, `Take the intervals with ${want.en}`), { tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    return { set, steps, type: 'intervals' };
}

/**
 * Solve an inequality in one variable (also a double one: a < f(x) ≤ b).
 * → {set: IntervalSet | null, steps, signChart: {points: [{x, tex, kind: 'zero'|'pole', included, mult}], signs} | null,
 *    answer: {tex, text}, type, odz?, reason? (when unsupported), approx?}
 */
export function solveInequality(input, v = 'x', opts = {}) {
    const node = typeof input === 'string' ? parse(input, { vars: v && v.length > 1 ? [v] : [] }) : input;
    const withSteps = opts.steps !== false;
    const out = (r) => {
        const res = { set: null, steps: [], signChart: null, ...r, v };
        res.answer = res.set
            ? { tex: byLang((l) => `${v} \\in ${intervalTex(res.set, l)}`), text: byLang((l) => intervalText(res.set, l)) }
            : { tex: '', text: res.reason ?? T('Не удалось решить.', 'Could not solve.') };
        if (res.set) res.steps.push(S(T('Ответ', 'Answer'), { tex: res.answer.tex, final: true, text: res.approx ? T('Границы найдены приближённо.', 'The bounds are approximate.') : undefined }));
        else if (res.reason) res.steps.push(S(T('Не удалось решить', 'Could not solve'), { text: res.reason, final: true }));
        if (!withSteps) res.steps = [];
        return res;
    };
    if (node.type === 'chain') {
        v = pickVar(node, v);
        let set = IntervalSet.all();
        const steps = [S(T('Двойное неравенство — это система двух неравенств', 'A double inequality is a system of two inequalities'))];
        for (let k = 0; k < node.ops.length; k++) {
            const r = solveInequality(rel(node.ops[k], node.items[k], node.items[k + 1]), v, { steps: true });
            if (!r.set) return out({ reason: r.reason, steps });
            set = set.intersect(r.set);
            steps.push(S(byLang((l) => `$${tex(rel(node.ops[k], node.items[k], node.items[k + 1]), l)}$`), { tex: r.answer.tex, sub: r.steps.slice(0, -1) }));
        }
        steps.push(S(T('Пересекаем', 'Intersect'), { tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`) }));
        return out({ set, steps, type: 'double' });
    }
    if (node.type !== 'rel' || node.op === '=') return out({ reason: T('Нужно неравенство.', 'An inequality is needed.') });
    v = pickVar(node, v);
    const others = freeVars(node).filter((x) => x !== v);
    if (others.length) return out({ reason: T(`Кроме $${v}$ есть другие буквы (${others.join(', ')}) — неравенства с параметрами пока не поддерживаются.`, `Besides $${v}$ there are other letters (${others.join(', ')}); inequalities with parameters are not supported yet.`) });
    const ctx = { v, domain: 'real', depth: 0 };
    if (node.op === '!=') {
        const r = solveEquation(rel('=', node.lhs, node.rhs), v, { steps: true });
        const conds = collectConds(node, v);
        const dom = conds.length ? odzInfo(conds, v).set ?? IntervalSet.all() : IntervalSet.all();
        let set = null;
        if (r.kind === 'roots' && !r.families && !r.roots.some((x) => x.approxOnly)) set = dom.minus(IntervalSet.points(r.roots.map((x) => x.node)));
        else if (r.kind === 'none') set = dom;
        else if (r.kind === 'all' || r.kind === 'set') set = dom.minus(r.set ?? IntervalSet.all());
        if (!set) return out({ reason: T('Не удалось решить соответствующее уравнение точно.', 'Could not solve the corresponding equation exactly.') });
        return out({ set, steps: [S(T('Решаем уравнение и исключаем его корни', 'Solve the equation and exclude its roots'), { sub: r.steps, tex: r.answer.tex })], type: 'ne' });
    }
    const steps = [];
    const conds = collectConds(node, v).filter((c) => !(c.whys.size === 1 && c.whys.has('den')));
    let odz = null;
    if (conds.length && !nodeSome(node, (n) => n.type === 'fn' && (n.name === 'log' || n.name === 'ln' || n.name === 'lg'))) {
        odz = odzInfo(conds, v);
        steps.push(odz.step);
    }
    let core;
    try {
        core = ineqCore(node.lhs, node.op, node.rhs, ctx);
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        core = { set: null, steps: [], reason: e.msg };
    }
    steps.push(...core.steps);
    if (!core.set) return out({ steps, reason: core.reason ?? T('Такие неравенства решатель пока не решает.', 'This kind of inequality is not supported yet.') });
    let set = core.set;
    if (odz) {
        if (odz.set === null) return out({ steps, reason: T('Не удалось точно найти ОДЗ.', 'Could not find the domain exactly.') });
        const before = set;
        set = set.intersect(odz.set);
        if (!before.equals(set)) steps.push(S(T('Учитываем ОДЗ', 'Take the domain into account'), { tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`) }));
    }
    // denominators that cancelled during simplification still exclude their zeros
    const dens = collectConds(node, v).filter((c) => c.kind === 'ne0' || c.kind === 'gt0');
    for (const c of dens) {
        const ds = signSet(c.expr, OP_OF[c.kind], v);
        if (!ds) continue;
        const before = set;
        set = set.intersect(ds);
        if (!before.equals(set)) {
            steps.push(S(T(`Исключаем точки, где $${condTex(c, 'ru')}$ нарушается`, `Exclude the points where $${condTex(c, 'en')}$ fails`), {
                tex: byLang((l) => `${v} \\in ${intervalTex(set, l)}`),
                text: T('При упрощении дробь сократилась, но выражение в этих точках не определено.', 'The fraction cancelled while simplifying, but the expression is not defined at these points.'),
            }));
        }
    }
    return out({ set, steps, signChart: core.chart ?? null, type: core.type, odz: odz && { tex: odz.tex, text: odz.text, set: odz.set }, approx: !!core.approx });
}

// ---------------------------------------------------------------- systems of equations

const VAR_ORDER = ['x', 'y', 'z', 't', 'u', 'v', 'w'];

function sortVars(vs) {
    return [...vs].sort((a, b) => {
        const ia = VAR_ORDER.indexOf(a);
        const ib = VAR_ORDER.indexOf(b);
        if (ia >= 0 || ib >= 0) return (ia < 0 ? 99 : ia) - (ib < 0 ? 99 : ib);
        return a.localeCompare(b, 'en', { numeric: true });
    });
}

function relsOf(input, varsHint = []) {
    const long = varsHint.filter((x) => x.length > 1);
    const one = (x) => (typeof x === 'string' ? parse(x, { vars: long }) : x);
    const flat = (n) => (n.type === 'list' ? [...n.items] : [n]);
    if (Array.isArray(input)) return input.flatMap((x) => flat(one(x)));
    return flat(one(input));
}

/** Rows {a: Q[], b: Q} of a linear system (null for a non-linear equation). */
function linearRows(rels, vars) {
    return rels.map((r) => {
        if (r.type !== 'rel' || r.op !== '=') return null;
        const lf = linearForm(r, vars);
        return lf && { a: vars.map((x) => lf.coeffs[x]), b: lf.constant.neg() };
    });
}

function linEqNode(a, b, vars) {
    const terms = [];
    a.forEach((q, j) => {
        if (!q.isZero()) terms.push(monoNode(q, vars[j]));
    });
    return rel('=', sumNode(terms), num(b));
}

const casesTex = (lines) => (lines.length > 1 ? `\\begin{cases} ${lines.join(' \\\\ ')} \\end{cases}` : lines[0]);
const systemTexB = (rows, vars) => byLang((l) => casesTex(rows.map((r) => tex(linEqNode(r.a, r.b, vars), l))));
const tupleTex = (items, lang) => `\\left(${items.join(lang === 'ru' ? ';\\ ' : ',\\ ')}\\right)`;
const ORD = { ru: ['первого', 'второго', 'третьего'], en: ['first', 'second', 'third'] };
const ORD_ACC = { ru: ['первое', 'второе', 'третье'], en: ['first', 'second', 'third'] };

/** Substitute a solution into every equation → {ok, step}. */
function checkSystem(rels, sol) {
    const items = rels.map((r) => {
        const Ls = substitute(r.lhs, sol);
        const Rs = substitute(r.rhs, sol);
        const z = exactZero(add(Ls, neg(Rs)));
        const ok = z === true || (z === null && close(approxOf(Ls), approxOf(Rs), 1e-9));
        const tx = byLang((l) => {
            const lv = sideValue(Ls);
            const rv = sideValue(Rs);
            const left = [tex(Ls, l)];
            if (lv && tex(lv, l) !== left[0]) left.push(tex(lv, l));
            const rightT = rv ? tex(rv, l) : tex(Rs, l);
            const rConst = freeVars(r.rhs).length === 0;
            if (ok && rConst && left[left.length - 1] === rightT) return `${left.join(' = ')}\\ \\checkmark`;
            return `${left.join(' = ')} ${ok ? '=' : '\\ne'} ${rightT}${ok ? '\\ \\checkmark' : ''}`;
        });
        return { ok, tex: tx };
    });
    const ok = items.every((x) => x.ok);
    return {
        ok,
        items,
        step: S(T('Проверка', 'Check'), {
            tex: byLang((l) => (items.length > 1 ? `\\begin{aligned} ${items.map((x) => `& ${pick(x.tex, l)}`).join(' \\\\ ')} \\end{aligned}` : pick(items[0].tex, l))),
            text: ok ? T('Подставили найденные значения в каждое уравнение — все равенства верны.', 'We substituted the values into every equation: all of them hold.') : T('Не все равенства выполняются.', 'Not all the equalities hold.'),
        }),
    };
}

function sysSubstitution(rows, vars) {
    let best = null;
    for (let i = 0; i < 2; i++) {
        for (let j = 0; j < 2; j++) {
            const a = rows[i].a[j];
            if (a.isZero()) continue;
            const score = a.abs().isOne() ? 0 : a.isInt() ? Number(a.abs().n) : 1000;
            if (!best || score < best.score) best = { i, j, score };
        }
    }
    if (!best) return null;
    const { i, j } = best;
    const k = 1 - j;
    const o = 1 - i;
    const [vj, vk] = [vars[j], vars[k]];
    const aij = rows[i].a[j];
    const aik = rows[i].a[k];
    const Y = sym(vk);
    const numer = simpOr(add(num(rows[i].b), mul(num(aik.neg()), Y)));
    const shown = aij.isOne() ? numer : aij.eq(-1) ? simpOr(neg(numer)) : div(numer, num(aij));
    const expr = simpOr(shown);
    const steps = [];
    steps.push(S(T(`Выражаем $${vj}$ из ${ORD.ru[i]} уравнения`, `Express $${vj}$ from the ${ORD.en[i]} equation`), { tex: byLang((l) => `${vj} = ${tex(shown, l)}`) }));
    const aoj = rows[o].a[j];
    const aok = rows[o].a[k];
    const lhsNode = sumNode([aoj.isZero() ? null : aoj.isOne() ? shown : mul(num(aoj), shown), aok.isZero() ? null : monoNode(aok, vk)].filter(Boolean));
    steps.push(S(T(`Подставляем ${o === 1 ? 'во' : 'в'} ${ORD_ACC.ru[o]} уравнение`, `Substitute into the ${ORD_ACC.en[o]} equation`), {
        tex: byLang((l) => `${tex(lhsNode, l)} = ${tex(num(rows[o].b), l)}`),
        text: T(`Получилось уравнение с одной неизвестной $${vk}$.`, `This is an equation in one unknown, $${vk}$.`),
    }));
    const A = Poly.fromNode(lhsNode, vk);
    const B = new Poly([rows[o].b]);
    const sub = solveLinearSchool(lhsNode, num(rows[o].b), A, B, { v: vk, domain: 'real', depth: 1 });
    steps.push(S(byLang((l) => (l === 'ru' ? `Решаем его` : 'Solve it')), { tex: byLang((l) => (sub.kind === 'roots' ? rootsTex(sub.roots, vk, l) : sub.kind === 'all' ? (l === 'ru' ? '\\text{верно при любом } ' : '\\text{true for every } ') + vk : l === 'ru' ? '\\text{решений нет}' : '\\text{no solutions}')), sub: sub.steps }));
    if (sub.kind === 'none') {
        steps.push(S(T('Получилось неверное равенство — система решений не имеет', 'A false equality: the system has no solutions'), { text: T('Геометрически это две параллельные прямые.', 'Geometrically these are two parallel lines.') }));
        return { kind: 'none', steps };
    }
    if (sub.kind === 'all') {
        steps.push(S(T('Уравнение верно при любом значении — решений бесконечно много', 'The equation holds for any value: infinitely many solutions'), {
            tex: byLang((l) => `${vk} \\in \\mathbb{R},\\quad ${vj} = ${tex(expr, l)}`),
            text: T('Оба уравнения задают одну и ту же прямую.', 'Both equations describe the same line.'),
        }));
        return { kind: 'infinite', steps, general: { [vk]: Y, [vj]: expr }, params: [vk] };
    }
    const yk = sub.roots[0].node;
    const yj = simpOr(substitute(expr, { [vk]: yk }));
    steps.push(S(T(`Находим $${vj}$`, `Find $${vj}$`), { tex: byLang((l) => `${vj} = ${tex(substitute(shown, { [vk]: yk }), l)} = ${tex(yj, l)}`) }));
    return { kind: 'unique', steps, solution: { [vj]: yj, [vk]: yk } };
}

function sysAddition(rows0, vars) {
    const steps = [];
    let rows = rows0.map((r) => {
        let den = 1n;
        for (const q of [...r.a, r.b]) den = bigLcm(den, q.d);
        return den > 1n ? { a: r.a.map((q) => q.mul(new Q(den))), b: r.b.mul(new Q(den)), den } : { ...r, den: 1n };
    });
    if (rows.some((r) => r.den > 1n)) steps.push(S(T('Избавляемся от дробей', 'Clear the fractions'), { tex: systemTexB(rows, vars) }));
    let pickJ = -1;
    let bestL = null;
    for (let j = 0; j < 2; j++) {
        const [a0, a1] = [rows[0].a[j], rows[1].a[j]];
        if (a0.isZero() || a1.isZero()) continue;
        const L = bigLcm(a0.abs().n, a1.abs().n);
        const score = a0.add(a1).isZero() ? -2n : a0.eq(a1) ? -1n : L;
        if (bestL === null || score < bestL) {
            bestL = score;
            pickJ = j;
        }
    }
    if (pickJ < 0) return null;
    const j = pickJ;
    const k = 1 - j;
    const [a0, a1] = [rows[0].a[j], rows[1].a[j]];
    const L = bigLcm(a0.abs().n, a1.abs().n);
    const m0 = new Q(L / a0.abs().n);
    let m1 = new Q(L / a1.abs().n);
    if (a0.isNeg() === a1.isNeg()) m1 = m1.neg();
    const scaled = [{ a: rows[0].a.map((q) => q.mul(m0)), b: rows[0].b.mul(m0) }, { a: rows[1].a.map((q) => q.mul(m1)), b: rows[1].b.mul(m1) }];
    if (!m0.isOne() || !m1.isOne()) {
        const what = (m, idx, l) => (m.isOne() ? '' : l === 'ru' ? `${ORD_ACC.ru[idx]} уравнение умножаем на $${tex(num(m), l)}$` : `multiply the ${ORD_ACC.en[idx]} equation by $${tex(num(m), l)}$`);
        const parts = (l) => [what(m0, 0, l), what(m1, 1, l)].filter(Boolean).join(l === 'ru' ? ', ' : ' and ');
        steps.push(S(byLang((l) => {
            const p0 = parts(l);
            return l === 'ru' ? p0.charAt(0).toUpperCase() + p0.slice(1) : p0.charAt(0).toUpperCase() + p0.slice(1);
        }), {
            tex: systemTexB(scaled, vars),
            text: T(`Теперь коэффициенты при $${vars[j]}$ противоположны.`, `Now the coefficients of $${vars[j]}$ are opposite.`),
        }));
    }
    const c = scaled[0].a[k].add(scaled[1].a[k]);
    const d = scaled[0].b.add(scaled[1].b);
    steps.push(S(T(`Складываем уравнения: $${vars[j]}$ исчезает`, `Add the equations: $${vars[j]}$ cancels`), { tex: byLang((l) => `${tex(monoNode(c, vars[k]), l)} = ${tex(num(d), l)}`) }));
    if (c.isZero()) {
        if (d.isZero()) {
            const pr = rows0[0].a[j].isZero() ? rows0[1] : rows0[0];
            const expr = simpOr(div(add(num(pr.b), mul(num(pr.a[k].neg()), sym(vars[k]))), num(pr.a[j])));
            steps.push(S(T('Получилось $0 = 0$ — решений бесконечно много', 'We get $0 = 0$: infinitely many solutions'), {
                tex: byLang((l) => `${vars[k]} \\in \\mathbb{R},\\quad ${vars[j]} = ${tex(expr, l)}`),
                text: T('Уравнения задают одну и ту же прямую.', 'The equations describe the same line.'),
            }));
            return { kind: 'infinite', steps, general: { [vars[k]]: sym(vars[k]), [vars[j]]: expr }, params: [vars[k]] };
        }
        steps.push(S(T(`Получилось $0 = ${tex(num(d))}$ — решений нет`, `We get $0 = ${tex(num(d), 'en')}$: no solutions`), { text: T('Прямые параллельны и не пересекаются.', 'The lines are parallel and never meet.') }));
        return { kind: 'none', steps };
    }
    const yk = d.div(c);
    if (!c.isOne()) steps.push(S(T(`Находим $${vars[k]}$`, `Find $${vars[k]}$`), { tex: byLang((l) => `${vars[k]} = ${tex(num(yk), l)}`) }));
    const src = rows0[0].a[j].isZero() ? 1 : 0;
    const r = rows0[src];
    const yj = r.b.sub(r.a[k].mul(yk)).div(r.a[j]);
    const substituted = sumNode([monoNode(r.a[j], vars[j]), r.a[k].isZero() ? null : mul(num(r.a[k]), num(yk))].filter(Boolean));
    steps.push(S(T(`Подставляем $${vars[k]} = ${tex(num(yk))}$ в ${ORD_ACC.ru[src]} уравнение`, `Substitute $${vars[k]} = ${tex(num(yk), 'en')}$ into the ${ORD_ACC.en[src]} equation`), {
        tex: byLang((l) => `${tex(substituted, l)} = ${tex(num(r.b), l)} \\quad\\Rightarrow\\quad ${vars[j]} = ${tex(num(yj), l)}`),
    }));
    return { kind: 'unique', steps, solution: { [vars[j]]: num(yj), [vars[k]]: num(yk) } };
}

/** Replay the row operations of matSolve on the system and show it as equations after each one. */
function withSystems(steps, rows, vars) {
    const W = rows.map((r) => [...r.a, r.b]);
    return steps.map((st) => {
        if (!st.op) return st;
        if (st.op === 'swap') [W[st.i], W[st.j]] = [W[st.j], W[st.i]];
        else if (st.op === 'scale') W[st.i] = W[st.i].map((x) => x.mul(st.k));
        else if (st.op === 'add') W[st.i] = W[st.i].map((x, c) => x.add(st.k.mul(W[st.j][c])));
        const sys = byLang((l) => casesTex(W.map((r) => tex(linEqNode(r.slice(0, -1), r[r.length - 1], vars), l))));
        const t = st.tex;
        return { ...st, tex: byLang((l) => `\\begin{gathered} ${pick(t, l)} \\\\ \\Leftrightarrow\\ ${pick(sys, l)} \\end{gathered}`) };
    });
}

// text is always {ru, en} (a one-unknown answer reads the same in both languages, but callers pick text[lang])
const bothLang = (f) => ({ ru: f('ru'), en: f('en') });
function sysAnswer(res, vars) {
    if (res.kind === 'unique') {
        if (vars.length === 1) {
            const x = vars[0];
            return { tex: byLang((l) => `${x} = ${tex(res.solution[x], l)}`), text: bothLang((l) => `${x} = ${toText(res.solution[x], { lang: l })}`) };
        }
        return {
            tex: byLang((l) => `${tupleTex(vars, l)} = ${tupleTex(vars.map((x) => tex(res.solution[x], l)), l)}`),
            text: bothLang((l) => `(${vars.map((x) => toText(res.solution[x], { lang: l })).join(l === 'ru' ? '; ' : ', ')})`),
        };
    }
    if (res.kind === 'infinite') {
        const g = res.general;
        return {
            tex: byLang((l) => `${tupleTex(vars.map((x) => tex(g[x], l)), l)},\\quad ${res.params.join(',\\ ')} \\in \\mathbb{R}`),
            text: bothLang((l) => `(${vars.map((x) => toText(g[x], { lang: l })).join(l === 'ru' ? '; ' : ', ')}), ${res.params.join(', ')} ∈ R`),
        };
    }
    if (res.kind === 'none') return { tex: T('\\text{решений нет}', '\\text{no solutions}'), text: T('Решений нет.', 'No solutions.') };
    return { tex: '', text: res.reason ?? T('Не удалось решить.', 'Could not solve.') };
}

/**
 * A system of linear equations. rels: array of equations (text or rel nodes) or one text with ";" or newlines.
 * vars: the unknowns (default: the letters found, x, y, z first). opts: {steps, method: 'gauss' | 'substitution' |
 * 'addition' | 'cramer'} (default: substitution or addition for 2×2, Gauss otherwise).
 * → {kind: 'unique'|'none'|'infinite'|'unsupported', solution?: {x: node, …}, general?: {x: node in params},
 *    params?: [names], method, vars, steps, check, answer: {tex, text}, reason?}
 */
export function solveLinearSystem(input, vars = null, opts = {}) {
    const rels = relsOf(input, vars ?? []);
    const withSteps = opts.steps !== false;
    if (!vars) vars = sortVars(new Set(rels.flatMap((r) => freeVars(r))));
    const done = (res) => {
        const out = { vars, steps: [], check: [], ...res };
        out.answer = sysAnswer(out, vars);
        if (out.kind === 'unsupported') out.steps.push(S(T('Не удалось решить', 'Could not solve'), { text: out.reason, final: true }));
        else out.steps.push(S(T('Ответ', 'Answer'), { tex: out.answer.tex, final: true }));
        if (!withSteps) out.steps = [];
        return out;
    };
    if (!rels.length || !vars.length) return done({ kind: 'unsupported', reason: T('Нет уравнений с неизвестными.', 'There are no equations with unknowns.') });
    const rows = linearRows(rels, vars);
    if (rows.some((r) => !r)) {
        const pair = rels.length === 2 && vars.length === 2 && rows.some(Boolean);
        return done({
            kind: 'unsupported',
            reason: pair
                ? T('Одно из уравнений не линейное — такую систему решают подстановкой: выражают неизвестную из линейного уравнения.', 'One of the equations is not linear: such a system is solved by substitution, expressing an unknown from the linear equation.')
                : T('Не все уравнения линейные, а метод Гаусса и формулы Крамера работают только для линейных систем.', 'Not all the equations are linear, and Gaussian elimination and Cramer’s rule work only for linear systems.'),
        });
    }
    const m = rows.length;
    const n = vars.length;
    let method = opts.method ?? (m === 2 && n === 2 ? (rows.some((r) => r.a.some((q) => q.abs().isOne())) ? 'substitution' : 'addition') : 'gauss');
    if ((method === 'substitution' || method === 'addition') && !(m === 2 && n === 2)) method = 'gauss';
    if (method === 'cramer' && (m !== n || n > 3)) method = 'gauss';
    const steps = [];
    const standard = rels.every((r) => r.rhs.type === 'num' && nodeKey(simpOr(r.lhs)) === nodeKey(simpOr(linEqNode(linearRows([r], vars)[0].a, Q.ZERO, vars).lhs)));
    if (!standard) steps.push(S(T('Приводим каждое уравнение к виду «неизвестные слева, число справа»', 'Bring each equation to the form "unknowns on the left, a number on the right"'), { tex: systemTexB(rows, vars) }));
    let res = null;
    if (method === 'substitution') res = sysSubstitution(rows, vars);
    else if (method === 'addition') res = sysAddition(rows, vars);
    else if (method === 'cramer') {
        const cr = matSolveCramer(Matrix.from(rows.map((r) => r.a)), rows.map((r) => r.b), { steps: true, vars });
        if (cr.kind === 'unique') res = { kind: 'unique', steps: cr.steps.filter((s) => s.rule !== 'answer').concat(cr.steps.filter((s) => s.rule === 'answer').map((s) => ({ ...s, title: T('Находим неизвестные', 'Find the unknowns') }))), solution: Object.fromEntries(vars.map((x, j) => [x, num(cr.x[j])])) };
        else {
            steps.push(...cr.steps);
            method = 'gauss';
        }
    }
    if (!res) {
        method = method === 'cramer' ? 'gauss' : method;
        let ms;
        try {
            ms = matSolve(Matrix.from(rows.map((r) => r.a)), rows.map((r) => r.b), { steps: true, vars });
        } catch (e) {
            if (!(e instanceof MathError)) throw e;
            return done({ kind: 'unsupported', reason: e.msg, method, steps });
        }
        const st = withSystems(ms.steps.filter((s) => s.rule !== 'check'), rows, vars);
        if (ms.kind === 'unique') res = { kind: 'unique', steps: st, solution: Object.fromEntries(vars.map((x, j) => [x, num(ms.x[j])])) };
        else if (ms.kind === 'none') res = { kind: 'none', steps: st };
        else {
            const general = {};
            vars.forEach((x, j) => {
                const p = ms.params.find((pp) => pp.index === j);
                general[x] = p ? sym(p.name) : simpOr(add(num(ms.x[j]), ...ms.params.map((pp, k) => mul(num(ms.basis[k][j]), sym(pp.name)))));
            });
            res = { kind: 'infinite', steps: st, general, params: ms.params.map((p) => p.name) };
        }
        method = 'gauss';
    }
    steps.push(...res.steps);
    const out = { ...res, steps, method };
    if (res.kind === 'unique') {
        const ch = checkSystem(rels, res.solution);
        steps.push(ch.step);
        out.check = ch.items.map((x) => ({ ok: x.ok, tex: x.tex }));
    }
    return done(out);
}

/**
 * A linear and a non-linear equation in two unknowns, by substitution: express one unknown from the
 * linear equation and substitute it into the other. → {kind: 'solutions'|'none'|'unsupported',
 * solutions: [{x: node, y: node}], steps, check, answer, reason?}
 */
export function solveSystem2(input, vars = null, opts = {}) {
    const rels = relsOf(input, vars ?? []);
    const withSteps = opts.steps !== false;
    if (!vars) vars = sortVars(new Set(rels.flatMap((r) => freeVars(r))));
    const done = (res) => {
        const out = { vars, steps: [], check: [], solutions: [], ...res };
        if (out.kind === 'solutions') {
            out.answer = {
                tex: byLang((l) => out.solutions.map((s) => tupleTex(vars.map((x) => tex(s[x], l)), l)).join(l === 'ru' ? ';\\quad ' : ',\\quad ')),
                text: byLang((l) => out.solutions.map((s) => `(${vars.map((x) => toText(s[x], { lang: l })).join(l === 'ru' ? '; ' : ', ')})`).join(l === 'ru' ? '; ' : ', ')),
            };
        } else if (out.kind === 'none') out.answer = { tex: T('\\text{решений нет}', '\\text{no solutions}'), text: T('Решений нет.', 'No solutions.') };
        else out.answer = { tex: '', text: out.reason };
        out.steps.push(out.kind === 'unsupported' ? S(T('Не удалось решить', 'Could not solve'), { text: out.reason, final: true }) : S(T('Ответ', 'Answer'), { tex: out.answer.tex, final: true }));
        if (!withSteps) out.steps = [];
        return out;
    };
    if (rels.length !== 2 || vars.length !== 2) return done({ kind: 'unsupported', reason: T('Нужны два уравнения с двумя неизвестными.', 'Two equations in two unknowns are needed.') });
    const rows = linearRows(rels, vars);
    if (rows.every(Boolean)) {
        const r = solveLinearSystem(rels, vars, opts);
        if (r.kind === 'unique') return done({ kind: 'solutions', solutions: [r.solution], steps: r.steps.slice(0, -1), check: r.check });
        if (r.kind === 'none') return done({ kind: 'none', steps: r.steps.slice(0, -1) });
        return done({ kind: 'unsupported', reason: T('Решений бесконечно много — это случай линейной системы.', 'Infinitely many solutions: see the linear system solver.'), steps: r.steps.slice(0, -1) });
    }
    const li = rows.findIndex(Boolean);
    if (li < 0) return done({ kind: 'unsupported', reason: T('Ни одно из уравнений не линейное — способ подстановки здесь не сработает.', 'Neither equation is linear, so substitution will not work here.') });
    const other = rels[1 - li];
    const row = rows[li];
    let j = row.a.findIndex((q) => q.abs().isOne());
    if (j < 0) j = row.a.findIndex((q) => !q.isZero());
    if (j < 0) return done({ kind: 'unsupported', reason: T('Линейное уравнение не содержит неизвестных.', 'The linear equation has no unknowns.') });
    const k = 1 - j;
    const [vj, vk] = [vars[j], vars[k]];
    const expr = simpOr(div(add(num(row.b), mul(num(row.a[k].neg()), sym(vk))), num(row.a[j])));
    const steps = [S(T(`Выражаем $${vj}$ из линейного уравнения`, `Express $${vj}$ from the linear equation`), { tex: byLang((l) => `${vj} = ${tex(expr, l)}`) })];
    const subst = rel('=', substitute(other.lhs, { [vj]: expr }), substitute(other.rhs, { [vj]: expr }));
    steps.push(S(T('Подставляем в другое уравнение', 'Substitute into the other equation'), { tex: byLang((l) => tex(subst, l)), text: T(`Осталась одна неизвестная — $${vk}$.`, `One unknown is left: $${vk}$.`) }));
    const r = solveEquation(subst, vk, { steps: true });
    steps.push(S(byLang((l) => (l === 'ru' ? `Решаем уравнение относительно $${vk}$` : `Solve for $${vk}$`)), { tex: r.answer.tex, sub: r.steps.slice(0, -1) }));
    if (r.kind === 'none') return done({ kind: 'none', steps });
    if (r.kind !== 'roots' || r.families || r.roots.some((x) => x.approxOnly)) {
        return done({ kind: 'unsupported', steps, reason: r.reason ?? T('Не удалось найти точные корни уравнения с одной неизвестной.', 'Could not find exact roots of the equation in one unknown.') });
    }
    const solutions = r.roots.map((x) => ({ [vk]: x.node, [vj]: simpOr(substitute(expr, { [vk]: x.node })) }))
        .sort((a, b) => approxOf(a[vars[0]]) - approxOf(b[vars[0]]) || approxOf(a[vars[1]]) - approxOf(b[vars[1]]));
    steps.push(S(T(`Находим $${vj}$ для каждого корня`, `Find $${vj}$ for each root`), {
        tex: byLang((l) => solutions.map((s) => `${vk} = ${tex(s[vk], l)}:\\ ${vj} = ${tex(s[vj], l)}`).join(l === 'ru' ? ';\\quad ' : ',\\quad ')),
    }));
    const check = [];
    const good = [];
    for (const s of solutions) {
        const ch = checkSystem(rels, s);
        check.push({ solution: s, ok: ch.ok, items: ch.items });
        if (ch.ok) good.push(s);
        steps.push(S(byLang((l) => (l === 'ru' ? 'Проверка ' : 'Check ') + `$${tupleTex(vars.map((x) => tex(s[x], l)), l)}$`), { tex: ch.step.tex, text: ch.step.text }));
    }
    return done({ kind: good.length ? 'solutions' : 'none', solutions: good, steps, check });
}
