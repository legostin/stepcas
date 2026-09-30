// solve/intervals — IntervalSet (unions of intervals with exact ends), printing and reading sets typed by people.

import { Q, MathError } from '../core/rational.js';
import { num, numValue, add, neg, nodeSome } from '../core/ast.js';
import { parse } from '../core/parse.js';
import { toText, plainText } from '../core/print.js';
import { approxNode, approxOf, exactZero, isConstNode, simp, tex } from './common.js';
import { msg, notation, DEFAULT_LANGUAGE, wordsPattern } from '../i18n/index.js';

// ---------------------------------------------------------------- IntervalSet

const INF_TEX = { lo: '-\\infty', hi: '+\\infty' };

/** Endpoint {node, x, q}: exact node, its double value and, when rational, its exact Q. */
export function endOf(v) {
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

export function cmpEnd(a, b) {
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

    toTex(lang = DEFAULT_LANGUAGE) {
        return intervalTex(this, lang);
    }

    toText(lang = DEFAULT_LANGUAGE) {
        return intervalText(this, lang);
    }

    toJSON() {
        return this.parts.map((p) => ({
            lo: p.lo === null ? '-inf' : plainText(p.lo.node),
            hi: p.hi === null ? '+inf' : plainText(p.hi.node),
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
export function intervalTex(set, lang = DEFAULT_LANGUAGE) {
    return setPieces(set, (e) => tex(e.node, lang, e.approx ? { decimals: true } : {}), INF_TEX, notation(lang).intervalTex, '\\varnothing', ' \\cup ', (s) => `\\{${s}\\}`);
}

/** Plain text of a set: (-∞; 2] ∪ (3; +∞) in RU, (-∞, 2] ∪ (3, +∞) in EN; ∅. */
export function intervalText(set, lang = DEFAULT_LANGUAGE) {
    return setPieces(set, (e) => (e.approx ? String(Number(e.x.toFixed(5))).replace('.', notation(lang).decimalText) : toText(e.node, { lang })), { lo: '-∞', hi: '+∞' }, notation(lang).listText, '∅', ' ∪ ', (s) => `{${s}}`);
}

// ---------------------------------------------------------------- reading sets typed by people

const SET_ERR = (text) => new MathError(msg('solve.intervals.could_not_read_set', { text }), 0, String(text).length, 'interval');
// built on use, so that languages registered later add their words
const infRe = () => new RegExp(`^([+-]?)\\s*(?:∞|${wordsPattern('infinity')})$`, 'i');

function readEnd(s, v) {
    const t = s.trim().replace(/[−–—]/g, '-');
    const m = infRe().exec(t);
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

// in a language with a decimal comma (Russian) a comma inside a number is not a separator
const commaIsDecimal = (lang) => notation(lang).decimalText === ',';

function splitPair(inner, lang) {
    if (inner.includes(';')) return inner.split(';');
    const commas = [...inner.matchAll(/,/g)].map((m) => m.index);
    if (commas.length === 1) return [inner.slice(0, commas[0]), inner.slice(commas[0] + 1)];
    if (/,\s/.test(inner)) {
        const k = inner.search(/,\s/);
        return [inner.slice(0, k), inner.slice(k + 1)];
    }
    if (!commaIsDecimal(lang) || commas.length !== 3) return inner.split(',');
    return [inner.slice(0, commas[1]), inner.slice(commas[1] + 1)]; // 1,5,2,5 in RU
}

export function relToSet(op, e) {
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
    if (new RegExp(`^(∅|ø|\\\\varnothing|\\\\emptyset|\\{\\s*\\}|${wordsPattern('none')})$`).test(low)) return IntervalSet.empty();
    if (new RegExp(`^(r|ℝ|(?:x\\s*[-—–]\\s*)?(?:${wordsPattern('all')})|\\(\\s*-\\s*∞\\s*[;,]\\s*\\+?\\s*∞\\s*\\))$`).test(low)) return IntervalSet.all();
    // {a; b; c}
    const br = /^\\?\{(.*?)\\?\}$/.exec(s);
    if (br) {
        const inner = br[1];
        const items = inner.includes(';') ? inner.split(';') : !commaIsDecimal(lang) || /,\s/.test(inner) ? inner.split(/,\s*/) : [inner];
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
export function parseIntervalSet(text, lang = DEFAULT_LANGUAGE, v = 'x') {
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
    s = s.replace(new RegExp(`\\s+(?:${wordsPattern('or')})\\s+`, 'gi'), ' ∪ ').replace(/([)\]}])\s*[Uu]\s*(?=[([{\\])/g, '$1 ∪ ');
    let pieces = s.split('∪');
    // "x < -1; x > 3" — alternatives written with a separator
    if (pieces.length === 1 && !/^[([{\\]/.test(s) && /[<>=]/.test(s)) {
        const alt = s.split(commaIsDecimal(lang) ? /;\s*/ : /[;,]\s*(?=[a-zA-Z\d(-])/);
        if (alt.length > 1 && alt.every((a) => new RegExp(`(^|[^a-zA-Z])${v}($|[^a-zA-Z])`).test(a))) pieces = alt;
    }
    let set = IntervalSet.empty();
    for (const p of pieces) set = set.union(readPiece(p, lang, v));
    return set;
}

/** Same set? a, b: IntervalSet or text (read with parseIntervalSet in `lang`). */
export function intervalEquals(a, b, lang = DEFAULT_LANGUAGE, tol = 1e-9) {
    try {
        const A = a instanceof IntervalSet ? a : parseIntervalSet(a, lang);
        const B = b instanceof IntervalSet ? b : parseIntervalSet(b, lang);
        return A.equals(B, tol);
    } catch {
        return false;
    }
}
