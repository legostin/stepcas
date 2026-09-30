// solve/domain — the domain (ОДЗ): conditions of an expression, their solution, the ОДЗ step, trigonometric families
// against the domain.

import { containsVar, nodeKey, numValue, add, num, neg, nodeChildren, fn, substitute, rel, mul } from '../core/ast.js';
import { Q, MathError } from '../core/rational.js';
import { parse } from '../core/parse.js';
import { N0, S, approxC, approxNode, approxOf, approxShowComplex, approxShowNode, approxTex, close, exactZero, expd, simp, simpOr, termScale, tex } from './common.js';
import { IntervalSet, intervalTex } from './intervals.js';
import { complexApproxNode } from './polynomial.js';
import { approxComplexTex } from './roots.js';
import { signSet } from './signs.js';
import { ZZ, basicTrig, mergeFamilies, mkFamily, periodN, plusTex } from './trig.js';
import { msg, eachLanguage } from '../i18n/index.js';

// ---------------------------------------------------------------- ОДЗ (the domain of an equation)

// A condition: {kind: 'ne0' | 'ge0' | 'gt0' | 'cos' | 'sin', expr, why}; for 'cos'/'sin' expr is the argument u
// and the condition reads cos u ≠ 0 (tg, sec) or sin u ≠ 0 (ctg, cosec).
const RANK = { ne0: 1, ge0: 2, gt0: 3 };

export function collectConds(node, v) {
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

export function condTex(c, lang) {
    if (c.kind === 'cos' || c.kind === 'sin') return `${tex(fn(c.kind, c.expr), lang)} \\ne 0`;
    return `${tex(c.expr, lang)} ${COND_OP[c.kind]} 0`;
}

const WHY = {
    den: msg('solve.domain.denominator_is_not_zero'),
    root: msg('solve.domain.even_root_needs_non_negative_radicand'),
    log: msg('solve.domain.logarithm_needs_positive_argument'),
    logbase: msg('solve.domain.base_of_logarithm_is_positive_and'),
    powbase: msg('solve.domain.power_with_variable_exponent_needs_positive'),
    powfrac: msg('solve.domain.power_with_fractional_exponent_needs_non'),
    tan: msg('solve.domain.tangent_needs_non_zero_cosine'),
    cot: msg('solve.domain.cotangent_needs_non_zero_sine'),
    arc: msg('solve.domain.arcsin_and_arccos_need_argument_in'),
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
export function sideValue(node, complex = false) {
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

export function relHoldsNum(op, a, b) {
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
export function checkRel(r, v, root, opts = {}) {
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
    const texOut = eachLanguage(texL);
    const valTex = (lang) => (root.approxOnly
        ? `${v} \\approx ${typeof root.approx === 'number' ? approxTex(root.approx, lang) : approxComplexTex(root.approx, lang)}`
        : `${v} = ${tex(val, lang)}`);
    const text = ok
        ? msg('solve.domain.true_equality_root_fits')
        : reason === 'odz'
            ? msg('solve.domain.value_is_outside_domain_expression_makes')
            : reason === 'undefined'
                ? msg('solve.domain.expression_is_not_defined_at_this')
                : msg('solve.domain.equality_is_false_extraneous_root');
    const ineqText = r.op !== '=' ? (ok ? msg('solve.domain.inequality_holds') : msg('solve.domain.inequality_fails')) : text;
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
        steps: [S(msg('solve.domain.substitute', { p: (lng) => valTex(lng) }), { tex: texOut, text: ineqText })],
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
    if (r.type !== 'rel') throw new MathError(msg('solve.domain.equation_or_inequality_is_needed'), null, null, 'not-rel');
    if (typeof value === 'number' && Number.isFinite(value) && !Number.isInteger(value) && Number(value.toPrecision(12)) !== value) {
        // a double like 1.000000000272059 (a numeric root) is an approximation: checked numerically, shown rounded
        return checkRel(r, v, { node: approxNode(value, 16), approx: value, approxOnly: true }, opts);
    }
    const node = valueNodeOf(value, v);
    const approx = opts.complex ? approxC(node) : approxOf(node);
    return checkRel(r, v, { node, approx }, opts);
}

// ---------------------------------------------------------------- ОДЗ step

export const OP_OF = { ne0: '!=', ge0: '>=', gt0: '>' };

export function odzInfo(conds, v) {
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
    const tx = eachLanguage(texOf);
    const text = msg('solve.domain.conditions', { p: (lng) => whys.map((w) => WHY[w][lng]).join('; ') });
    return {
        conds,
        set: partial && set.isAll() ? null : set,
        partial,
        exclusions: excl,
        tex: tx,
        text,
        step: S(msg('solve.domain.domain_admissible_values'), { tex: tx, text }),
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

export function filterFamilies(fams, node, v, conds) {
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
