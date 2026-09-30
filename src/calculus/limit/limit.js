// limit/limit — the public API limit(): one-sided limits, the domain side, the steps and the check.

import { niceForm } from '../derivative/index.js';
import { nodeChildren, neg, num, add, mul, div, pow, fn, substitute, freeVars, mapNode, containsVar } from '../../core/ast.js';
import { evaluate } from '../../core/evaluate.js';
import { MathError } from '../../core/rational.js';
import { step } from '../../core/steps.js';
import { DNE, Split, T_, asNode, atPoint, bt, evalAt, fin, infV, isOneV, isZeroV, limTex, lt, makePoint, sideSignStrict, simp, trySimp, tx } from './common.js';
import { ev } from './evaluator.js';
import { FORM_NAME, FORM_TEX, plainNum, quotientParts } from './forms.js';
import { crossCheck, fmtNum, numericEstimate, tableFor, tableStep } from './table.js';

// ---------------------------------------------------------------- public API

function valueOut(L) {
    if (!L) return null;
    if (L.k === 'fin') return niceForm(L.node);
    if (L.k === 'inf') return L.s > 0 ? 'inf' : '-inf';
    if (L.k === 'dne' || L.k === 'bnd') return 'dne';
    return null;
}

function valueTex(val, L) {
    if (val === 'inf') return '+\\infty';
    if (val === '-inf') return '-\\infty';
    if (val === 'dne') return L === 'ru' ? '\\text{не существует}' : '\\text{does not exist}';
    if (val && typeof val === 'object') return tx(val, L);
    return '?';
}

/** Is f defined at x = a (no 0⁰, no division by zero, no ln 0 …)? */
function definedAt(f, v, x) {
    let ok = true;
    const walk = (n) => {
        if (!ok) return;
        if (n.type === 'pow') {
            const b = evalAt(n.base, v, x);
            const e = evalAt(n.exp, v, x);
            if (b === 0 && !(e > 0)) ok = false;
        }
        if (n.type === 'fn' && (n.name === 'tan' || n.name === 'sec') && Math.abs(Math.cos(evalAt(n.args[0], v, x))) < 1e-12) ok = false;
        if (n.type === 'fn' && (n.name === 'cot' || n.name === 'csc') && Math.abs(Math.sin(evalAt(n.args[0], v, x))) < 1e-12) ok = false;
        nodeChildren(n).forEach(walk);
    };
    walk(f);
    return ok && Number.isFinite(evalAt(f, v, x));
}

/** |u| and sgn u with u → 0 at the point: replace by ±u and ±1 using the sign of u on the side. */
function unfoldAbs(f, v, P) {
    if (!Number.isFinite(P.x)) return f;
    let changed = false;
    const g = mapNodeDeep(f, (m) => {
        if (m.type !== 'fn' || (m.name !== 'abs' && m.name !== 'sign')) return undefined;
        const u = m.args[0];
        const u0 = evalAt(u, v, P.x);
        if (!(Math.abs(u0) < 1e-12)) return undefined;
        const s = sideSignStrict(u, v, P);
        if (!s || Number.isNaN(s)) return undefined;
        changed = true;
        return m.name === 'abs' ? (s > 0 ? u : neg(u)) : num(s);
    });
    return changed ? trySimp(g) ?? f : f;
}

function mapNodeDeep(n, fnc) {
    const r = fnc(n);
    if (r !== undefined) return r;
    const kids = nodeChildren(n);
    if (!kids.length) return n;
    const nk = kids.map((c) => mapNodeDeep(c, fnc));
    if (nk.every((c, i) => c === kids[i])) return n;
    return rebuild(n, nk);
}

function rebuild(n, kids) {
    switch (n.type) {
        case 'add':
            return add(kids);
        case 'mul':
            return mul(kids);
        case 'div':
            return div(kids[0], kids[1]);
        case 'neg':
            return neg(kids[0]);
        case 'pow':
            return pow(kids[0], kids[1]);
        case 'fn':
            return fn(n.name, ...kids);
        default:
            return n;
    }
}

function oneSide(f0, v, P, opts) {
    void opts;
    const C = { v, P, depth: 0, log: [], methods: new Set(), active: new Set(), work: { n: 0 }, rounds: 0, root: null };
    let f = f0;
    // direct substitution (continuity)
    if (P.a && definedAt(f0, v, P.x)) {
        let val = null;
        try {
            const s = simp(substitute(f, { [v]: P.a }));
            const x = evaluate(s);
            if (Number.isFinite(x) && !freeVars(s).length) {
                // continuity check: the values next to the point must approach f(a)
                const sides = P.side === 'both' ? ['left', 'right'] : [P.side];
                const ok = sides.every((side) => {
                    const ys = [1e-6, 1e-8].map((h) => evalAt(f, v, atPoint({ ...P, side }, h)));
                    return ys.every((y) => Number.isFinite(y) && Math.abs(y - x) < 1e-4 * Math.max(1, Math.abs(x)));
                });
                if (ok) val = fin(s);
            }
        } catch {
            val = null;
        }
        if (val) return { L: val, C, method: 'substitution' };
    }
    f = unfoldAbs(f0, v, P);
    C.root = f;
    const L = ev(f, C);
    if (L && L.k === 'inf' && L.s === 0) throw new Split();
    return { L, C, method: C.methods.size ? [...C.methods][C.methods.size - 1] : L ? 'arithmetic' : null };
}

/**
 * Limit of node as v → a. a: node, number, string ('inf', '-inf', 'pi/2', …) or ±Infinity.
 * opts: {steps, side: 'both' | 'left' | 'right'}.
 * → {value: node | 'inf' | '-inf' | 'dne' | null, method, steps, table: [{x, fx, side}], verified,
 *    approx?: number (a numeric estimate when no symbolic method worked; value is null then),
 *    sides?: {left, right} (when a two-sided limit splits), tex}.
 */
// |u| where the sign of u has settled near the point — x → ±∞ or a one-sided approach — is ±u there
function settleAbs(f, v, P) {
    if (P.side === 'both' && Number.isFinite(P.x)) return f;
    const probes = Number.isFinite(P.x)
        ? [1e-3, 1e-4, 1e-6, 1e-8].map((h) => P.x + (P.side === 'left' ? -h : h) * Math.max(1, Math.abs(P.x)))
        : [1e3, 1e4, 1e5, 1e6, 1e8].map((t) => (P.x > 0 ? t : -t));
    let changed = false;
    const g = mapNode(f, (n) => {
        if (n.type !== 'fn' || n.name !== 'abs' || !containsVar(n.args[0], v)) return undefined;
        const signs = probes.map((x) => Math.sign(evalAt(n.args[0], v, x)));
        if (!signs.every((z) => z === signs[0]) || !(signs[0] === 1 || signs[0] === -1)) return undefined;
        changed = true;
        const inner = settleAbs(n.args[0], v, P);
        return signs[0] > 0 ? inner : neg(inner);
    });
    if (!changed) return f;
    try {
        return simp(g);
    } catch {
        return g;
    }
}

export function limit(node, v = 'x', a = 0, opts = {}) {
    node = asNode(node);
    if (node.type === 'rel' || node.type === 'list' || node.type === 'chain') throw new MathError({ ru: 'Нужна формула функции', en: 'A formula is needed' }, null, null, 'not-expr');
    const others = freeVars(node).filter((w) => w !== v);
    const side = opts.side ?? 'both';
    let P = makePoint(asNode(a), side);
    let f;
    try {
        f = simp(node);
    } catch {
        f = node;
    }
    // x·ln x at 0: the function lives only on one side of the point, so the limit is taken from that side
    let domainSide = null;
    if (P.side === 'both' && Number.isFinite(P.x) && !others.length) {
        const scale = Math.max(1, Math.abs(P.x));
        const lives = (dir) => [1e-3, 1e-5, 1e-7].some((h) => !Number.isNaN(evalAt(f, v, P.x + dir * h * scale)));
        const l = lives(-1), r = lives(1);
        if (l !== r) {
            domainSide = r ? 'right' : 'left';
            P = { ...P, side: domainSide };
        }
    }
    if (!others.length) f = settleAbs(f, v, P);
    const wantSteps = !!opts.steps;
    const steps = [];
    const table = others.length ? [] : tableFor(f, v, P);
    const head = (L) => `${limTex(P, v, L)} ${lt(node, L)}`;
    if (wantSteps) {
        steps.push(step({ title: T_('Что ищем', 'What we look for'), tex: bt(head), rule: 'start' }));
        if (domainSide) {
            steps.push(step({
                title: T_('Где определена функция', 'Where the function is defined'),
                text: domainSide === 'right'
                    ? T_(`Левее точки ${v} = ${plainNum(P)} функция не определена, поэтому к точке можно подойти только справа: предел — правосторонний.`, `Left of ${v} = ${plainNum(P)} the function is undefined, so the point can only be approached from the right: the limit is one-sided.`)
                    : T_(`Правее точки ${v} = ${plainNum(P)} функция не определена, поэтому к точке можно подойти только слева: предел — левосторонний.`, `Right of ${v} = ${plainNum(P)} the function is undefined, so the point can only be approached from the left: the limit is one-sided.`),
                rule: 'domain-side',
            }));
        }
    }
    let result;
    let sidesInfo = null;
    const run = (PP) => {
        try {
            return oneSide(f, v, PP, opts);
        } catch (e) {
            if (e instanceof Split) return { split: true };
            if (e instanceof MathError) return { L: null, C: { log: [], methods: new Set() } };
            throw e;
        }
    };
    result = run(P);
    if (result.split) {
        const l = run({ ...P, side: 'left' });
        const r = run({ ...P, side: 'right' });
        const vl = l.split ? null : l.L;
        const vr = r.split ? null : r.L;
        sidesInfo = { left: valueOut(vl), right: valueOut(vr) };
        const same = vl && vr && vl.k === vr.k && (vl.k !== 'fin' || Math.abs(vl.x - vr.x) < 1e-12) && (vl.k !== 'inf' || vl.s === vr.s);
        if (wantSteps) {
            steps.push(step({ title: T_('Предел слева', 'Limit from the left'), tex: bt((L) => `${limTex({ ...P, side: 'left' }, v, L)} ${tx(node, L)} = ${valueTex(sidesInfo.left, L)}`), rule: 'left', sub: l.C?.log ?? [] }));
            steps.push(step({ title: T_('Предел справа', 'Limit from the right'), tex: bt((L) => `${limTex({ ...P, side: 'right' }, v, L)} ${tx(node, L)} = ${valueTex(sidesInfo.right, L)}`), rule: 'right', sub: r.C?.log ?? [] }));
        }
        result = same ? { L: vl, C: l.C, method: l.method } : { L: vl && vr ? DNE : null, C: { log: [], methods: new Set() }, method: 'one-sided', splitDiffer: !!(vl && vr) };
    }
    let L = result.L;
    let method = result.method;
    let verified = false;
    let approx;
    // cross-check against the numbers
    if (L && !others.length && (L.k === 'fin' || L.k === 'inf')) {
        const sides = P.side === 'both' && Number.isFinite(P.x) ? ['left', 'right'] : [P.side];
        const checks = sides.map((s) => crossCheck(f, v, { ...P, side: s }, L));
        const usable = sides.filter((s) => numericEstimate(f, v, { ...P, side: s }) || tableFor(f, v, { ...P, side: s }).some((r) => Number.isFinite(r.fx)));
        if (checks.includes('contradict')) {
            L = null;
            method = null;
        } else verified = checks.includes('agree') || !usable.length;
    }
    if (L && (L.k === 'dne' || L.k === 'bnd') && !others.length) verified = true;
    if (!L && !others.length) {
        // numeric fallback
        const sides = P.side === 'both' && Number.isFinite(P.x) ? ['left', 'right'] : [P.side];
        const ests = sides.map((s) => numericEstimate(f, v, { ...P, side: s }));
        if (ests.every(Boolean)) {
            const [e1, e2] = ests;
            const agreeSides = !e2 || (e1.k === e2.k && (e1.k === 'inf' ? e1.s === e2.s : Math.abs(e1.x - e2.x) < 1e-3 * Math.max(1, Math.abs(e1.x))));
            if (!agreeSides) {
                L = DNE;
                method = 'numeric';
                sidesInfo = { left: e1.k === 'inf' ? (e1.s > 0 ? 'inf' : '-inf') : null, right: e2.k === 'inf' ? (e2.s > 0 ? 'inf' : '-inf') : null, leftApprox: e1.k === 'fin' ? e1.x : undefined, rightApprox: e2.k === 'fin' ? e2.x : undefined };
            } else if (e1.k === 'inf') {
                L = infV(e1.s);
                method = 'numeric';
            } else {
                approx = e1.x;
                method = 'numeric';
            }
        }
    }
    const value = approx !== undefined ? null : valueOut(L);
    if (value === null && approx === undefined) method = null;
    const tex = approx !== undefined
        ? bt((Lg) => `${head(Lg)} \\approx ${fmtNum(approx, Lg)}`)
        : value !== null
            ? bt((Lg) => `${head(Lg)} = ${valueTex(value, Lg)}`)
            : null;
    if (wantSteps) {
        if (method === 'substitution') {
            steps.push(step({
                title: T_('Подставляем', 'Substitute'),
                tex: bt((Lg) => `${head(Lg)} = ${valueTex(value, Lg)}`),
                text: T_(`Функция определена и непрерывна в точке ${v} = ${plainNum(P)}, поэтому предел равен её значению в этой точке.`, `The function is defined and continuous at ${v} = ${plainNum(P)}, so the limit is its value there.`),
                rule: 'substitution',
            }));
        } else if (result.C && result.C.log && !result.split) {
            const form = firstForm(f, v, P);
            if (form) {
                steps.push(step({
                    title: T_('Определяем вид неопределённости', 'Identify the indeterminate form'),
                    tex: bt((Lg) => `${head(Lg)} = \\left[${FORM_TEX[form]}\\right]`),
                    text: T_(`Подстановка даёт неопределённость ${FORM_NAME[form]}: сразу ответ не получить, выражение нужно преобразовать.`, `Substitution gives the indeterminate form ${FORM_NAME[form]}: the expression has to be transformed first.`),
                    rule: 'form',
                }));
            }
            steps.push(...result.C.log);
        }
        if (result.splitDiffer || (L && L.k === 'dne')) {
            steps.push(step({
                title: T_('Предела нет', 'No limit'),
                text: sidesInfo
                    ? T_('Пределы слева и справа различаются, поэтому (двусторонний) предел не существует.', 'The limits from the left and from the right differ, so the (two-sided) limit does not exist.')
                    : T_('Функция колеблется и не приближается ни к какому числу, поэтому предела нет.', 'The function oscillates and approaches no number, so there is no limit.'),
                rule: 'dne',
            }));
        }
        if (table.length) steps.push(tableStep(table, v, P, f));
        if (approx !== undefined) {
            steps.push(step({
                title: T_('Численная оценка', 'Numeric estimate'),
                text: T_('Точными методами предел найти не удалось; по таблице значений он примерно равен указанному числу. Это приближение, а не доказательство.', 'The exact methods did not work; judging by the table of values the limit is approximately this number. It is an estimate, not a proof.'),
                rule: 'numeric',
            }));
        }
        if (tex) {
            const s = step({ title: approx !== undefined ? T_('Ответ (приближённо)', 'Answer (approximate)') : T_('Ответ', 'Answer'), tex, rule: 'answer' });
            s.final = true;
            steps.push(s);
        } else {
            steps.push(step({ title: T_('Не получилось', 'Not found'), text: T_('Найти этот предел не удалось ни точными методами, ни по таблице значений.', 'This limit could not be found either exactly or from a table of values.'), rule: 'fail' }));
        }
    }
    const out = { value, method, steps, table, verified, tex };
    if (approx !== undefined) out.approx = approx;
    if (sidesInfo) out.sides = sidesInfo;
    if (domainSide) out.domainSide = domainSide;
    return out;
}

function firstForm(f, v, P) {
    // the form of the top-level expression after naive substitution (for the explanation)
    const C = { v, P, depth: 99, log: [], methods: new Set(), active: new Set(), work: { n: 0 }, rounds: 0 };
    const S = trySimp(f) ?? f;
    try {
        if (S.type === 'add') {
            const vals = S.args.map((t) => ev(t, C));
            if (vals.some((x) => x && x.k === 'inf' && x.s > 0) && vals.some((x) => x && x.k === 'inf' && x.s < 0)) return 'inf-inf';
        }
        if (S.type === 'pow' && containsVar(S.exp, v) && containsVar(S.base, v)) {
            const B = ev(S.base, C);
            const Ex = ev(S.exp, C);
            if (isOneV(B) && Ex && Ex.k === 'inf') return '1^inf';
            if (isZeroV(B) && isZeroV(Ex)) return '0^0';
            if (B && B.k === 'inf' && isZeroV(Ex)) return 'inf^0';
        }
        const q = quotientParts(S, v);
        if (q) {
            const U = ev(q.u, C);
            const W = ev(q.w, C);
            if (isZeroV(U) && isZeroV(W)) return '0/0';
            if (U && W && U.k === 'inf' && W.k === 'inf') return 'inf/inf';
        }
        if (S.type === 'mul') {
            const vals = S.args.map((t) => ev(t, C));
            if (vals.some(isZeroV) && vals.some((x) => x && x.k === 'inf')) return '0*inf';
        }
    } catch {
        return null;
    }
    return null;
}
