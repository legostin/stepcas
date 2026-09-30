// param — equations with a parameter: for which values of a does the equation have two roots, one root, …
//
//   solveWithParameter("x^2 - 2a x + 4 = 0", {param: 'a', want: 'two-roots'}) → {set, steps, answer, method}
//   want: 'two-roots' | 'one-root' | 'has-roots' | 'no-roots' | a number (exactly that many roots)
//
// A quadratic in x with coefficients depending on a goes the school way: the leading coefficient is zero (the
// equation is linear), otherwise the discriminant decides. Anything linear in a goes the graphical way: a = g(x),
// study g (domain, derivative, corners, limits at the ends) and count where the line y = a meets the graph.
import { Q, MathError } from './rational.js';
import { num, sym, add, mul, div, neg, pow, rel, nodeKey, containsVar, substitute, numValue, nodeSome, freeVars } from './ast.js';
import { parse } from './parse.js';
import { toTex, toText } from './print.js';
import { simplify } from './simplify.js';
import { evaluate } from './evaluate.js';
import { L, step } from './steps.js';
import { derivative } from './diff.js';
import { limit } from './limit.js';
import { solveEquation, solveInequality, IntervalSet, intervalTex, domainSet } from './solve.js';

const N0 = num(0);
const simpO = (n) => {
    try {
        return simplify(n);
    } catch {
        return n;
    }
};
const val = (n, env = {}) => {
    try {
        const x = evaluate(n, env);
        return typeof x === 'number' ? x : NaN;
    } catch {
        return NaN;
    }
};
const d = (n, v) => simpO(derivative(n, v).result);
const tex = (n, l = 'ru') => toTex(n, { lang: l });
const bt = (f) => L(f('ru'), f('en'));
const exactRoots = (r) => r && (r.kind === 'none' || (r.kind === 'roots' && !r.families?.length && !r.roots.some((z) => z.approxOnly)));
const rootNodes = (r) => (r.kind === 'none' ? [] : r.roots.map((z) => z.node));

const WANT = {
    'two-roots': { n: 2, ru: 'ровно два корня', en: 'exactly two roots' },
    'one-root': { n: 1, ru: 'ровно один корень', en: 'exactly one root' },
    'no-roots': { n: 0, ru: 'нет корней', en: 'no roots' },
    'has-roots': { min: 1, ru: 'есть хотя бы один корень', en: 'at least one root' },
};
function wantOf(w) {
    if (typeof w === 'number') {
        const m10 = w % 10;
        const m100 = w % 100;
        const word = m10 === 1 && m100 !== 11 ? 'корень' : m10 >= 2 && m10 <= 4 && (m100 < 12 || m100 > 14) ? 'корня' : 'корней';
        return { n: w, ru: `ровно ${w} ${word}`, en: `exactly ${w} root${w === 1 ? '' : 's'}` };
    }
    return WANT[w] ?? WANT['has-roots'];
}
const fits = (want, count) => (want.min !== undefined ? count >= want.min : count === want.n);

/* ------------------------------------------------------------------ the quadratic way */

function quadratic(E, x, a, want) {
    if (nodeSome(E, (n) => (n.type === 'fn' && containsVar(n, x)) || (n.type === 'div' && containsVar(n.den, x)) || (n.type === 'pow' && containsVar(n.base, x) && !numValue(n.exp)?.isInt()))) return null;
    const A = simpO(div(d(d(E, x), x), num(2)));
    if (containsVar(A, x)) return null;
    const B = simpO(substitute(d(E, x), { [x]: N0 }));
    const C = simpO(substitute(E, { [x]: N0 }));
    // E = Ax² + Bx + C identically
    const X = sym(x);
    const back = add(mul(A, pow(X, num(2))), mul(B, X), C);
    for (const [xv, av] of [[0.37, 1.3], [-1.2, 0.4], [2.1, -0.7]]) {
        if (Math.abs(val(E, { [x]: xv, [a]: av }) - val(back, { [x]: xv, [a]: av })) > 1e-9) return null;
    }
    if (!containsVar(A, a) && val(A) === 0) return null; // not a quadratic
    if (!containsVar(A, a) && !containsVar(B, a) && !containsVar(C, a)) return null;
    const steps = [];
    const count = new Map(); // key → {set, n}
    const addPiece = (set, n) => {
        const k = String(n);
        count.set(k, { set: (count.get(k)?.set ?? IntervalSet.empty()).union(set), n });
    };
    let zeroA = [];
    if (containsVar(A, a)) {
        const r = solveEquation(rel('=', A, N0), a, { steps: true });
        if (!exactRoots(r)) return null;
        zeroA = rootNodes(r);
        const lines = [];
        for (const a0 of zeroA) {
            const b0 = simpO(substitute(B, { [a]: a0 }));
            const c0 = simpO(substitute(C, { [a]: a0 }));
            const bz = Math.abs(val(b0)) < 1e-12;
            const cz = Math.abs(val(c0)) < 1e-12;
            const n = !bz ? 1 : cz ? Infinity : 0;
            addPiece(IntervalSet.point(a0), n);
            const lin = rel('=', add(mul(b0, X), c0), N0);
            lines.push(L(`$${a} = ${tex(a0)}$: $${tex(simpO(lin.lhs))} = 0$ — ${n === 1 ? 'один корень' : n === 0 ? 'корней нет' : 'любое $x$'}`, `$${a} = ${tex(a0, 'en')}$: $${tex(simpO(lin.lhs), 'en')} = 0$ — ${n === 1 ? 'one root' : n === 0 ? 'no roots' : 'every $x$'}`));
        }
        steps.push(step({
            title: L('Старший коэффициент равен нулю', 'The leading coefficient is zero'),
            tex: bt((l) => (A.type === 'sym' ? `${a} = ${zeroA.map((z) => tex(z, l)).join(',\\ ')}` : `${tex(A, l)} = 0 \\;\\Rightarrow\\; ${a} = ${zeroA.map((z) => tex(z, l)).join(',\\ ')}`)),
            text: L(`Тогда уравнение линейное. ${lines.map((z) => z.ru).join('; ')}.`, `Then the equation is linear. ${lines.map((z) => z.en).join('; ')}.`),
        }));
    }
    const notZero = IntervalSet.all().minus(IntervalSet.points(zeroA));
    const D = simpO(add(mul(B, B), neg(mul(num(4), A, C))));
    steps.push(step({
        title: zeroA.length ? L(`При $${tex(A)} \\ne 0$ — квадратное уравнение`, `For $${tex(A, 'en')} \\ne 0$ — a quadratic equation`) : L('Квадратное уравнение', 'A quadratic equation'),
        tex: bt((l) => `D = b^2 - 4ac = ${tex(D, l)}`),
        text: L('Два корня при $D > 0$, один при $D = 0$, ни одного при $D < 0$.', 'Two roots for $D > 0$, one for $D = 0$, none for $D < 0$.'),
    }));
    const pos = solveInequality(rel('>', D, N0), a, { steps: true });
    const zer = solveEquation(rel('=', D, N0), a, { steps: true });
    if (!pos.set || !exactRoots(zer)) return null;
    const zeroSet = IntervalSet.points(rootNodes(zer));
    addPiece(pos.set.intersect(notZero), 2);
    addPiece(zeroSet.intersect(notZero), 1);
    addPiece(IntervalSet.all().minus(pos.set).minus(zeroSet).intersect(notZero), 0);
    steps.push(step({ title: L('$D > 0$', '$D > 0$'), tex: bt((l) => `${a} \\in ${intervalTex(pos.set, l)}`), sub: pos.steps.slice(0, -1) }));
    steps.push(step({ title: L('$D = 0$', '$D = 0$'), tex: bt((l) => (zer.kind === 'none' ? '\\varnothing' : `${a} = ${rootNodes(zer).map((z) => tex(z, l)).join(',\\ ')}`)) }));
    return { count, steps, method: 'quadratic' };
}

/* ------------------------------------------------------------------ the graphical way */

function graphical(E, x, a, want) {
    const Qn = d(E, a);
    if (containsVar(Qn, a)) return null; // not linear in a
    const P = simpO(substitute(E, { [a]: N0 }));
    const g = simpO(neg(div(P, Qn)));
    const X = sym(x);
    const Dom = domainSet(E, x);
    if (!Dom) return null;
    // points where Q = 0: roots for every a when P = 0 there too, otherwise never
    const qz = containsVar(Qn, x) ? solveEquation(rel('=', Qn, N0), x, { steps: false }) : { kind: 'none', roots: [] };
    if (!exactRoots(qz)) return null;
    let always = 0;
    const holes = [];
    for (const z of rootNodes(qz)) {
        if (!Dom.contains(z)) continue;
        if (Math.abs(val(substitute(P, { [x]: z }))) < 1e-12) always += 1;
        holes.push(z);
    }
    const G = Dom.minus(IntervalSet.points(holes));
    const gDom = domainSet(g, x);
    const D = gDom ? G.intersect(gDom) : G;
    // breakpoints: critical points, corners, ends of the domain
    const g1 = d(g, x);
    const crit = solveEquation(rel('=', g1, N0), x, { steps: false });
    if (!(exactRoots(crit) || crit.kind === 'unsupported' || crit.kind === 'all')) return null;
    const pts = [];
    const push = (n) => {
        const v = val(n);
        if (Number.isFinite(v) && !pts.some((p) => Math.abs(p.x - v) < 1e-12)) pts.push({ node: simpO(n), x: v });
    };
    if (exactRoots(crit)) rootNodes(crit).filter((z) => D.contains(z)).forEach(push);
    // corners: zeros of |u| arguments
    const corners = [];
    const walk = (n) => {
        if (n.type === 'fn' && n.name === 'abs' && containsVar(n.args[0], x)) corners.push(n.args[0]);
        for (const k of Object.values(n)) {
            if (k && typeof k === 'object' && k.type) walk(k);
            if (Array.isArray(k)) k.forEach((c) => c && c.type && walk(c));
        }
    };
    walk(g);
    for (const u of corners) {
        const r = solveEquation(rel('=', u, N0), x, { steps: false });
        if (!exactRoots(r)) return null;
        rootNodes(r).filter((z) => D.contains(z)).forEach(push);
    }
    for (const p of D.parts) {
        if (p.lo) push(p.lo.node);
        if (p.hi) push(p.hi.node);
    }
    holes.forEach(push);
    pts.sort((u, v) => u.x - v.x);
    // pieces between neighbouring breakpoints that lie in the domain
    const pieces = [];
    const lim = (b, side) => {
        let r = null;
        try {
            r = limit(g, x, b, { side });
        } catch {
            r = null;
        }
        if (!r) return null;
        if (r.value === 'inf') return { inf: 1 };
        if (r.value === '-inf') return { inf: -1 };
        if (r.value && typeof r.value === 'object') return { node: simpO(r.value), x: val(r.value) };
        return null;
    };
    for (let i = 0; i <= pts.length; i++) {
        const lo = i > 0 ? pts[i - 1] : null;
        const hi = i < pts.length ? pts[i] : null;
        const xs = (lo && hi ? [1, 2, 3, 4, 5, 6, 7].map((j) => lo.x + ((hi.x - lo.x) * j) / 8) : hi ? [0.5, 1, 2, 5, 20, 100].map((t) => hi.x - t) : lo ? [0.5, 1, 2, 5, 20, 100].map((t) => lo.x + t) : [-50, -5, -1, 0.3, 1, 5, 50]).sort((u, v) => u - v);
        const inside = xs.map((t) => D.contains(t));
        if (inside.every((z) => !z)) continue;
        if (!inside.every(Boolean)) return null;
        const ys = xs.map((t) => val(g, { [x]: t }));
        if (!ys.every(Number.isFinite)) return null;
        const diffs = ys.slice(1).map((y, j) => y - ys[j]);
        const up = diffs.every((z) => z > 0);
        const down = diffs.every((z) => z < 0);
        if (!up && !down) {
            if (diffs.every((z) => Math.abs(z) < 1e-12)) return null; // constant piece: every a of that value
            return null;
        }
        const left = lo ? lim(lo.node, 'right') : lim(mul(num(-1), sym('inf')), 'both');
        const right = hi ? lim(hi.node, 'left') : lim(sym('inf'), 'both');
        if (!left || !right) return null;
        pieces.push({ lo, hi, left, right, up });
    }
    // the value at a breakpoint inside the domain
    const pointVals = pts.filter((p) => D.contains(p.node)).map((p) => ({ ...p, y: simpO(substitute(g, { [x]: p.node })) }));
    // levels where the count may change
    const levels = [];
    const addLevel = (n) => {
        const v = val(n);
        if (Number.isFinite(v) && !levels.some((z) => Math.abs(z.x - v) < 1e-12)) levels.push({ node: n, x: v });
    };
    for (const p of pieces) {
        if (p.left.node) addLevel(p.left.node);
        if (p.right.node) addLevel(p.right.node);
    }
    pointVals.forEach((p) => addLevel(p.y));
    levels.sort((u, v) => u.x - v.x);
    const inOpen = (p, y) => {
        const lv = p.left.inf ? p.left.inf * Infinity : p.left.x;
        const rv = p.right.inf ? p.right.inf * Infinity : p.right.x;
        const lo = Math.min(lv, rv);
        const hi = Math.max(lv, rv);
        return y > lo + 1e-12 && y < hi - 1e-12;
    };
    const countAt = (y) => always + pieces.filter((p) => inOpen(p, y)).length + pointVals.filter((p) => Math.abs(val(p.y) - y) < 1e-12).length;
    const count = new Map();
    const addPiece = (set, n) => {
        const k = String(n);
        count.set(k, { set: (count.get(k)?.set ?? IntervalSet.empty()).union(set), n });
    };
    for (let i = 0; i <= levels.length; i++) {
        const lo = i > 0 ? levels[i - 1] : null;
        const hi = i < levels.length ? levels[i] : null;
        const y = lo && hi ? (lo.x + hi.x) / 2 : hi ? hi.x - 1 - Math.abs(hi.x) : lo ? lo.x + 1 + Math.abs(lo.x) : 0;
        addPiece(IntervalSet.interval(lo ? lo.node : null, hi ? hi.node : null, false, false), countAt(y));
        if (hi) addPiece(IntervalSet.point(hi.node), countAt(hi.x));
    }
    // steps
    const steps = [];
    steps.push(step({
        title: L('Выражаем параметр', 'Express the parameter'),
        tex: bt((l) => `${a} = ${tex(g, l)}`),
        text: L(`Число корней равно числу точек пересечения горизонтальной прямой $y = ${a}$ с графиком $y = g(${x})$.`, `The number of roots is the number of points where the horizontal line $y = ${a}$ meets the graph $y = g(${x})$.`),
    }));
    if (holes.length) steps.push(step({ title: L('Исключённые точки', 'Excluded points'), tex: bt((l) => `${x} \\ne ${holes.map((h) => tex(h, l)).join(',\\ ')}`), text: always ? L('В этой точке уравнение верно при любом $a$.', 'Here the equation holds for every $a$.') : L('В этих точках при делении получился бы ноль в знаменателе, а исходное уравнение там не выполняется.', 'Dividing by zero would happen here, and the original equation does not hold there.') }));
    const endTex = (e, l) => (e.inf ? (e.inf > 0 ? '+\\infty' : '-\\infty') : tex(e.node, l));
    steps.push(step({
        title: L(`Исследуем $g(${x})$`, `Study $g(${x})$`),
        tex: bt((l) => pieces.map((p) => `${intervalTex(IntervalSet.interval(p.lo ? p.lo.node : null, p.hi ? p.hi.node : null), l)}\\!:\\ ${p.up ? '\\nearrow' : '\\searrow'}\\ ${endTex(p.left, l)} \\to ${endTex(p.right, l)}`).join(';\\quad ')),
        text: L(`Производная $g'(${x}) = ${tex(g1)}$; на каждом промежутке функция монотонна, на концах — значения и пределы.${pointVals.length ? ` Значения в точках: ${pointVals.map((p) => `$g(${tex(p.node)}) = ${tex(p.y)}$`).join(', ')}.` : ''}`,
            `The derivative is $g'(${x}) = ${tex(g1, 'en')}$; g is monotone on each interval, with the values and limits at the ends.${pointVals.length ? ` Values at the points: ${pointVals.map((p) => `$g(${tex(p.node, 'en')}) = ${tex(p.y, 'en')}$`).join(', ')}.` : ''}`),
    }));
    return { count, steps, method: 'graphical' };
}

/* ------------------------------------------------------------------ entry */

/** For which values of the parameter does the equation have the wanted number of roots? */
export function solveWithParameter(input, opts = {}) {
    const obj = typeof input === 'object' && input !== null && !input.type ? input : null;
    const text = obj ? obj.task : input;
    const a = opts.param ?? obj?.param ?? 'a';
    const x = opts.v ?? obj?.v ?? 'x';
    const want = wantOf(opts.want ?? obj?.want ?? 'has-roots');
    let node;
    try {
        node = typeof text === 'string' ? parse(text) : text;
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        return { kind: 'unsupported', reason: e.msg, steps: [] };
    }
    if (node.type !== 'rel' || node.op !== '=') return { kind: 'unsupported', reason: L('Нужно уравнение.', 'An equation is needed.'), steps: [] };
    const others = freeVars(node).filter((v) => v !== a && v !== x);
    if (others.length) return { kind: 'unsupported', reason: L(`Лишние буквы: ${others.join(', ')}.`, `Extra letters: ${others.join(', ')}.`), steps: [] };
    const E = simpO(add(node.lhs, neg(node.rhs)));
    let r = null;
    try {
        r = quadratic(E, x, a, want) ?? graphical(E, x, a, want);
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        r = null;
    }
    if (!r) return { kind: 'unsupported', reason: L('Такую задачу с параметром решатель пока не решает.', 'This parameter problem is not supported yet.'), steps: [] };
    let set = IntervalSet.empty();
    for (const { set: s, n } of r.count.values()) if (fits(want, n)) set = set.union(s);
    const summary = [...r.count.values()].filter((z) => !z.set.isEmpty()).sort((u, v) => u.n - v.n);
    const steps = [
        step({ title: L('Задача', 'The problem'), tex: bt((l) => tex(node, l)), text: L(`При каких $${a}$ у уравнения ${want.ru}?`, `For which $${a}$ does the equation have ${want.en}?`) }),
        ...r.steps,
        step({
            title: L('Число корней в зависимости от параметра', 'The number of roots against the parameter'),
            tex: bt((l) => summary.map((z) => `${a} \\in ${intervalTex(z.set, l)}\\!:\\ ${z.n === Infinity ? '\\infty' : z.n}`).join(';\\quad ')),
        }),
    ];
    const answerTex = bt((l) => `${a} \\in ${intervalTex(set, l)}`);
    steps.push(step({ title: L('Ответ', 'Answer'), tex: answerTex }));
    steps[steps.length - 1].final = true;
    return { kind: 'set', set, method: r.method, steps, answer: { tex: answerTex, text: bt((l) => set.toText(l)) }, text: set.toText('en') };
}
