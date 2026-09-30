// series — sums of series, finite and infinite, step by step.
//
//   sumSeries("sum(1/(k(k + 1)), k, 1, inf)") → {kind: 'value' | 'diverges' | 'approx' | 'unsupported', value, approx, type, steps, text}
//
// Finite: polynomial terms by Faulhaber's formulas (Σk, Σk², Σk³), geometric progressions, anything else term by
// term. Infinite: geometric and arithmetico-geometric (P(k)·qᵏ, deg P ≤ 2), telescoping rational terms (partial
// fractions with poles an integer apart), a table of classic sums (π²/6, ln 2, e, π/4, …) matched up to a factor
// and a shift of the start, the necessary condition (terms not tending to zero) and the harmonic comparison for
// divergence; otherwise a numeric estimate marked as approximate.
import { Q, MathError } from './rational.js';
import { num, sym, add, mul, div, neg, pow, fn, nodeKey, containsVar, substitute, numValue, freeVars } from './ast.js';
import { parse } from './parse.js';
import { toTex, toText } from './print.js';
import { simplify } from './simplify.js';
import { evaluate } from './evaluate.js';
import { L, step } from './steps.js';
import { Poly } from './poly.js';
import { limit } from './limit.js';
import { numDen } from './expand.js';

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
const tex = (n, l = 'ru') => toTex(n, { lang: l });
const bt = (f) => L(f('ru'), f('en'));
const N0 = num(0);
const N1 = num(1);
const INF = sym('inf');
const isInf = (n) => n.type === 'sym' && n.name === 'inf';

/* ------------------------------------------------------------------ input */

function splitTop(s) {
    const out = [];
    let depth = 0;
    let cur = '';
    for (const ch of s) {
        if (ch === '(' || ch === '[') depth++;
        if (ch === ')' || ch === ']') depth--;
        if (ch === ',' && depth === 0) {
            out.push(cur);
            cur = '';
        } else cur += ch;
    }
    out.push(cur);
    return out.map((x) => x.trim());
}
function readInput(input) {
    const s = String(input).trim();
    const m = s.match(/^(?:sum|Σ|сумма)\s*\(([\s\S]*)\)$/i);
    if (!m) throw new MathError(L('Запись: sum(член, k, начало, конец), конец может быть inf.', 'Write it as sum(term, k, start, end); the end may be inf.'));
    const parts = splitTop(m[1]);
    if (parts.length !== 4) throw new MathError(L('Нужно четыре части: sum(член, k, начало, конец).', 'Four parts are needed: sum(term, k, start, end).'));
    const k = parts[1];
    if (!/^[a-zA-Z]$/.test(k)) throw new MathError(L('Индекс суммирования — одна буква.', 'The index is a single letter.'));
    const term = parse(parts[0], { vars: [k] });
    const lo = simpO(parse(parts[2]));
    const hiText = parts[3].replace(/∞|infinity/i, 'inf');
    const hi = /^\+?inf$/.test(hiText) ? INF : simpO(parse(hiText));
    const others = freeVars(term).filter((x) => x !== k);
    if (others.length) throw new MathError(L(`Кроме ${k} в члене есть другие буквы (${others.join(', ')}).`, `Besides ${k} the term has other letters (${others.join(', ')}).`));
    if (!numValue(lo)?.isInt() || (!isInf(hi) && !numValue(hi)?.isInt())) throw new MathError(L('Границы суммирования — целые числа (конец может быть inf).', 'The bounds are integers (the end may be inf).'));
    return { term, k, lo: numValue(lo), hi: isInf(hi) ? null : numValue(hi) };
}

const sumTex = (term, k, lo, hi, l) => `\\sum_{${k}=${lo.toTex(l)}}^{${hi ? hi.toTex(l) : '\\infty'}} ${tex(term, l)}`;
const at = (term, k, v) => simpO(substitute(term, { [k]: num(v) }));

/* ------------------------------------------------------------------ finite */

// Σ_{k=1}^{n} k^m for m ≤ 3
const FAUL = [
    (n) => n,
    (n) => n.mul(n.add(Q.ONE)).div(new Q(2n)),
    (n) => n.mul(n.add(Q.ONE)).mul(n.mul(new Q(2n)).add(Q.ONE)).div(new Q(6n)),
    (n) => n.mul(n.add(Q.ONE)).div(new Q(2n)).pow(2),
];
const FAUL_TEX = ['\\sum_{k=1}^{n} 1 = n', '\\sum_{k=1}^{n} k = \\frac{n(n+1)}{2}', '\\sum_{k=1}^{n} k^2 = \\frac{n(n+1)(2n+1)}{6}', '\\sum_{k=1}^{n} k^3 = \\left(\\frac{n(n+1)}{2}\\right)^2'];

function finiteSum(term, k, lo, hi) {
    const steps = [];
    const P = Poly.fromNode(term, k);
    // Σ_{k=lo}^{hi} = Σ_{1}^{hi} − Σ_{1}^{lo−1}
    const S = (m, n) => (n.lt(Q.ONE) ? (n.isZero() || m > 0 ? Q.ZERO : null) : FAUL[m](n));
    if (P && P.degree <= 3 && lo.ge(Q.ZERO)) {
        let total = Q.ZERO;
        const used = [];
        for (let m = 0; m <= P.degree; m++) {
            const c = P.coeff(m);
            if (c.isZero()) continue;
            const a = S(m, hi);
            let b = S(m, lo.sub(Q.ONE));
            if (m === 0) b = lo.sub(Q.ONE); // Σ_{1}^{lo−1} 1 = lo − 1
            if (a === null || b === null) return null;
            total = total.add(c.mul(a.sub(b)));
            used.push(m);
        }
        if (P.degree === 1 && !P.coeff(1).isZero()) {
            const first = P.evalAt(lo);
            const last = P.evalAt(hi);
            const n = hi.sub(lo).add(Q.ONE);
            steps.push(step({
                title: L('Сумма арифметической прогрессии', 'The sum of an arithmetic progression'),
                tex: bt((l) => `S = \\frac{a_1 + a_n}{2}\\cdot n = \\frac{${first.toTex(l)} + ${last.toTex(l)}}{2}\\cdot ${n.toTex(l)} = ${total.toTex(l)}`),
                text: L(`Члены растут на одно и то же число, первый $${first.toTex('ru')}$, последний $${last.toTex('ru')}$, всего $${n.toTex('ru')}$.`, `The terms grow by the same step: the first is $${first.toTex('en')}$, the last $${last.toTex('en')}$, $${n.toTex('en')}$ in all.`),
            }));
        } else {
            steps.push(step({
                title: L('Формулы сумм степеней', 'The power-sum formulas'),
                tex: used.map((m) => FAUL_TEX[m]).join(',\\qquad '),
                text: L('Раскладываем член по степеням $k$ и суммируем каждую степень по формуле.', 'Split the term by powers of $k$ and sum each power by its formula.'),
            }));
            steps.push(step({ title: L('Подставляем границы', 'Substitute the bounds'), tex: bt((l) => `${sumTex(term, k, lo, hi, l)} = ${total.toTex(l)}`) }));
        }
        return { value: num(total), steps, type: P.degree === 1 ? 'arithmetic' : 'power-sums' };
    }
    const geo = geometricParts(term, k);
    if (geo) {
        const first = at(term, k, lo);
        const n = hi.sub(lo).add(Q.ONE);
        const value = simpO(div(mul(first, add(pow(geo.q, num(n)), num(-1))), add(geo.q, num(-1))));
        steps.push(step({
            title: L('Сумма геометрической прогрессии', 'The sum of a geometric progression'),
            tex: bt((l) => `S_n = b_1\\frac{q^n - 1}{q - 1} = ${tex(first, l)}\\cdot\\frac{${tex(geo.q, l)}^{${n.toTex(l)}} - 1}{${tex(geo.q, l)} - 1} = ${tex(value, l)}`),
            text: L(`Отношение соседних членов постоянно: $q = ${tex(geo.q)}$.`, `The ratio of neighbouring terms is constant: $q = ${tex(geo.q, 'en')}$.`),
        }));
        return { value, steps, type: 'geometric' };
    }
    const count = hi.sub(lo).add(Q.ONE);
    if (count.gt(new Q(2000n))) return null;
    let acc = N0;
    for (let i = lo; i.le(hi); i = i.add(Q.ONE)) acc = simpO(add(acc, at(term, k, i)));
    steps.push(step({ title: L('Складываем члены', 'Add the terms'), tex: bt((l) => `${sumTex(term, k, lo, hi, l)} = ${tex(acc, l)}`) }));
    return { value: acc, steps, type: 'direct' };
}

/* ------------------------------------------------------------------ geometric and arithmetico-geometric */

// c·qᵏ: the ratio t(k+1)/t(k) is a constant
function geometricParts(term, k) {
    const r = simpO(div(substitute(term, { [k]: add(sym(k), N1) }), term));
    if (containsVar(r, k)) return null;
    const qv = val(r);
    if (!Number.isFinite(qv) || qv === 0) return null;
    return { q: r, qv };
}
// P(k)·qᵏ with deg P ≤ 2 → {P (Poly), q (node), qv}
function arithGeoParts(term, k) {
    const fs = term.type === 'mul' ? term.args : term.type === 'div' ? null : [term];
    let expPart = null;
    let rest = [];
    const collect = (list) => {
        for (const f of list) {
            if (f.type === 'pow' && containsVar(f.exp, k) && !containsVar(f.base, k)) {
                if (expPart) return false;
                expPart = f;
            } else rest.push(f);
        }
        return true;
    };
    if (term.type === 'div') {
        // k/2^k → k·(1/2)^k
        if (!(term.den.type === 'pow' && containsVar(term.den.exp, k) && !containsVar(term.den.base, k))) return null;
        expPart = pow(div(N1, term.den.base), term.den.exp);
        rest = [term.num];
    } else if (!collect(fs)) return null;
    if (!expPart) return null;
    const P = Poly.fromNode(rest.length ? mul(rest) : N1, k);
    if (!P || P.degree > 2 || P.degree < 1) return null;
    // qᵏ with the exponent k + c
    const e = Poly.fromNode(expPart.exp, k);
    if (!e || e.degree !== 1 || !e.coeff(1).isOne()) return null;
    const q = simpO(expPart.base);
    const shift = simpO(pow(expPart.base, num(e.coeff(0))));
    return { P, q, qv: val(q), shift };
}

function geometricInfinite(term, k, lo) {
    const g = geometricParts(term, k);
    if (!g) return null;
    const first = at(term, k, lo);
    const steps = [];
    if (Math.abs(g.qv) >= 1) {
        steps.push(step({ title: L('Геометрический ряд расходится', 'The geometric series diverges'), tex: bt((l) => `q = ${tex(g.q, l)},\\quad |q| \\ge 1`), text: L('Члены не стремятся к нулю.', 'The terms do not tend to zero.') }));
        return { diverges: true, steps, type: 'geometric' };
    }
    const value = simpO(div(first, add(N1, neg(g.q))));
    steps.push(step({
        title: L('Геометрический ряд', 'A geometric series'),
        tex: bt((l) => `q = \\frac{a_{${k}+1}}{a_{${k}}} = ${tex(g.q, l)},\\quad |q| < 1`),
        text: L('Отношение соседних членов постоянно и по модулю меньше единицы — ряд сходится.', 'The ratio of neighbouring terms is constant and less than one in absolute value, so the series converges.'),
    }));
    steps.push(step({ title: L('Сумма бесконечно убывающей прогрессии', 'The sum of an infinite geometric progression'), tex: bt((l) => `S = \\frac{b_1}{1 - q} = \\frac{${tex(first, l)}}{1 - ${tex(g.q, l)}} = ${tex(value, l)}`) }));
    return { value, steps, type: 'geometric' };
}

// Σ_{k≥0} qᵏ = 1/(1−q), Σ k qᵏ = q/(1−q)², Σ k² qᵏ = q(1+q)/(1−q)³
function arithGeoInfinite(term, k, lo) {
    const g = arithGeoParts(term, k);
    if (!g || !(Math.abs(g.qv) < 1)) return null;
    const q = g.q;
    const one = add(N1, neg(q));
    const base = [div(N1, one), div(q, pow(one, num(2))), div(mul(q, add(N1, q)), pow(one, num(3)))];
    let total = N0;
    for (let m = 0; m <= g.P.degree; m++) {
        const c = g.P.coeff(m);
        if (!c.isZero()) total = add(total, mul(num(c), base[m]));
    }
    total = mul(g.shift, total);
    // the sum starts at 0: take away k = 0 … lo − 1 (or add them back for a negative start)
    let head = N0;
    for (let i = Q.ZERO; i.lt(lo); i = i.add(Q.ONE)) head = add(head, at(term, k, i));
    for (let i = lo; i.lt(Q.ZERO); i = i.add(Q.ONE)) head = add(head, neg(at(term, k, i)));
    const value = simpO(add(total, neg(head)));
    const steps = [
        step({
            title: L('Арифметико-геометрический ряд', 'An arithmetico-geometric series'),
            tex: L(`\\sum_{k=0}^{\\infty} q^k = \\frac{1}{1-q},\\quad \\sum_{k=0}^{\\infty} k q^k = \\frac{q}{(1-q)^2},\\quad \\sum_{k=0}^{\\infty} k^2 q^k = \\frac{q(1+q)}{(1-q)^3}`),
            text: L(`Член — многочлен от $k$, умноженный на $q^k$ с $q = ${tex(q)}$, $|q| < 1$. Формулы получаются дифференцированием суммы геометрической прогрессии по $q$.`, `The term is a polynomial in $k$ times $q^k$ with $q = ${tex(q, 'en')}$, $|q| < 1$. The formulas come from differentiating the geometric sum in $q$.`),
        }),
        step({ title: L('Подставляем', 'Substitute'), tex: bt((l) => `${sumTex(term, k, lo, null, l)} = ${tex(value, l)}`) }),
    ];
    return { value, steps, type: 'arithmetico-geometric' };
}

/* ------------------------------------------------------------------ telescoping */

function telescoping(term, k, lo) {
    let N;
    let D;
    try {
        const nd = numDen(simpO(term));
        if (!nd) return null;
        N = Poly.fromNode(nd.num, k);
        D = Poly.fromNode(nd.den, k);
    } catch {
        return null;
    }
    if (!N || !D || D.degree < 2 || N.degree > D.degree - 2) return null;
    const { constant, factors } = D.factor();
    if (factors.some((f) => f.poly.degree !== 1 || f.mult !== 1)) return null;
    const roots = factors.map((f) => f.poly.coeff(0).neg().div(f.poly.coeff(1)));
    // integer shifts from the largest root: 1/(k − r) = 1/(k + c + m) with c = −max r
    const rmax = roots.reduce((a, b) => (a.gt(b) ? a : b));
    const ms = roots.map((r) => rmax.sub(r));
    if (!ms.every((m) => m.isInt())) return null;
    if (lo.add(rmax.neg()).le(Q.ZERO)) return null; // a pole inside the range
    const Dd = D.derivative();
    const A = roots.map((r) => N.evalAt(r).div(Dd.evalAt(r)));
    const c = rmax.neg();
    // S = −Σ Aᵢ Σ_{j=0}^{mᵢ−1} 1/(lo + c + j)
    let S = Q.ZERO;
    A.forEach((a, i) => {
        for (let j = 0n; j < ms[i].n; j++) S = S.sub(a.div(lo.add(c).add(new Q(j))));
    });
    const K = sym(k);
    const pieces = A.map((a, i) => mul(num(a), div(N1, add(K, num(roots[i].neg())))));
    const decomposed = simpO(add(pieces));
    const n = sym('n');
    // S_n = S + Σ Aᵢ Σ_{j=0}^{mᵢ−1} 1/(n + 1 + c + j)
    const tail = add(A.flatMap((a, i) => Array.from({ length: Number(ms[i].n) }, (_, j) => mul(num(a), div(N1, add(n, num(Q.ONE.add(c).add(new Q(BigInt(j))))))))));
    const Sn = simpO(add(num(S), tail));
    const steps = [
        step({ title: L('Раскладываем член на простейшие дроби', 'Split the term into partial fractions'), tex: bt((l) => `${tex(term, l)} = ${tex(decomposed, l)}`) }),
        step({
            title: L('Ряд телескопический', 'The series telescopes'),
            tex: bt((l) => `S_n = ${tex(Sn, l)}`),
            text: L('Слагаемые соседних членов взаимно уничтожаются; в частичной сумме остаются только первые и последние.', 'Pieces of neighbouring terms cancel; only the first and the last survive in a partial sum.'),
        }),
        step({ title: L('Переходим к пределу', 'Take the limit'), tex: bt((l) => `S = \\lim_{n\\to\\infty} S_n = ${S.toTex(l)}`) }),
    ];
    void constant;
    return { value: num(S), steps, type: 'telescoping' };
}

/* ------------------------------------------------------------------ a table of classic sums */

const TABLE = [
    { f: '1/k^2', s: 1, v: 'pi^2/6', name: L('Базельская задача (Эйлер)', 'The Basel problem (Euler)') },
    { f: '1/k^4', s: 1, v: 'pi^4/90', name: L('Сумма Эйлера', "Euler's sum") },
    { f: '(-1)^(k+1)/k', s: 1, v: 'ln(2)', name: L('Знакочередующийся гармонический ряд', 'The alternating harmonic series') },
    { f: '(-1)^k/(2k+1)', s: 0, v: 'pi/4', name: L('Ряд Лейбница', 'The Leibniz series') },
    { f: '1/k!', s: 0, v: 'e', name: L('Ряд для числа e', 'The series for e') },
    { f: '(-1)^k/k!', s: 0, v: '1/e', name: L('Ряд для 1/e', 'The series for 1/e') },
    { f: '(-1)^(k+1)/k^2', s: 1, v: 'pi^2/12', name: L('Знакочередующийся ряд обратных квадратов', 'The alternating series of inverse squares') },
    { f: '1/(2k-1)^2', s: 1, v: 'pi^2/8', name: L('Сумма обратных квадратов нечётных', 'Inverse squares of odd numbers') },
];

function tableSum(term, k, lo) {
    for (const row of TABLE) {
        const f = parse(row.f.replace(/k/g, k), { vars: [k] });
        // term = c·f(k) with a constant c
        const ks = [3, 4, 7, 10];
        const ratios = ks.map((x) => val(term, { [k]: x }) / val(f, { [k]: x }));
        if (!ratios.every((r) => Number.isFinite(r) && Math.abs(r - ratios[0]) < 1e-12 * Math.max(1, Math.abs(r)))) continue;
        const c = simpO(div(term, f));
        if (containsVar(c, k)) {
            const cq = Q.of(Math.round(ratios[0] * 1e6) / 1e6);
            if (Math.abs(cq.toNumber() - ratios[0]) > 1e-12) continue;
        }
        const coef = containsVar(c, k) ? num(Q.of(Math.round(ratios[0] * 1e6) / 1e6)) : c;
        const s = new Q(BigInt(row.s));
        let head = N0;
        for (let i = s; i.lt(lo); i = i.add(Q.ONE)) head = add(head, at(f, k, i));
        for (let i = lo; i.lt(s); i = i.add(Q.ONE)) head = add(head, neg(at(f, k, i)));
        const V = parse(row.v);
        const value = simpO(mul(coef, add(V, neg(head))));
        return {
            value,
            steps: [step({
                title: row.name,
                tex: bt((l) => `\\sum_{${k}=${row.s}}^{\\infty} ${tex(f, l)} = ${tex(V, l)}`),
                text: L('Классическая сумма; член отличается от табличного постоянным множителем или началом суммирования.', 'A classic sum; the term differs from the table one by a constant factor or the starting index.'),
            }), step({ title: L('Подставляем', 'Substitute'), tex: bt((l) => `${sumTex(term, k, lo, null, l)} = ${tex(value, l)}`) })],
            type: 'table',
        };
    }
    return null;
}

/* ------------------------------------------------------------------ divergence and numbers */

function divergence(term, k) {
    let lim = null;
    try {
        lim = limit(term, k, 'inf');
    } catch {
        lim = null;
    }
    const lv = lim && lim.value !== null && typeof lim.value === 'object' ? val(lim.value) : lim?.value === 'inf' || lim?.value === '-inf' ? Infinity : NaN;
    if (lim && (lim.value === 'dne' || (Number.isFinite(lv) && Math.abs(lv) > 1e-12) || lv === Infinity)) {
        return { diverges: true, type: 'necessary', steps: [step({ title: L('Необходимый признак не выполнен', 'The necessary condition fails'), tex: bt((l) => `\\lim_{${k}\\to\\infty} ${tex(term, l)} ${lim.value === 'dne' ? '\\text{ — не существует}' : `= ${typeof lim.value === 'object' ? tex(lim.value, l) : '\\infty'} \\ne 0`}`), text: L('Если ряд сходится, его члены стремятся к нулю. Здесь это не так — ряд расходится.', 'If a series converges, its terms tend to zero. They do not here, so the series diverges.') })] };
    }
    // rational term of degree −1 or more: comparison with the harmonic series
    try {
        const nd0 = numDen(simpO(term));
        const Np = nd0 && Poly.fromNode(nd0.num, k);
        const Dp = nd0 && Poly.fromNode(nd0.den, k);
        if (Np && Dp && Dp.degree - Np.degree === 1) {
            return { diverges: true, type: 'harmonic', steps: [step({ title: L('Сравнение с гармоническим рядом', 'Comparison with the harmonic series'), tex: bt((l) => `${tex(term, l)} \\sim \\frac{${Np.lead.div(Dp.lead).toTex(l)}}{${k}}`), text: L('Члены ведут себя как $c/k$, а гармонический ряд $\\sum 1/k$ расходится — значит, расходится и этот.', 'The terms behave like $c/k$, and the harmonic series $\\sum 1/k$ diverges, so this one diverges too.') })] };
        }
    } catch {
        /* not rational */
    }
    return null;
}

// |term| ~ c/k^p for large k: p from three far points (must agree), as a simple fraction; the sign must settle
function powerRate(term, k) {
    const ks = [1e3, 1e4, 1e5, 1e6];
    const ts = ks.map((x) => val(term, { [k]: x }));
    if (!ts.every((t) => Number.isFinite(t) && t !== 0)) return null;
    // one sign for all large k: neighbours too, not only these (even) points
    const signs = [...ks, 1e3 + 1, 1e4 + 1, 1e5 + 3, 1e5 + 7, 12345, 99999].map((x) => Math.sign(val(term, { [k]: x })));
    if (!signs.every((z) => z === signs[0])) return null;
    const ps = [0, 1, 2].map((i) => Math.log(Math.abs(ts[i] / ts[i + 1])) / Math.log(10));
    if (!ps.every((p) => Math.abs(p - ps[2]) < 0.02)) return null;
    for (let q = 1; q <= 6; q++) {
        const n = Math.round(ps[2] * q);
        if (Math.abs(n / q - ps[2]) < 0.005) return { p: new Q(BigInt(n), BigInt(q)), sign: Math.sign(ts[0]) };
    }
    return null;
}

function pSeries(term, k) {
    const r = powerRate(term, k);
    if (!r || r.p.gt(Q.ONE)) return null;
    const pT = r.p.toTex('ru');
    return {
        diverges: true,
        type: 'p-series',
        steps: [step({
            title: L('Сравнение с рядом $\\sum 1/k^p$', 'Comparison with $\\sum 1/k^p$'),
            tex: bt((l) => `${tex(term, l)} \\sim \\frac{c}{${k}^{${r.p.toTex(l)}}},\\quad p = ${r.p.toTex(l)} \\le 1`),
            text: L(`Члены одного знака и убывают как $1/k^{${pT}}$; ряд $\\sum 1/k^p$ сходится только при $p > 1$, поэтому этот ряд расходится.`, `The terms keep one sign and decay like $1/k^{${r.p.toTex('en')}}$; $\\sum 1/k^p$ converges only for $p > 1$, so this series diverges.`),
        })],
    };
}

/* ------------------------------------------------------------------ entry */

/** The sum of a series: sum(term, k, start, end) with end a number or inf. */
export function sumSeries(input, opts = {}) {
    let inp;
    try {
        inp = readInput(typeof input === 'object' && input?.task ? input.task : input);
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        return { kind: 'unsupported', reason: e.msg, steps: [] };
    }
    const { term, k, lo, hi } = inp;
    const head = step({ title: L('Сумма', 'The sum'), tex: bt((l) => sumTex(term, k, lo, hi, l)) });
    let r = null;
    try {
        if (hi) r = hi.lt(lo) ? { value: N0, steps: [step({ title: L('Пустая сумма', 'An empty sum'), text: L('Конец меньше начала — слагаемых нет.', 'The end is below the start: no terms.') })], type: 'empty' } : finiteSum(term, k, lo, hi);
        else r = geometricInfinite(term, k, lo) ?? arithGeoInfinite(term, k, lo) ?? telescoping(term, k, lo) ?? tableSum(term, k, lo) ?? divergence(term, k) ?? pSeries(term, k);
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        r = null;
    }
    if (r?.diverges) {
        const steps = [head, ...r.steps, step({ title: L('Ответ', 'Answer'), tex: L('\\text{ряд расходится}', '\\text{the series diverges}') })];
        steps[steps.length - 1].final = true;
        return { kind: 'diverges', value: null, type: r.type, steps, text: 'diverges' };
    }
    if (!r) {
        // a numeric estimate: partial sums with the average of two neighbours (alternating tails)
        if (hi) return { kind: 'unsupported', reason: L('Не удалось сложить.', 'Could not add it up.'), steps: [] };
        const T = (x) => val(term, { [k]: x });
        // strictly alternating signs over runs of neighbours, absolute values falling to zero: the Leibniz test
        const run = (K) => Array.from({ length: 12 }, (_, j) => T(K + j));
        const alternating = [1e3, 1e4, 1e5].every((K) => run(K).every((t, j, a) => j === 0 || Math.sign(t) === -Math.sign(a[j - 1])));
        const leibniz = alternating && Math.abs(T(1e4)) > Math.abs(T(1e5)) && Math.abs(T(1e5)) > Math.abs(T(1e6)) && Math.abs(T(1e6)) < 0.01;
        // an envelope max|t| over [K, 2K] that falls faster than 1/k^1.1: absolute convergence by comparison
        const env = (K) => Math.max(...Array.from({ length: 64 }, (_, j) => Math.abs(T(Math.round(K + (K * j) / 63)))));
        const pEnv = Math.log(env(1e3) / env(1e5)) / Math.log(100);
        const pEnv2 = Math.log(env(1e4) / env(1e5)) / Math.log(10);
        const rate = powerRate(term, k);
        const absolute = rate ? rate.p.gt(new Q(11n, 10n)) : Number.isFinite(pEnv) && pEnv > 1.1 && Math.abs(pEnv - pEnv2) < 0.15;
        if (!leibniz && !absolute) {
            return { kind: 'unsupported', reason: L('Не удалось ни найти сумму, ни доказать сходимость.', 'Could neither find the sum nor prove convergence.'), steps: [] };
        }
        let s = 0;
        let prev = 0;
        const Nmax = 200000;
        const last = Number(lo.n) + Nmax - 1;
        for (let i = Number(lo.n); i <= last; i++) {
            prev = s;
            s += val(term, { [k]: i });
        }
        // alternating: the mean of two neighbouring partial sums; one sign: the tail ∫ c/x^p ≈ t(N)(N + ½)/(p − 1)
        const est = leibniz ? (s + prev) / 2 : s + (rate ? (val(term, { [k]: last }) * (last + 0.5)) / (rate.p.toNumber() - 1) : 0);
        const digits = leibniz || rate ? 8 : 6;
        if (!Number.isFinite(est)) return { kind: 'unsupported', reason: L('Не удалось оценить сумму.', 'Could not estimate the sum.'), steps: [] };
        const why = leibniz
            ? L('Ряд знакочередующийся, модули членов убывают к нулю — по признаку Лейбница он сходится.', 'The series alternates and the absolute values of its terms decrease to zero, so it converges by the Leibniz test.')
            : rate
                ? L(`Члены одного знака и убывают как $1/k^{${rate.p.toTex('ru')}}$ с показателем больше 1 — ряд сходится (сравнение с $\\sum 1/k^p$).`, `The terms keep one sign and decay like $1/k^{${rate.p.toTex('en')}}$ with the power above 1, so the series converges (comparison with $\\sum 1/k^p$).`)
                : L('Модули членов не больше $c/k^p$ с $p > 1$ — ряд сходится абсолютно (сравнение с $\\sum 1/k^p$).', 'The absolute values of the terms are at most $c/k^p$ with $p > 1$, so the series converges absolutely (comparison with $\\sum 1/k^p$).');
        const steps = [head, step({ title: L('Сходимость', 'Convergence'), text: why }), step({ title: L('Численная оценка', 'A numeric estimate'), tex: `S \\approx ${est.toPrecision(digits)}`, text: L('Точную сумму в элементарных функциях найти не удалось; оценка по частичной сумме из 200 000 членов с поправкой на хвост.', 'No exact sum in elementary terms was found; the estimate is a partial sum of 200,000 terms with a tail correction.') })];
        steps[steps.length - 1].final = true;
        return { kind: 'approx', value: null, approx: est, steps, type: 'numeric', text: `≈ ${est.toPrecision(digits)}` };
    }
    const value = simpO(r.value);
    const steps = [head, ...r.steps, step({ title: L('Ответ', 'Answer'), tex: bt((l) => `${sumTex(term, k, lo, hi, l)} = ${tex(value, l)}`) })];
    steps[steps.length - 1].final = true;
    return { kind: 'value', value, approx: val(value), type: r.type, steps, text: toText(value, { lang: 'en' }) };
}
