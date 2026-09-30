// calculus/series — sums of series, finite and infinite, step by step.
//
//   sumSeries("sum(1/(k(k + 1)), k, 1, inf)") → {kind: 'value' | 'diverges' | 'approx' | 'unsupported', value, approx, type, steps, text}
//
// Finite: polynomial terms by Faulhaber's formulas (Σk, Σk², Σk³), geometric progressions, anything else term by
// term. Infinite: geometric and arithmetico-geometric (P(k)·qᵏ, deg P ≤ 2), telescoping rational terms (partial
// fractions with poles an integer apart), a table of classic sums (π²/6, ln 2, e, π/4, …) matched up to a factor
// and a shift of the start, the necessary condition (terms not tending to zero) and the harmonic comparison for
// divergence; otherwise a numeric estimate marked as approximate.
import { Q, MathError } from '../core/rational.js';
import { num, sym, add, mul, div, neg, pow, containsVar, substitute, numValue, freeVars } from '../core/ast.js';
import { parse } from '../core/parse.js';
import { toTex, plainText } from '../core/print.js';
import { step } from '../core/steps.js';
import { Poly } from '../core/poly.js';
import { limit } from './limit/index.js';
import { numDen } from '../core/fractions.js';
import { trySimplify, approx } from '../core/safe.js';
import { msg, eachLanguage, DEFAULT_LANGUAGE, wordsPattern } from '../i18n/index.js';
import { N0, N1 } from './display.js';

const tex = (n, l = DEFAULT_LANGUAGE) => toTex(n, { lang: l });
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
    const m = s.match(new RegExp(`^(?:Σ|${wordsPattern('sum')})\\s*\\(([\\s\\S]*)\\)$`, 'i'));
    if (!m) throw new MathError(msg('calculus.series.write_it_as_sum_term_k'));
    const parts = splitTop(m[1]);
    if (parts.length !== 4) throw new MathError(msg('calculus.series.four_parts_are_needed_sum_term'));
    const k = parts[1];
    if (!/^[a-zA-Z]$/.test(k)) throw new MathError(msg('calculus.series.index_is_single_letter'));
    const term = parse(parts[0], { vars: [k] });
    const lo = trySimplify(parse(parts[2]));
    const hiText = parts[3].replace(/∞|infinity/i, 'inf');
    const hi = /^\+?inf$/.test(hiText) ? INF : trySimplify(parse(hiText));
    const others = freeVars(term).filter((x) => x !== k);
    if (others.length) throw new MathError(msg('calculus.series.besides_term_has_other_letters', { k, p: others.join(', ') }));
    if (!numValue(lo)?.isInt() || (!isInf(hi) && !numValue(hi)?.isInt())) throw new MathError(msg('calculus.series.bounds_are_integers_end_may_be'));
    return { term, k, lo: numValue(lo), hi: isInf(hi) ? null : numValue(hi) };
}

const sumTex = (term, k, lo, hi, l) => `\\sum_{${k}=${lo.toTex(l)}}^{${hi ? hi.toTex(l) : '\\infty'}} ${tex(term, l)}`;
const at = (term, k, v) => trySimplify(substitute(term, { [k]: num(v) }));

/* ------------------------------------------------------------------ finite */

// Σ_{k=1}^{n} k^m for m ≤ 3
const FAUL = [
    (n) => n,
    (n) => n.mul(n.add(Q.ONE)).div(new Q(2n)),
    (n) =>
        n
            .mul(n.add(Q.ONE))
            .mul(n.mul(new Q(2n)).add(Q.ONE))
            .div(new Q(6n)),
    (n) => n.mul(n.add(Q.ONE)).div(new Q(2n)).pow(2),
];
const FAUL_TEX = [
    '\\sum_{k=1}^{n} 1 = n',
    '\\sum_{k=1}^{n} k = \\frac{n(n+1)}{2}',
    '\\sum_{k=1}^{n} k^2 = \\frac{n(n+1)(2n+1)}{6}',
    '\\sum_{k=1}^{n} k^3 = \\left(\\frac{n(n+1)}{2}\\right)^2',
];

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
            steps.push(
                step({
                    title: msg('calculus.series.sum_of_arithmetic_progression'),
                    tex: eachLanguage(
                        (l) => `S = \\frac{a_1 + a_n}{2}\\cdot n = \\frac{${first.toTex(l)} + ${last.toTex(l)}}{2}\\cdot ${n.toTex(l)} = ${total.toTex(l)}`,
                    ),
                    text: msg('calculus.series.terms_grow_by_same_step_first', {
                        p: (lng) => first.toTex(lng),
                        p2: (lng) => last.toTex(lng),
                        p3: (lng) => n.toTex(lng),
                    }),
                }),
            );
        } else {
            steps.push(
                step({
                    title: msg('calculus.series.power_sum_formulas'),
                    tex: used.map((m) => FAUL_TEX[m]).join(',\\qquad '),
                    text: msg('calculus.series.split_term_by_powers_of_and'),
                }),
            );
            steps.push(
                step({ title: msg('calculus.series.substitute_bounds'), tex: eachLanguage((l) => `${sumTex(term, k, lo, hi, l)} = ${total.toTex(l)}`) }),
            );
        }
        return { value: num(total), steps, type: P.degree === 1 ? 'arithmetic' : 'power-sums' };
    }
    const geo = geometricParts(term, k);
    if (geo) {
        const first = at(term, k, lo);
        const n = hi.sub(lo).add(Q.ONE);
        const value = trySimplify(div(mul(first, add(pow(geo.q, num(n)), num(-1))), add(geo.q, num(-1))));
        steps.push(
            step({
                title: msg('calculus.series.sum_of_geometric_progression'),
                tex: eachLanguage(
                    (l) =>
                        `S_n = b_1\\frac{q^n - 1}{q - 1} = ${tex(first, l)}\\cdot\\frac{${tex(geo.q, l)}^{${n.toTex(l)}} - 1}{${tex(geo.q, l)} - 1} = ${tex(value, l)}`,
                ),
                text: msg('calculus.series.ratio_of_neighbouring_terms_is_constant', { p: (lng) => tex(geo.q, lng) }),
            }),
        );
        return { value, steps, type: 'geometric' };
    }
    const count = hi.sub(lo).add(Q.ONE);
    if (count.gt(new Q(2000n))) return null;
    let acc = N0;
    for (let i = lo; i.le(hi); i = i.add(Q.ONE)) acc = trySimplify(add(acc, at(term, k, i)));
    steps.push(step({ title: msg('calculus.series.add_terms'), tex: eachLanguage((l) => `${sumTex(term, k, lo, hi, l)} = ${tex(acc, l)}`) }));
    return { value: acc, steps, type: 'direct' };
}

/* ------------------------------------------------------------------ geometric and arithmetico-geometric */

// c·qᵏ: the ratio t(k+1)/t(k) is a constant
function geometricParts(term, k) {
    const r = trySimplify(div(substitute(term, { [k]: add(sym(k), N1) }), term));
    if (containsVar(r, k)) return null;
    const qv = approx(r);
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
    const q = trySimplify(expPart.base);
    const shift = trySimplify(pow(expPart.base, num(e.coeff(0))));
    return { P, q, qv: approx(q), shift };
}

function geometricInfinite(term, k, lo) {
    const g = geometricParts(term, k);
    if (!g) return null;
    const first = at(term, k, lo);
    const steps = [];
    if (Math.abs(g.qv) >= 1) {
        steps.push(
            step({
                title: msg('calculus.series.geometric_series_diverges'),
                tex: eachLanguage((l) => `q = ${tex(g.q, l)},\\quad |q| \\ge 1`),
                text: msg('calculus.series.terms_do_not_tend_to_zero'),
            }),
        );
        return { diverges: true, steps, type: 'geometric' };
    }
    const value = trySimplify(div(first, add(N1, neg(g.q))));
    steps.push(
        step({
            title: msg('calculus.series.geometric_series'),
            tex: eachLanguage((l) => `q = \\frac{a_{${k}+1}}{a_{${k}}} = ${tex(g.q, l)},\\quad |q| < 1`),
            text: msg('calculus.series.ratio_of_neighbouring_terms_is_constant_2'),
        }),
    );
    steps.push(
        step({
            title: msg('calculus.series.sum_of_infinite_geometric_progression'),
            tex: eachLanguage((l) => `S = \\frac{b_1}{1 - q} = \\frac{${tex(first, l)}}{1 - ${tex(g.q, l)}} = ${tex(value, l)}`),
        }),
    );
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
    const value = trySimplify(add(total, neg(head)));
    const steps = [
        step({
            title: msg('calculus.series.arithmetico_geometric_series'),
            tex: `\\sum_{k=0}^{\\infty} q^k = \\frac{1}{1-q},\\quad \\sum_{k=0}^{\\infty} k q^k = \\frac{q}{(1-q)^2},\\quad \\sum_{k=0}^{\\infty} k^2 q^k = \\frac{q(1+q)}{(1-q)^3}`,
            text: msg('calculus.series.term_is_polynomial_in_times_with', { q: (lng) => tex(q, lng) }),
        }),
        step({ title: msg('calculus.series.substitute'), tex: eachLanguage((l) => `${sumTex(term, k, lo, null, l)} = ${tex(value, l)}`) }),
    ];
    return { value, steps, type: 'arithmetico-geometric' };
}

/* ------------------------------------------------------------------ telescoping */

function telescoping(term, k, lo) {
    let N;
    let D;
    try {
        const nd = numDen(trySimplify(term));
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
    const decomposed = trySimplify(add(pieces));
    const n = sym('n');
    // S_n = S + Σ Aᵢ Σ_{j=0}^{mᵢ−1} 1/(n + 1 + c + j)
    const tail = add(
        A.flatMap((a, i) => Array.from({ length: Number(ms[i].n) }, (_, j) => mul(num(a), div(N1, add(n, num(Q.ONE.add(c).add(new Q(BigInt(j))))))))),
    );
    const Sn = trySimplify(add(num(S), tail));
    const steps = [
        step({ title: msg('calculus.series.split_term_into_partial_fractions'), tex: eachLanguage((l) => `${tex(term, l)} = ${tex(decomposed, l)}`) }),
        step({
            title: msg('calculus.series.series_telescopes'),
            tex: eachLanguage((l) => `S_n = ${tex(Sn, l)}`),
            text: msg('calculus.series.pieces_of_neighbouring_terms_cancel_only'),
        }),
        step({ title: msg('calculus.series.take_limit'), tex: eachLanguage((l) => `S = \\lim_{n\\to\\infty} S_n = ${S.toTex(l)}`) }),
    ];
    void constant;
    return { value: num(S), steps, type: 'telescoping' };
}

/* ------------------------------------------------------------------ a table of classic sums */

const TABLE = [
    { f: '1/k^2', s: 1, v: 'pi^2/6', name: msg('calculus.series.basel_problem_euler') },
    { f: '1/k^4', s: 1, v: 'pi^4/90', name: msg('calculus.series.euler_s_sum') },
    { f: '(-1)^(k+1)/k', s: 1, v: 'ln(2)', name: msg('calculus.series.alternating_harmonic_series') },
    { f: '(-1)^k/(2k+1)', s: 0, v: 'pi/4', name: msg('calculus.series.leibniz_series') },
    { f: '1/k!', s: 0, v: 'e', name: msg('calculus.series.series_for_e') },
    { f: '(-1)^k/k!', s: 0, v: '1/e', name: msg('calculus.series.series_for_1_e') },
    { f: '(-1)^(k+1)/k^2', s: 1, v: 'pi^2/12', name: msg('calculus.series.alternating_series_of_inverse_squares') },
    { f: '1/(2k-1)^2', s: 1, v: 'pi^2/8', name: msg('calculus.series.inverse_squares_of_odd_numbers') },
];

function tableSum(term, k, lo) {
    for (const row of TABLE) {
        const f = parse(row.f.replace(/k/g, k), { vars: [k] });
        // term = c·f(k) with a constant c
        const ks = [3, 4, 7, 10];
        const ratios = ks.map((x) => approx(term, { [k]: x }) / approx(f, { [k]: x }));
        if (!ratios.every((r) => Number.isFinite(r) && Math.abs(r - ratios[0]) < 1e-12 * Math.max(1, Math.abs(r)))) continue;
        const c = trySimplify(div(term, f));
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
        const value = trySimplify(mul(coef, add(V, neg(head))));
        return {
            value,
            steps: [
                step({
                    title: row.name,
                    tex: eachLanguage((l) => `\\sum_{${k}=${row.s}}^{\\infty} ${tex(f, l)} = ${tex(V, l)}`),
                    text: msg('calculus.series.classic_sum_term_differs_from_table'),
                }),
                step({ title: msg('calculus.series.substitute'), tex: eachLanguage((l) => `${sumTex(term, k, lo, null, l)} = ${tex(value, l)}`) }),
            ],
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
    const lv = lim && lim.value !== null && typeof lim.value === 'object' ? approx(lim.value) : lim?.value === 'inf' || lim?.value === '-inf' ? Infinity : NaN;
    if (lim && (lim.value === 'dne' || (Number.isFinite(lv) && Math.abs(lv) > 1e-12) || lv === Infinity)) {
        return {
            diverges: true,
            type: 'necessary',
            steps: [
                step({
                    title: msg('calculus.series.necessary_condition_fails'),
                    tex: eachLanguage(
                        (l) =>
                            `\\lim_{${k}\\to\\infty} ${tex(term, l)} ${lim.value === 'dne' ? msg('calculus.series.does_not_exist_tex').in(l) : `= ${typeof lim.value === 'object' ? tex(lim.value, l) : '\\infty'} \\ne 0`}`,
                    ),
                    text: msg('calculus.series.if_series_converges_its_terms_tend'),
                }),
            ],
        };
    }
    // rational term of degree −1 or more: comparison with the harmonic series
    try {
        const nd0 = numDen(trySimplify(term));
        const Np = nd0 && Poly.fromNode(nd0.num, k);
        const Dp = nd0 && Poly.fromNode(nd0.den, k);
        if (Np && Dp && Dp.degree - Np.degree === 1) {
            return {
                diverges: true,
                type: 'harmonic',
                steps: [
                    step({
                        title: msg('calculus.series.comparison_with_harmonic_series'),
                        tex: eachLanguage((l) => `${tex(term, l)} \\sim \\frac{${Np.lead.div(Dp.lead).toTex(l)}}{${k}}`),
                        text: msg('calculus.series.terms_behave_like_and_harmonic_series'),
                    }),
                ],
            };
        }
    } catch {
        /* not rational */
    }
    return null;
}

// |term| ~ c/k^p for large k: p from three far points (must agree), as a simple fraction; the sign must settle
function powerRate(term, k) {
    const ks = [1e3, 1e4, 1e5, 1e6];
    const ts = ks.map((x) => approx(term, { [k]: x }));
    if (!ts.every((t) => Number.isFinite(t) && t !== 0)) return null;
    // one sign for all large k: neighbours too, not only these (even) points
    const signs = [...ks, 1e3 + 1, 1e4 + 1, 1e5 + 3, 1e5 + 7, 12345, 99999].map((x) => Math.sign(approx(term, { [k]: x })));
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
    return {
        diverges: true,
        type: 'p-series',
        steps: [
            step({
                title: msg('calculus.series.comparison_with'),
                tex: eachLanguage((l) => `${tex(term, l)} \\sim \\frac{c}{${k}^{${r.p.toTex(l)}}},\\quad p = ${r.p.toTex(l)} \\le 1`),
                text: msg('calculus.series.terms_keep_one_sign_and_decay', { p: r.p.toTex() }),
            }),
        ],
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
    const head = step({ title: msg('calculus.series.sum'), tex: eachLanguage((l) => sumTex(term, k, lo, hi, l)) });
    let r;
    try {
        if (hi)
            r = hi.lt(lo)
                ? {
                      value: N0,
                      steps: [step({ title: msg('calculus.series.empty_sum'), text: msg('calculus.series.end_is_below_start_no_terms') })],
                      type: 'empty',
                  }
                : finiteSum(term, k, lo, hi);
        else
            r =
                geometricInfinite(term, k, lo) ??
                arithGeoInfinite(term, k, lo) ??
                telescoping(term, k, lo) ??
                tableSum(term, k, lo) ??
                divergence(term, k) ??
                pSeries(term, k);
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        r = null;
    }
    if (r?.diverges) {
        const steps = [head, ...r.steps, step({ title: msg('calculus.series.answer'), tex: msg('calculus.series.series_diverges') })];
        steps[steps.length - 1].final = true;
        return { kind: 'diverges', value: null, type: r.type, steps, text: 'diverges' };
    }
    if (!r) {
        // a numeric estimate: partial sums with the average of two neighbours (alternating tails)
        if (hi) return { kind: 'unsupported', reason: msg('calculus.series.could_not_add_it_up'), steps: [] };
        const T = (x) => approx(term, { [k]: x });
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
            return { kind: 'unsupported', reason: msg('calculus.series.could_neither_find_sum_nor_prove'), steps: [] };
        }
        let s = 0;
        let prev = 0;
        const Nmax = 200000;
        const last = Number(lo.n) + Nmax - 1;
        for (let i = Number(lo.n); i <= last; i++) {
            prev = s;
            s += approx(term, { [k]: i });
        }
        // alternating: the mean of two neighbouring partial sums; one sign: the tail ∫ c/x^p ≈ t(N)(N + ½)/(p − 1)
        const est = leibniz ? (s + prev) / 2 : s + (rate ? (approx(term, { [k]: last }) * (last + 0.5)) / (rate.p.toNumber() - 1) : 0);
        const digits = leibniz || rate ? 8 : 6;
        if (!Number.isFinite(est)) return { kind: 'unsupported', reason: msg('calculus.series.could_not_estimate_sum'), steps: [] };
        const why = leibniz
            ? msg('calculus.series.series_alternates_and_absolute_values_of')
            : rate
              ? msg('calculus.series.terms_keep_one_sign_and_decay_2', { p: (lng) => rate.p.toTex(lng) })
              : msg('calculus.series.absolute_values_of_terms_are_at');
        const steps = [
            head,
            step({ title: msg('calculus.series.convergence'), text: why }),
            step({
                title: msg('calculus.series.numeric_estimate'),
                tex: `S \\approx ${est.toPrecision(digits)}`,
                text: msg('calculus.series.no_exact_sum_in_elementary_terms'),
            }),
        ];
        steps[steps.length - 1].final = true;
        return { kind: 'approx', value: null, approx: est, steps, type: 'numeric', text: `≈ ${est.toPrecision(digits)}` };
    }
    const value = trySimplify(r.value);
    const steps = [
        head,
        ...r.steps,
        step({ title: msg('calculus.series.answer'), tex: eachLanguage((l) => `${sumTex(term, k, lo, hi, l)} = ${tex(value, l)}`) }),
    ];
    steps[steps.length - 1].final = true;
    return { kind: 'value', value, approx: approx(value), type: r.type, steps, text: plainText(value) };
}
