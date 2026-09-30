// solve/polynomial — linear, quadratic and higher-degree equations, school style; «a product equals zero».

import { Q, rootExtract, bigGcd, bigLcm } from '../core/rational.js';
import { Poly } from '../core/poly.js';
import { num, sym, mul, div, neg, add, pow, numValue, containsVar, nodeSome, nodeKey } from '../core/ast.js';
import { numPolyRoots } from '../numbers/numeric/index.js';
import { N0, N1, S, approxC, approxNode, approxOf, exactZero, expd, parQ, pick, simp, simpOr, sq, tex } from './common.js';
import { solveCore } from './equation.js';
import { IntervalSet } from './intervals.js';
import { approxComplexTex, cmpRoots, hasI, mergeRoots, mkRoot, mkRootC, qRoot, rootsTex, sameRoot } from './roots.js';
import { familiesTex, familiesToRoots, mergeFamilies } from './trig.js';
import { msg, notation, eachLanguage } from '../i18n/index.js';

// ---------------------------------------------------------------- polynomials: helpers

export const polyTex = (P, v, lang) => tex(P.toNode(v), lang);
const X_POW = (v, k) => (k === 1 ? v : `${v}^{${k}}`);

export function multOf(P, m) {
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
        ? msg('solve.polynomial.multiply_both_sides_by')
        : msg('solve.polynomial.multiply_both_sides_by_2', { p: tex(num(k)) });
    else if (k.inv().isInt()) title = msg('solve.polynomial.divide_both_sides_by', { p: tex(num(k.inv())) });
    else title = msg('solve.polynomial.multiply_both_sides_by_2', { p: tex(num(k)) });
    const text = !k.isInt() && !k.inv().isInt()
        ? msg('solve.polynomial.this_makes_coefficients_integers_without_common')
        : k.isNeg() && k.abs().isOne()
            ? msg('solve.polynomial.positive_leading_coefficient_is_easier_to')
            : k.isInt()
                ? msg('solve.polynomial.this_clears_fractions')
                : msg('solve.polynomial.all_coefficients_share_this_factor_so');
    return S(title, { tex: eachLanguage((l) => `${polyTex(Pn, v, l)} = 0`), text });
}

// ---------------------------------------------------------------- quadratic equations

/** a x² + b x + c = 0 with rational coefficients → {roots, cplx, steps}. */
export function quadSolve(P0, ctx) {
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
        steps.push(S(msg('solve.polynomial.incomplete_quadratic_take_out_of_brackets', { v }), {
            tex: eachLanguage((l) => `${v}\\left(${polyTex(lin, v, l)}\\right) = 0`),
            text: msg('solve.polynomial.product_is_zero_when_one_of'),
        }));
        const rs = mergeRoots([qRoot(Q.ZERO), qRoot(r)]);
        steps.push(S(msg('solve.polynomial.roots'), { tex: eachLanguage((l) => `${v} = 0 \\quad ${msg('solve.polynomial.or').in(l)} \\quad ${polyTex(lin, v, l)} = 0 \\;\\Rightarrow\\; ${v} = ${tex(num(r), l)}`) }));
        roots.push(...rs);
        return { roots, cplx, steps };
    }
    if (b.isZero()) {
        const r = c.neg().div(a);
        steps.push(S(msg('solve.polynomial.incomplete_quadratic_solve_for', { vv }), {
            tex: eachLanguage((l) => `${vv} = ${tex(num(r), l)}`),
        }));
        if (r.isPos()) {
            const s = simpOr(pow(num(r), num(Q.HALF)));
            const sq1 = numValue(s);
            steps.push(S(msg('solve.polynomial.take_square_root_two_roots_of'), {
                tex: eachLanguage((l) => `${v} = \\pm\\sqrt{${tex(num(r), l)}} = \\pm ${tex(s, l)}`),
                text: msg('solve.polynomial.both_and_squared_give', { s: tex(s), p: tex(simpOr(neg(s))), p2: tex(num(r)) }),
            }));
            const mp = sq1 ? null : P;
            roots.push(sq1 ? qRoot(sq1.neg()) : { node: simpOr(neg(s)), approx: -Math.sqrt(r.toNumber()), mult: 1, minPoly: mp });
            roots.push(sq1 ? qRoot(sq1) : { node: s, approx: Math.sqrt(r.toNumber()), mult: 1, minPoly: mp });
        } else {
            const s = simpOr(pow(num(r.neg()), num(Q.HALF)));
            const zi = simpOr(mul(s, sym('i')));
            steps.push(S(msg('solve.polynomial.square_is_never_negative_so_there'), {
                text: msg('solve.polynomial.in_complex_numbers_there_are_roots', { v, zi: (lng) => tex(zi, lng) }),
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
    steps.push(S(msg('solve.polynomial.quadratic_equation_read_off_coefficients'), {
        tex: eachLanguage((l) => `a = ${tex(num(a), l)},\\quad b = ${tex(num(b), l)},\\quad c = ${tex(num(c), l)}`),
    }));
    steps.push(S(msg('solve.polynomial.compute_discriminant'), {
        tex: `D = b^2 - 4ac = ${parQ(b)}^{2} - 4 \\cdot ${parQ(a)} \\cdot ${parQ(c)} = ${b2} ${ac4 < 0n ? '+' : '-'} ${ac4 < 0n ? -ac4 : ac4} = ${D}`,
        text: msg('solve.polynomial.its_sign_tells_how_many_roots'),
    }));
    const f = quadFormulaRoots(A, B, C);
    const mb = tex(num(-B));
    const a2 = `${2n * A}`;
    if (D === 0n) {
        const r = f.real[0];
        steps.push(S(msg('solve.polynomial.one_root_double_one'), {
            tex: `${v} = -\\frac{b}{2a} = \\frac{${mb}}{${a2}} = ${tex(r.node)}`,
        }));
        roots.push(r);
    } else if (D > 0n) {
        let t = `${v}_{1,2} = \\frac{-b \\pm \\sqrt{D}}{2a} = \\frac{${mb} \\pm \\sqrt{${D}}}{${a2}}`;
        if (f.inn === undefined) {
            const s = rootExtract(D, 2).out;
            t = `${v}_{1,2} = \\frac{-b \\pm \\sqrt{D}}{2a} = \\frac{${mb} \\pm ${s}}{${a2}}`;
            steps.push(S(msg('solve.polynomial.two_roots'), { tex: t }));
            const [r1, r2] = f.real;
            steps.push(S(msg('solve.polynomial.compute_each_root'), {
                tex: eachLanguage((l) => `${v}_1 = \\frac{${mb} - ${s}}{${a2}} = ${tex(r1.node, l)};\\quad ${v}_2 = \\frac{${mb} + ${s}}{${a2}} = ${tex(r2.node, l)}`),
            }));
            roots.push(...f.real);
            const qs = numValue(r1.node).add(numValue(r2.node));
            const qp = numValue(r1.node).mul(numValue(r2.node));
            steps.push(S(msg('solve.polynomial.check_with_vieta_s_formulas'), {
                tex: eachLanguage((l) => `${v}_1 + ${v}_2 = ${tex(num(qs), l)} = -\\frac{b}{a},\\quad ${v}_1 ${v}_2 = ${tex(num(qp), l)} = \\frac{c}{a}`),
                text: msg('solve.polynomial.sum_of_roots_is_and_product'),
            }));
        } else {
            const { out } = rootExtract(D, 2);
            if (out > 1n) t += ` = \\frac{${mb} \\pm ${out}\\sqrt{${f.inn}}}{${a2}}`;
            const [r1, r2] = f.real;
            const reduced = f.r !== 2n * A;
            steps.push(S(msg('solve.polynomial.two_roots'), {
                tex: t,
                text: out > 1n ? msg('solve.polynomial.simplify_root', { D, out, inn: f.inn }) : undefined,
            }));
            steps.push(S(reduced ? msg('solve.polynomial.reduce_fraction') : msg('solve.polynomial.roots'), {
                tex: eachLanguage((l) => `${v}_1 = ${tex(r1.node, l)};\\quad ${v}_2 = ${tex(r2.node, l)}`),
            }));
            roots.push(...f.real);
        }
    } else {
        const zs = f.cplx;
        steps.push(S(msg('solve.polynomial.no_real_roots'), {
            text: msg('solve.polynomial.there_is_no_real_square_root', { v, p: (lng) => tex(zs[0].node, lng), p2: (lng) => tex(zs[1].node, lng) }),
        }));
        cplx.push(...zs);
    }
    return { roots, cplx, steps };
}

// ---------------------------------------------------------------- higher degree

/** A nested "solve this part" step: the result in the title line, the details inside. */
export function partStep(eqTex, res, v) {
    return S(eachLanguage((l) => (msg('solve.polynomial.solve', { eqTex: (lng) => pick(eqTex, lng) }).in(l))), {
        tex: eachLanguage((l) => (res.kind === 'all' ? `${v} \\in \\mathbb{R}` : rootsTex(res.roots, v, l))),
        sub: res.steps,
        text: !res.roots.length && res.cplx?.length ? msg('solve.polynomial.no_real_roots_2') : undefined,
    });
}

/** Push "solve lhs = rhs" as a nested step, unless it is already the answer (x = c). */
export function pushPart(steps, lhs, rhs, res, v) {
    if (lhs.type === 'sym' && lhs.name === v && !containsVar(rhs, v) && res.kind === 'roots' && res.roots.length === 1) return;
    steps.push(partStep(eachLanguage((l) => `${tex(lhs, l)} = ${tex(rhs, l)}`), res, v));
}

/** Any polynomial over Q (degree ≥ 1) → {roots, cplx, steps, numeric}. */
export function solveAnyPoly(P0, ctx) {
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
            steps: [S(msg('solve.polynomial.solve_for', { v }), { tex: eachLanguage((l) => `${v} = ${tex(num(r), l)}`) })],
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
    return shown.join(notation(lang).listTex) + (pos.length > 16 ? ',\\ \\ldots' : '');
}

function hornerTex(P, r, lang) {
    const h = P.horner(r);
    const top = h.top.map((q) => tex(num(q), lang));
    const row = h.row.map((q) => tex(num(q), lang));
    return `\\begin{array}{c|${'c'.repeat(top.length)}} & ${top.join(' & ')} \\\\ \\hline ${tex(num(r), lang)} & ${row.join(' & ')} \\end{array}`;
}

const linFactorNode = (v, r) => (r.isZero() ? sym(v) : add(sym(v), num(r.neg())));

export const complexApproxNode = (re, im, digits = 16) => {
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
    if (deg === 3) return msg('solve.polynomial.cubics_have_cardano_s_formula_but');
    if (deg === 4) return msg('solve.polynomial.quartics_have_ferrari_s_method_but');
    return msg('solve.polynomial.from_degree_5_on_there_is');
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
    const eqTex = (Q_) => eachLanguage((l) => `${polyTex(Q_, v, l)} = 0`);

    // 1. common factor x^k
    if (nz[0] > 0) {
        const k = nz[0];
        const Qp = new Poly(P.c.slice(k));
        const xk = X_POW(v, k);
        steps.push(S(msg('solve.polynomial.take_out_of_brackets', { xk }), {
            tex: eachLanguage((l) => `${xk}\\left(${polyTex(Qp, v, l)}\\right) = 0`),
            text: msg('solve.polynomial.product_is_zero_when_one_of_2', { v, Qp: (lng) => polyTex(Qp, v, lng) }),
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
        steps.push(S(msg('solve.polynomial.solve_for_2', { xn }), { tex: eachLanguage((l) => `${xn} = ${tex(num(r), l)}`) }));
        const exactR = r.exactRoot(deg);
        if (deg % 2 === 1) {
            const node = exactR ? num(exactR) : simpOr(pow(num(r), num(new Q(1n, BigInt(deg)))));
            steps.push(S(msg('solve.polynomial.odd_power_exactly_one_real_root'), {
                tex: eachLanguage((l) => `${v} = \\sqrt[${deg}]{${tex(num(r), l)}} = ${tex(node, l)}`),
            }));
            roots.push(exactR ? qRoot(exactR) : { node, approx: Math.sign(r.toNumber()) * Math.abs(r.toNumber()) ** (1 / deg), mult: 1, minPoly: P });
        } else if (r.isPos()) {
            const node = exactR ? num(exactR) : simpOr(pow(num(r), num(new Q(1n, BigInt(deg)))));
            steps.push(S(msg('solve.polynomial.even_power_two_roots_of_opposite'), {
                tex: eachLanguage((l) => `${v} = \\pm\\sqrt[${deg}]{${tex(num(r), l)}} = \\pm ${tex(node, l)}`),
            }));
            const a = r.toNumber() ** (1 / deg);
            roots.push(exactR ? qRoot(exactR.neg()) : { node: simpOr(neg(node)), approx: -a, mult: 1, minPoly: P });
            roots.push(exactR ? qRoot(exactR) : { node, approx: a, mult: 1, minPoly: P });
        } else {
            steps.push(S(msg('solve.polynomial.even_power_is_never_negative_no')));
        }
        if (ctx.domain === 'complex') {
            const n = numericRoots(P, ctx);
            cplx.push(...n.cplx);
            if (n.cplx.length) steps.push(S(msg('solve.polynomial.complex_roots'), { tex: eachLanguage((l) => n.cplx.map((z) => approxComplexTex(z.approx, l)).join(';\\ ')), text: msg('solve.polynomial.found_numerically') }));
            numeric = numeric || n.cplx.length > 0;
        }
        return { roots, cplx, steps, numeric };
    }

    // 3. trinomial in x^m: a x^{2m} + b x^m + c
    if (nz.length === 3 && nz[0] === 0 && nz[2] === 2 * nz[1] && nz[1] >= 2) {
        const m = nz[1];
        const Tq = new Poly([P.coeff(0), P.coeff(m), P.coeff(2 * m)]);
        const xm = X_POW(v, m);
        const name = m === 2 ? msg('solve.polynomial.biquadratic') : msg('solve.polynomial.trinomial');
        steps.push(S(msg('solve.polynomial.this_is_equation_substitute', { p: name, xm }), {
            tex: eachLanguage((l) => `${polyTex(Tq, 't', l)} = 0`),
            text: m % 2 === 0
                ? msg('solve.polynomial.since_only_will_do', { xm })
                : msg('solve.polynomial.equation_is_now_quadratic_in'),
        }));
        const tr = solveAnyPoly(Tq, { v: 't', domain: 'real' });
        steps.push(partStep(eachLanguage((l) => `${polyTex(Tq, 't', l)} = 0`), tr, 't'));
        const back = [];
        for (const t of tr.roots) {
            const tq = numValue(t.node);
            const tMin = t.minPoly ?? new Poly([tq.neg(), Q.ONE]);
            const mp = composeXm(tMin, m).primitive();
            const tt = (l) => tex(t.node, l);
            if (m % 2 === 0 && t.approx < -1e-12) {
                back.push(S(eachLanguage((l) => `$${xm} = ${tt(l)}$`), { text: msg('solve.polynomial.even_power_is_never_negative_no_2') }));
                if (ctx.domain === 'complex' && m === 2) {
                    const z = simpOr(mul(sym('i'), pow(simpOr(neg(t.node)), num(Q.HALF))));
                    const im = Math.sqrt(-t.approx);
                    cplx.push({ node: simpOr(neg(z)), approx: { re: 0, im: -im }, mult: 1, minPoly: mp, complex: true }, { node: z, approx: { re: 0, im }, mult: 1, minPoly: mp, complex: true });
                }
                continue;
            }
            if (Math.abs(t.approx) <= 1e-12) {
                back.push(S(eachLanguage((l) => `$${xm} = 0$`), { tex: `${v} = 0` }));
                roots.push(qRoot(Q.ZERO));
                continue;
            }
            const rootNode = simpOr(pow(t.node, num(new Q(1n, BigInt(m)))));
            const a = Math.sign(t.approx) * Math.abs(t.approx) ** (1 / m);
            const rq = numValue(rootNode);
            if (m % 2 === 0) {
                back.push(S(eachLanguage((l) => `$${xm} = ${tt(l)}$`), { tex: eachLanguage((l) => `${v} = \\pm ${tex(rootNode, l)}`) }));
                roots.push(rq ? qRoot(rq.neg()) : { node: simpOr(neg(rootNode)), approx: -a, mult: 1, minPoly: mp });
                roots.push(rq ? qRoot(rq) : { node: rootNode, approx: a, mult: 1, minPoly: mp });
            } else {
                back.push(S(eachLanguage((l) => `$${xm} = ${tt(l)}$`), { tex: eachLanguage((l) => `${v} = ${tex(rootNode, l)}`) }));
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
        steps.push(S(msg('solve.polynomial.substitute_back'), { sub: back, tex: eachLanguage((l) => rootsTex(mergeRoots(roots), v, l)) }));
        return { roots, cplx, steps, numeric };
    }

    // 4. reciprocal (symmetric) quartic: a x^4 + b x^3 + c x^2 + b x + a
    if (deg === 4 && P.coeff(4).eq(P.coeff(0)) && P.coeff(3).eq(P.coeff(1)) && !P.coeff(1).isZero()) {
        const a = P.coeff(4);
        const b = P.coeff(3);
        const c = P.coeff(2);
        const Tq = new Poly([c.sub(a.mul(2)), b, a]);
        steps.push(S(msg('solve.polynomial.symmetric_reciprocal_equation_divide_by', { v }), {
            tex: eachLanguage((l) => `${tex(num(a), l) === '1' ? '' : tex(num(a), l)}\\left(${v}^2 + \\frac{1}{${v}^2}\\right) ${b.isNeg() ? '-' : '+'} ${b.abs().isOne() ? '' : tex(num(b.abs()), l)}\\left(${v} + \\frac{1}{${v}}\\right) ${c.isNeg() ? '-' : '+'} ${tex(num(c.abs()), l)} = 0`),
            text: msg('solve.polynomial.coefficients_read_same_both_ways_is', { v }),
        }));
        steps.push(S(msg('solve.polynomial.substitute_then', { v }), {
            tex: eachLanguage((l) => `${polyTex(Tq, 't', l)} = 0`),
        }));
        const tr = solveAnyPoly(Tq, { v: 't', domain: 'real' });
        steps.push(partStep(eachLanguage((l) => `${polyTex(Tq, 't', l)} = 0`), tr, 't'));
        const back = [];
        for (const t of tr.roots) {
            const tq = numValue(t.node);
            if (tq) {
                const Qx = new Poly([Q.ONE, tq.neg(), Q.ONE]);
                const sub = solveAnyPoly(Qx, ctx);
                roots.push(...sub.roots);
                cplx.push(...(sub.cplx ?? []));
                back.push(partStep(eachLanguage((l) => `${v} + \\frac{1}{${v}} = ${tex(t.node, l)} \\;\\Leftrightarrow\\; ${polyTex(Qx, v, l)} = 0`), sub, v));
            } else {
                const res = nodeQuadRoots(N1, simpOr(neg(t.node)), N1, ctx);
                roots.push(...res.roots.map((r) => ({ ...r, minPoly: P })));
                cplx.push(...res.cplx.map((r) => ({ ...r, minPoly: P })));
                back.push(S(eachLanguage((l) => `$${v} + \\frac{1}{${v}} = ${tex(t.node, l)}$`), { tex: eachLanguage((l) => rootsTex(res.roots, v, l)), sub: res.steps }));
            }
        }
        steps.push(S(msg('solve.polynomial.substitute_back'), { sub: back, tex: eachLanguage((l) => rootsTex(mergeRoots(roots), v, l)) }));
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
        steps.push(S(msg('solve.polynomial.group_terms'), {
            tex: eachLanguage((l) => `${tex(grouped, l)} = 0 \\;\\Rightarrow\\; \\left(${polyTex(lin, v, l)}\\right)\\left(${polyTex(sqr, v, l)}\\right) = 0`),
            text: msg('solve.polynomial.take_out_of_first_two_terms'),
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
    steps.push(S(msg('solve.polynomial.look_for_rational_roots'), {
        text: msg('solve.polynomial.if_polynomial_with_integer_coefficients_has', { cands: (lng) => candidatesTex(cands, lng) }),
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
            const triedTex = (l) => tried.slice(-6).map(([x, y]) => `P(${tex(num(x), l)}) = ${tex(num(y), l)} \\ne 0`).join(notation(l).listTex);
            steps.push(S(msg('solve.polynomial.horner_s_scheme_is_root', { v, p: (lng) => tex(num(c), lng) }), {
                tex: eachLanguage((l) => hornerTex(rest, c, l)),
                text: msg('solve.polynomial.remainder_last_number_is_zero_so', { p: (lng) => tried.length ? msg('solve.polynomial.checked', { p: (lng) => triedTex(lng) }).in(lng) : '', p2: (lng) => tex(num(c), lng), p3: (lng) => tex(linFactorNode(v, c), lng), p4: (lng) => tex(mul(linFactorNode(v, c), Qn.toNode(v)), lng) }),
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
        steps.push(S(msg('solve.polynomial.factor_remaining_polynomial'), {
            tex: eachLanguage((l) => `${polyTex(restP, v, l)} = ${tex(prod, l)}`),
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
    steps.push(S(msg('solve.polynomial.has_no_more_rational_roots', { restP: (lng) => polyTex(restP, v, lng) }), {
        text: numericNote(restP.degree),
        tex: eachLanguage((l) => (n.roots.length ? rootsTex(n.roots, v, l) : msg('solve.polynomial.no_real_roots_3').in(l))),
    }));
    return { roots, cplx, steps, numeric };
}

/** Quadratic with constant node coefficients (irrational ones allowed) → {roots, cplx, steps}. */
export function nodeQuadRoots(aN, bN, cN, ctx) {
    const v = ctx.v;
    const cx = [aN, bN, cN].some(hasI);
    const co = cx ? { complex: true } : undefined;
    const D = simpOr(expd(add(pow(bN, num(2)), mul(num(-4), aN, cN)), co) ?? add(pow(bN, num(2)), mul(num(-4), aN, cN)), co);
    const d = approxOf(D);
    const steps = [S(msg('solve.polynomial.discriminant'), { tex: eachLanguage((l) => `D = b^2 - 4ac = ${tex(D, l)}`) })];
    const two = mul(num(2), aN);
    const roots = [];
    const cplx = [];
    const Dc = cx ? approxC(D) : null;
    if (cx && Dc && Math.abs(Dc.im) > 1e-12 * Math.max(1, Math.abs(Dc.re))) {
        // a non-real discriminant (complex coefficients): its square root, exactly when it is a Gaussian rational
        const s = simpOr(pow(D, num(Q.HALF)), co);
        const exactS = !(s.type === 'pow' || nodeSome(s, (x) => x.type === 'pow' && hasI(x.base)));
        steps.push(S(msg('solve.polynomial.square_root_of_complex_discriminant'), {
            tex: eachLanguage((l) => `\\sqrt{D} = ${exactS ? `\\pm\\left(${tex(s, l)}\\right)` : `\\pm\\sqrt{${tex(D, l)}}`}`),
            text: exactS
                ? msg('solve.polynomial.look_for_with_check', { s: (lng) => tex(s, lng), D: (lng) => tex(D, lng) })
                : undefined,
        }));
        for (const sg of [-1, 1]) {
            const node = simpOr(div(add(neg(bN), sg < 0 ? neg(s) : s), two), co);
            const r = mkRootC(node);
            if (r.complex) cplx.push(r);
            else roots.push(r);
        }
        steps.push(S(msg('solve.polynomial.roots'), { tex: eachLanguage((l) => `${v}_{1,2} = \\frac{-b \\pm \\sqrt{D}}{2a}:\\quad ${[...roots, ...cplx].map((r) => tex(r.node, l)).join(notation(l).listTex)}`) }));
        return { roots, cplx, steps };
    }
    if (Math.abs(d) <= 1e-12 * Math.max(1, Math.abs(approxOf(bN)) ** 2) && exactZero(D) !== false) {
        const r = simpOr(div(neg(bN), two));
        roots.push(mkRoot(r, { mult: 2 }));
        steps.push(S(msg('solve.polynomial.one_root'), { tex: eachLanguage((l) => `${v} = ${tex(r, l)}`) }));
    } else if (d > 0) {
        const s = simpOr(pow(D, num(Q.HALF)));
        for (const sg of [-1, 1]) roots.push(mkRoot(simpOr(div(add(neg(bN), sg < 0 ? neg(s) : s), two))));
        roots.sort(cmpRoots);
        steps.push(S(msg('solve.polynomial.two_roots'), { tex: eachLanguage((l) => rootsTex(roots, v, l)) }));
    } else {
        const s = simpOr(pow(simpOr(neg(D)), num(Q.HALF)));
        for (const sg of [-1, 1]) {
            const node = simpOr(div(add(neg(bN), mul(num(sg), sym('i'), s)), two), { complex: true });
            cplx.push({ node, approx: approxC(node) ?? { re: NaN, im: NaN }, mult: 1, complex: true });
        }
        steps.push(S(msg('solve.polynomial.no_real_roots')));
    }
    return { roots, cplx, steps };
}

// ---------------------------------------------------------------- linear equations (school style)

export const isZeroNode = (n) => n.type === 'num' && n.value.isZero();
export const monoNode = (c, v, k = 1) => simpOr(mul(num(c), k === 1 ? sym(v) : pow(sym(v), num(k))));
export const sumNode = (terms) => (terms.length ? (terms.length === 1 ? terms[0] : add(terms)) : N0);

/** a₁x + a₀ = b₁x + b₀ (both sides polynomials over Q, the difference of degree ≤ 1). */
export function solveLinearSchool(lhs, rhs, A, B, ctx) {
    const v = ctx.v;
    const steps = [];
    let den = 1n;
    for (const q of [...A.c, ...B.c]) den = bigLcm(den, q.d);
    let A1 = A;
    let B1 = B;
    const eqT = (P1, P2) => eachLanguage((l) => `${polyTex(P1, v, l)} = ${polyTex(P2, v, l)}`);
    const expanded = nodeKey(simpOr(lhs)) !== nodeKey(A.toNode(v)) || nodeKey(simpOr(rhs)) !== nodeKey(B.toNode(v)) || nodeSome(lhs, (n) => n.type === 'mul' && n.args.some((a) => a.type === 'add')) || nodeSome(rhs, (n) => n.type === 'mul' && n.args.some((a) => a.type === 'add'));
    if (den > 1n) {
        A1 = A.scale(new Q(den));
        B1 = B.scale(new Q(den));
        steps.push(S(msg('solve.polynomial.multiply_both_sides_by_common_denominator', { den }), {
            tex: eqT(A1, B1),
            text: msg('solve.polynomial.multiplying_both_sides_by_same_non'),
        }));
    } else if (expanded) {
        steps.push(S(msg('solve.polynomial.expand_brackets_and_collect_like_terms'), { tex: eqT(A1, B1) }));
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
        steps.push(S(msg('solve.polynomial.move_terms_to_left_and_numbers', { v }), {
            tex: eachLanguage((l) => `${tex(sumNode(left), l)} = ${tex(sumNode(right), l)}`),
            text: hi >= 2
                ? msg('solve.polynomial.higher_powers_of_are_same_on', { v })
                : msg('solve.polynomial.term_that_crosses_equals_sign_changes'),
        }));
        if (left.length > 1 || right.length > 1) steps.push(S(msg('solve.polynomial.collect_like_terms'), { tex: eachLanguage((l) => `${tex(monoNode(a, v), l)} = ${tex(num(b), l)}`) }));
    }
    if (a.isZero()) {
        if (b.isZero()) {
            steps.push(S(msg('solve.polynomial.we_get_true_for_every', { v }), {
                text: msg('solve.polynomial.equation_is_identity_every_number_is'),
            }));
            return { kind: 'all', roots: [], steps, type: 'linear' };
        }
        steps.push(S(msg('solve.polynomial.we_get_which_never_holds', { v, p: (lng) => tex(num(b), lng) }), {
            text: msg('solve.polynomial.left_side_is_zero_for_every', { v }),
        }));
        return { kind: 'none', roots: [], steps, type: 'linear' };
    }
    const r = b.div(a);
    if (!a.isOne()) {
        steps.push(S(msg('solve.polynomial.divide_both_sides_by', { p: (lng) => tex(num(a), lng) }), {
            tex: eachLanguage((l) => {
                const fr = a.isInt() && b.isInt() ? `\\frac{${tex(num(b), l)}}{${tex(num(a), l)}}` : `${tex(num(b), l)} : ${parQ(a, l)}`;
                const rt = tex(num(r), l);
                return fr === rt ? `${v} = ${rt}` : `${v} = ${fr} = ${rt}`;
            }),
            text: msg('solve.polynomial.that_is_allowed_coefficient_is_not'),
        }));
    }
    return { kind: 'roots', roots: [qRoot(r)], steps, type: 'linear' };
}

// ---------------------------------------------------------------- polynomial equations of degree ≥ 2

export function solvePolyEquation(lhs, rhs, P, ctx) {
    const v = ctx.v;
    const steps = [];
    const rhsZero = isZeroNode(simpOr(rhs));
    const same = rhsZero && nodeKey(simpOr(lhs)) === nodeKey(P.toNode(v));
    if (!same) {
        steps.push(S(rhsZero ? msg('solve.polynomial.expand_brackets_and_collect_like_terms') : msg('solve.polynomial.move_everything_to_left_and_collect'), {
            tex: eachLanguage((l) => `${polyTex(P, v, l)} = 0`),
            text: rhsZero ? undefined : msg('solve.polynomial.terms_cross_equals_sign_with_opposite'),
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

export function productSplit(lhs, rhs, ctx) {
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
    const steps = [S(msg('solve.polynomial.product_equals_zero'), {
        text: msg('solve.polynomial.product_is_zero_when_at_least'),
        tex: eachLanguage((l) => bases.map((b) => `${tex(b.node, l)} = 0`).join(` \\quad ${msg('solve.polynomial.or').in(l)} \\quad `)),
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
        steps.push(partStep(eachLanguage((l) => `${tex(b.node, l)} = 0`), { ...sub, roots: sub.families ? [] : sub.roots }, v));
        if (sub.families) steps[steps.length - 1].tex = eachLanguage((l) => familiesTex(sub.families, v, l));
    }
    roots = mergeRoots(roots, true);
    if (kind === 'all') return { kind: 'all', roots: [], steps, type: 'product', set };
    if (set && !set.isFinite()) return { kind: 'set', roots, set: set.union(IntervalSet.points(roots.map((r) => r.node))), steps, type: 'product' };
    if (families.length) return { kind: 'roots', roots: familiesToRoots(mergeFamilies(families)), families: mergeFamilies(families), steps, type: 'trig', periodic: true };
    return { kind: roots.length ? 'roots' : 'none', roots, complexRoots: mergeRoots(cplx), steps, type: 'product', numeric };
}
