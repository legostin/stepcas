// solve/polynomial — linear, quadratic and higher-degree equations, school style; «a product equals zero».

import { Q, rootExtract, bigGcd, bigLcm } from '../core/rational.js';
import { Poly } from '../core/poly.js';
import { num, sym, mul, div, neg, add, pow, numValue, containsVar, nodeSome, nodeKey } from '../core/ast.js';
import { numPolyRoots } from '../numbers/numeric/index.js';
import { N0, N1, S, T, approxC, approxNode, approxOf, byLang, exactZero, expd, parQ, pick, simp, simpOr, sq, tex } from './common.js';
import { solveCore } from './equation.js';
import { IntervalSet } from './intervals.js';
import { approxComplexTex, cmpRoots, hasI, mergeRoots, mkRoot, mkRootC, qRoot, rootsTex, sameRoot } from './roots.js';
import { familiesTex, familiesToRoots, mergeFamilies } from './trig.js';

// ---------------------------------------------------------------- polynomials: helpers

export const polyTex = (P, v, lang) => tex(P.toNode(v), lang);
const polyTexB = (P, v) => byLang((l) => polyTex(P, v, l));
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
export function partStep(eqTex, res, v) {
    const found = [...res.roots, ...(res.cplx ?? [])];
    return S(byLang((l) => (l === 'ru' ? `Решаем $${pick(eqTex, 'ru')}$` : `Solve $${pick(eqTex, 'en')}$`)), {
        tex: byLang((l) => (res.kind === 'all' ? `${v} \\in \\mathbb{R}` : rootsTex(res.roots, v, l))),
        sub: res.steps,
        text: !res.roots.length && res.cplx?.length ? T('Действительных корней нет.', 'No real roots.') : undefined,
    });
}

/** Push "solve lhs = rhs" as a nested step, unless it is already the answer (x = c). */
export function pushPart(steps, lhs, rhs, res, v) {
    if (lhs.type === 'sym' && lhs.name === v && !containsVar(rhs, v) && res.kind === 'roots' && res.roots.length === 1) return;
    steps.push(partStep(byLang((l) => `${tex(lhs, l)} = ${tex(rhs, l)}`), res, v));
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
export function nodeQuadRoots(aN, bN, cN, ctx) {
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

export function solvePolyEquation(lhs, rhs, P, ctx) {
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
