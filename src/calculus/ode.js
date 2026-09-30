// ode — ordinary differential equations of a first-year course, step by step.
//
//   solveOde("y' + y = x; y(0) = 1") → {kind: 'solution' | 'general' | 'unsupported', expr, general, type, steps, tex, text}
//
// First order: y' = f(x) (integrate), separable y' = f(x)·g(y), linear y' + p(x)y = q(x) (integrating factor),
// homogeneous y' = φ(y/x) (y = ux). Second order: a·y'' + b·y' + c·y = 0 with constant coefficients (the
// characteristic equation: two real roots, a double root, complex roots). Initial conditions y(x₀) = y₀,
// y'(x₀) = y₁ fix the constants. Every answer is substituted back into the equation numerically before it is
// returned; an answer that fails the check is not returned.
import { Q, MathError } from '../core/rational.js';
import { num, sym, add, mul, div, neg, pow, fn, rel, nodeKey, freeVars, containsVar, substitute, numValue, nodeSome } from '../core/ast.js';
import { parse } from '../core/parse.js';
import { toTex, toText } from '../core/print.js';
import { simplify } from '../core/simplify.js';
import { evaluate } from '../core/evaluate.js';
import { L, step } from '../core/steps.js';
import { derivative } from './derivative.js';
import { integrate } from './integral.js';
import { solveEquation } from '../solve/solve.js';
import { expand } from '../core/expand.js';
import { mapNode } from '../core/ast.js';

const YP = 'yp';
const YPP = 'ypp';
const N0 = num(0);
const N1 = num(1);
const N2 = num(2);
const simpO = (n) => {
    try {
        return simplify(n);
    } catch {
        return n;
    }
};
const val = (n, env) => {
    try {
        const x = evaluate(n, env);
        return typeof x === 'number' ? x : NaN;
    } catch {
        return NaN;
    }
};
const d = (n, v) => simpO(derivative(n, v).result);
const free = (n, ...vs) => vs.every((v) => !containsVar(n, v));
const isZ = (n) => n.type === 'num' && n.value.isZero();
// the shorter of the simplified and the expanded forms: e^(−x)(e^x(x − 1) + 2) → x − 1 + 2e^(−x)
function tidy(n) {
    const a = simpO(n);
    let b = null;
    try {
        b = simpO(expand(a));
    } catch {
        b = null;
    }
    return b && toText(b).length < toText(a).length ? b : a;
}
// ln|u| → ln u: after exponentiating, the sign goes into the constant (y = C·x rather than C·|x|)
const dropAbsInLn = (n) => mapNode(n, (m) => (m.type === 'fn' && m.name === 'ln' && m.args[0].type === 'fn' && m.args[0].name === 'abs' ? fn('ln', dropAbsInLn(m.args[0].args[0])) : undefined));
const E_ = sym('e');

/** TeX with the primes shown as primes. */
function tex(n, lang = 'ru') {
    return toTex(n, { lang }).replace(/\\mathrm\{([a-z])('+)\}/g, '$1$2');
}
const bt = (f) => L(f('ru'), f('en'));

/* ------------------------------------------------------------------ input */

// "y' + y = x; y(0) = 1" → {eq: node (primes as yp, ypp), conds: [{order, at, value}], y, x}
function readInput(input) {
    const parts = String(input).split(/[;\n]/).map((s) => s.trim()).filter(Boolean);
    let eq = null;
    const conds = [];
    for (const p of parts) {
        const m = p.match(/^([a-zA-Z])('*)\s*\(\s*([^()]+?)\s*\)\s*=\s*(.+)$/);
        if (m && eq) {
            conds.push({ fname: m[1], order: m[2].length, at: simpO(parse(m[3])), value: simpO(parse(m[4])) });
            continue;
        }
        if (eq) throw new MathError(L('Уравнение должно быть одно, остальное — начальные условия вида y(0) = 1.', 'There must be one equation; the rest are initial conditions like y(0) = 1.'));
        eq = p;
    }
    if (!eq) throw new MathError(L('Нет уравнения.', 'No equation.'));
    const fm = eq.match(/([a-zA-Z])'/);
    const y = fm ? fm[1] : 'y';
    if (!fm) throw new MathError(L('В уравнении нет производной (y\').', 'The equation has no derivative (y\').'));
    const text = eq.replace(new RegExp(`${y}''`, 'g'), ` ${YPP} `).replace(new RegExp(`${y}'`, 'g'), ` ${YP} `);
    const node = parse(text, { vars: [YP, YPP] });
    if (node.type !== 'rel' || node.op !== '=') throw new MathError(L('Нужно уравнение со знаком «=».', 'An equation with "=" is needed.'));
    const vars = freeVars(node).filter((v) => v !== y && v !== YP && v !== YPP);
    if (vars.length > 1) throw new MathError(L(`Слишком много букв: ${vars.join(', ')}.`, `Too many letters: ${vars.join(', ')}.`));
    return { eq: node, conds: conds.filter((c) => c.fname === y), y, x: vars[0] ?? 'x' };
}

/* ------------------------------------------------------------------ inverse: G(y) = H → y */

// peel G around the unknown; sign choices (±, |·|) go by the point (x0, y0) when there is one
function invert(G, y, H, pick) {
    let g = G;
    let h = H;
    for (let guard = 0; guard < 20; guard++) {
        if (g.type === 'sym' && g.name === y) return simpO(h);
        if (g.type === 'neg') {
            h = neg(h);
            g = g.arg;
            continue;
        }
        if (g.type === 'add') {
            const withY = g.args.filter((t) => containsVar(t, y));
            if (withY.length !== 1) return null;
            h = add(h, neg(add(g.args.filter((t) => !containsVar(t, y)))));
            g = withY[0];
            continue;
        }
        if (g.type === 'mul') {
            const withY = g.args.filter((t) => containsVar(t, y));
            if (withY.length !== 1) return null;
            h = div(h, mul(g.args.filter((t) => !containsVar(t, y))));
            g = withY[0];
            continue;
        }
        if (g.type === 'div') {
            if (!containsVar(g.den, y)) {
                h = mul(h, g.den);
                g = g.num;
            } else if (!containsVar(g.num, y)) {
                h = div(g.num, h);
                g = g.den;
            } else return null;
            continue;
        }
        if (g.type === 'pow') {
            if (containsVar(g.exp, y)) {
                if (containsVar(g.base, y)) return null;
                h = g.base.type === 'sym' && g.base.name === 'e' ? fn('ln', h) : div(fn('ln', h), fn('ln', g.base));
                g = g.exp;
                continue;
            }
            const e = numValue(g.exp);
            if (!e) return null;
            if (e.eq(-1)) {
                h = div(N1, h);
                g = g.base;
                continue;
            }
            const inv = pow(h, num(e.inv()));
            if (e.n % 2n === 0n) {
                const both = [inv, neg(inv)];
                const chosen = pick ? pick((c) => invert(g.base, y, c, pick), both) : inv;
                if (!chosen) return null;
                return chosen;
            }
            h = inv;
            g = g.base;
            continue;
        }
        if (g.type === 'fn') {
            const a = g.args[0];
            if (g.name === 'ln' && a.type === 'fn' && a.name === 'abs') {
                const ex = pow(E_, h);
                const chosen = pick ? pick((c) => invert(a.args[0], y, c, pick), [ex, neg(ex)]) : ex;
                return chosen;
            }
            const INV = { ln: (t) => pow(E_, t), exp: (t) => fn('ln', t), sqrt: (t) => pow(t, N2), atan: (t) => fn('tan', t), tan: (t) => fn('atan', t), sin: (t) => fn('asin', t), cos: (t) => fn('acos', t), asin: (t) => fn('sin', t), cbrt: (t) => pow(t, num(3)) };
            if (!INV[g.name] || g.args.length !== 1) return null;
            h = INV[g.name](h);
            g = a;
            continue;
        }
        return null;
    }
    return null;
}

/* ------------------------------------------------------------------ checks */

// residual of the equation at a few points: y = Y(x) substituted with its derivatives
function satisfies(eq, Y, x, y) {
    const Y1 = d(Y, x);
    const Y2 = d(Y1, x);
    const E = add(eq.lhs, neg(eq.rhs));
    const pts = [0.37, 0.81, 1.23, -0.44, 0.05, 1.7];
    let good = 0;
    for (const p of pts) {
        const env = { [x]: p };
        const y0 = val(Y, env);
        const y1 = val(Y1, env);
        const y2 = val(Y2, env);
        if (![y0, y1, y2].every(Number.isFinite)) continue;
        const r = val(E, { ...env, [y]: y0, [YP]: y1, [YPP]: y2 });
        if (!Number.isFinite(r)) continue;
        if (Math.abs(r) > 1e-6 * Math.max(1, Math.abs(y0), Math.abs(y1), Math.abs(y2))) return false;
        good++;
    }
    return good >= 3;
}

/* ------------------------------------------------------------------ first order */

// a sign choice (±, |·|) by the initial condition: the candidate whose value at x₀ is the target
function picker(x, cond, target) {
    if (!cond) return null;
    const x0 = val(cond.at, {});
    const t = val(target ?? cond.value, {});
    return (inv, cands) => {
        for (const c of cands) {
            const r = inv(c);
            if (!r) continue;
            const v0 = val(r, { [x]: x0 });
            if (Math.abs(v0 - t) < 1e-9 * Math.max(1, Math.abs(t))) return r;
        }
        return null;
    };
}

// dy/g(y) as it is written by hand: e^y dy, u du, but dy/y², dy/(1 + y²)
function sepLeft(g, v, l) {
    const inv = simpO(div(N1, g));
    const frac = nodeSome(inv, (m) => m.type === 'div' || (m.type === 'pow' && numValue(m.exp)?.isNeg()));
    return frac ? `\\frac{d${v}}{${tex(g, l)}}` : numValue(inv)?.isOne() ? `d${v}` : `${tex(inv, l)}\\,d${v}`;
}

// y' = R(x, y) from the equation (linear in y')
function explicitFirst(E, y) {
    const a = d(E, YP);
    if (containsVar(a, YP) || isZ(a)) return null;
    const b = simpO(add(E, neg(mul(a, sym(YP)))));
    if (containsVar(b, YP)) return null;
    return simpO(neg(div(b, a)));
}

// e^(u + v) → e^u·e^v so that the factors separate
function splitExp(n) {
    if (n.type === 'pow' && n.base.type === 'sym' && n.base.name === 'e' && n.exp.type === 'add') return mul(n.exp.args.map((t) => pow(E_, t)));
    if (n.type === 'mul' || n.type === 'add') return { ...n, args: n.args.map(splitExp) };
    if (n.type === 'div') return div(splitExp(n.num), splitExp(n.den));
    if (n.type === 'neg') return neg(splitExp(n.arg));
    return n;
}
// R = f(x)·g(y) → {f, g}
function separate(R, x, y) {
    const S = splitExp(R);
    const factors = [];
    const walk = (n, sgn) => {
        if (n.type === 'mul') n.args.forEach((f) => walk(f, sgn));
        else if (n.type === 'div') {
            walk(n.num, sgn);
            walk(n.den, -sgn);
        } else if (n.type === 'neg') {
            factors.push([num(-1), 1]);
            walk(n.arg, sgn);
        } else factors.push([n, sgn]);
    };
    walk(S, 1);
    const fx = [];
    const gy = [];
    for (const [f, s] of factors) {
        const node = s > 0 ? f : pow(f, num(-1));
        if (!containsVar(f, y)) fx.push(node);
        else if (!containsVar(f, x)) gy.push(node);
        else return null;
    }
    if (!gy.length) return null;
    return { f: simpO(mul(fx.length ? fx : [N1])), g: simpO(mul(gy)) };
}

function solveFirst(E, x, y, cond, explicitAlready) {
    const R = explicitFirst(E, y);
    if (!R) return null;
    const steps = [];
    const Y = sym(y);
    const X = sym(x);
    const C = sym('C');
    const yp = sym("y'");
    const Rt = (l) => tex(R, l);
    if (!explicitAlready) steps.push(step({ title: L('Выражаем производную', 'Solve for the derivative'), tex: bt((l) => `${tex(yp, l)} = ${Rt(l)}`) }));
    const dRy = d(R, y);
    const p = !containsVar(dRy, y) ? simpO(neg(dRy)) : null;
    const q = p ? tidy(substitute(R, { [y]: N0 })) : null; // R = −p·y + q, so q = R(x, 0)
    const pick = picker(x, cond);

    // y' = q(x)
    if (!containsVar(R, y)) {
        const I = integrate(R, x, { steps: true });
        if (!I.result) return null;
        const F = I.result;
        steps.push(step({ title: L('Интегрируем', 'Integrate'), tex: bt((l) => `${y} = \\int ${tex(R, l)}\\,d${x} = ${tex(F, l)} + C`), sub: I.steps }));
        return finish({ general: add(F, C), steps, type: 'integrate', x, y, cond, solveC: (c0) => simpO(add(F, c0)) });
    }
    // linear with a right-hand side: the integrating factor
    if (p && q && !isZ(q) && !isZ(p) && free(q, y)) return linearFirst(p, q, x, y, cond, steps);
    // separable
    const sp = separate(R, x, y);
    if (sp) {
        const Iy = integrate(simpO(div(N1, sp.g)), y, { steps: true });
        const Ix = integrate(sp.f, x, { steps: true });
        if (!Iy.result || !Ix.result) return null;
        const G = Iy.result;
        const F = Ix.result;
        steps.push(step({
            title: L('Разделяем переменные', 'Separate the variables'),
            tex: bt((l) => `${sepLeft(sp.g, y, l)} = ${numValue(sp.f)?.isOne() ? `d${x}` : `${tex(sp.f, l)}\\,d${x}`}`),
            text: L(`Производная — это $\\frac{d${y}}{d${x}}$; умножаем на $d${x}$ и делим на $${tex(sp.g)}$ (при $${tex(sp.g)} \\ne 0$).`, `The derivative is $\\frac{d${y}}{d${x}}$; multiply by $d${x}$ and divide by $${tex(sp.g, 'en')}$ (where it is not zero).`),
        }));
        steps.push(step({ title: L('Интегрируем обе части', 'Integrate both sides'), tex: bt((l) => `${tex(G, l)} = ${tex(F, l)} + C`), sub: [...(Iy.steps ?? []).slice(-1), ...(Ix.steps ?? []).slice(-1)] }));
        const lnForm = G.type === 'fn' && G.name === 'ln' && G.args[0].type === 'fn' && G.args[0].name === 'abs' && G.args[0].args[0].type === 'sym';
        const Fe = lnForm ? dropAbsInLn(F) : F;
        const general = lnForm ? simpO(mul(C, pow(E_, Fe))) : invert(G, y, add(F, C), null);
        const solveC = (c0) => {
            if (lnForm) return simpO(mul(c0, pow(E_, Fe)));
            return invert(G, y, add(F, c0), pick);
        };
        if (lnForm) steps.push(step({ title: L(`Выражаем $${y}$`, `Express $${y}$`), tex: bt((l) => `|${y}| = e^{${tex(F, l)} + C} \\;\\Rightarrow\\; ${y} = ${tex(general, l)}`), text: L('Постоянная $\\pm e^{C}$ снова обозначена $C$; $C = 0$ даёт решение $y = 0$, потерянное при делении.', 'The constant $\\pm e^{C}$ is renamed $C$ again; $C = 0$ gives the solution $y = 0$ lost in the division.') }));
        else if (general) steps.push(step({ title: L(`Выражаем $${y}$`, `Express $${y}$`), tex: bt((l) => `${y} = ${tex(general, l)}`) }));
        return finish({ general: general ?? rel('=', G, add(F, C)), implicit: !general, steps, type: 'separable', x, y, cond, solveC, lnForm, G, F: Fe });
    }
    return homogeneous(R, x, y, cond, steps);
}

function linearFirst(p, q, x, y, cond, steps) {
    const Ip = integrate(p, x, { steps: true });
    if (!Ip.result) return null;
    const mu = simpO(pow(E_, dropAbsInLn(Ip.result)));
    const Iq = integrate(simpO(mul(mu, q)), x, { steps: true });
    if (!Iq.result) return null;
    const C = sym('C');
    steps.push(step({
        title: L('Линейное уравнение первого порядка', 'A first-order linear equation'),
        tex: bt((l) => {
            const negP = tex(p, 'en').startsWith('-');
            const py = simpO(mul(negP ? simpO(neg(p)) : p, sym(y)));
            return tex(rel('=', add(sym(`${y}'`), negP ? neg(py) : py), q), l);
        }),
        text: L('Вид $y\' + p(x)y = q(x)$. Умножаем на интегрирующий множитель $\\mu = e^{\\int p\\,dx}$: левая часть становится производной $(\\mu y)\'$.', 'The form $y\' + p(x)y = q(x)$. Multiply by the integrating factor $\\mu = e^{\\int p\\,dx}$: the left side becomes $(\\mu y)\'$.'),
    }));
    steps.push(step({ title: L('Интегрирующий множитель', 'The integrating factor'), tex: bt((l) => `\\mu = e^{\\int ${tex(p, l)}\\,d${x}} = ${tex(mu, l)}`) }));
    steps.push(step({ title: L('Интегрируем', 'Integrate'), tex: bt((l) => `(${tex(mu, l)}\\,${y})' = ${tex(simpO(mul(mu, q)), l)} \\;\\Rightarrow\\; ${tex(mu, l)}\\,${y} = ${tex(Iq.result, l)} + C`), sub: (Iq.steps ?? []).slice(-1) }));
    const general = tidy(div(add(Iq.result, C), mu));
    steps.push(step({ title: L(`Выражаем $${y}$`, `Express $${y}$`), tex: bt((l) => `${y} = ${tex(general, l)}`) }));
    return finish({ general, steps, type: 'linear', x, y, cond, solveC: (c0) => tidy(div(add(Iq.result, c0), mu)) });
}

// y' = φ(y/x): check φ(tx, ty) = φ(x, y), then y = ux
function homogeneous(R, x, y, cond, steps) {
    for (const [a, b, t] of [[0.7, 1.3, 2.1], [1.9, -0.6, 0.45], [-1.1, 0.8, 3.3]]) {
        const r1 = val(R, { [x]: a, [y]: b });
        const r2 = val(R, { [x]: a * t, [y]: b * t });
        if (!Number.isFinite(r1) || !Number.isFinite(r2) || Math.abs(r1 - r2) > 1e-9 * Math.max(1, Math.abs(r1))) return null;
    }
    const U = sym('u');
    const X = sym(x);
    const phi = tidy(substitute(R, { [x]: N1, [y]: U })); // degree 0: φ(u) = R(1, u)
    if (containsVar(phi, x)) return null;
    const den = simpO(add(phi, neg(U)));
    if (isZ(den)) return null;
    const Iu = integrate(simpO(div(N1, den)), 'u', { steps: true });
    if (!Iu.result) return null;
    const G = Iu.result;
    const F = fn('ln', fn('abs', X));
    const C = sym('C');
    steps.push(step({ title: L('Однородное уравнение: замена $y = ux$', 'A homogeneous equation: $y = ux$'), tex: bt((l) => `u + x u' = ${tex(phi, l)}`), text: L("Правая часть зависит только от $y/x$. Тогда $y' = u + xu'$.", "The right side depends on $y/x$ only. Then $y' = u + xu'$.") }));
    steps.push(step({ title: L('Разделяем переменные', 'Separate the variables'), tex: bt((l) => `${sepLeft(den, 'u', l)} = \\frac{d${x}}{${x}} \\;\\Rightarrow\\; ${tex(G, l)} = \\ln|${x}| + C`) }));
    const pickU = cond ? picker(x, cond, div(cond.value, cond.at)) : null;
    const Uinv = (c, pk = null) => invert(G, 'u', add(F, c), pk);
    const general = Uinv(C);
    return finish({
        general: general ? simpO(mul(general, X)) : rel('=', substitute(G, { u: div(sym(y), X) }), add(F, C)),
        implicit: !general,
        steps,
        type: 'homogeneous',
        x,
        y,
        cond,
        solveC: (c0) => {
            const u = Uinv(c0, pickU);
            return u ? simpO(mul(u, X)) : null;
        },
        constFromIc: (x0, y0) => simpO(add(substitute(G, { u: div(y0, x0) }), neg(substitute(F, { [x]: x0 })))),
    });
}

/* ------------------------------------------------------------------ second order, constant coefficients */

// a close fraction p/q (q ≤ 5000) or null
function rationalize(x) {
    if (!Number.isFinite(x)) return null;
    for (let q = 1; q <= 5000; q++) {
        const p = Math.round(x * q);
        if (Math.abs(p / q - x) < 1e-9 * Math.max(1, Math.abs(x))) return new Q(BigInt(p), BigInt(q));
    }
    return null;
}
// Gaussian elimination with partial pivoting (square system), null when singular
function solveLin(A, b) {
    const n = A.length;
    const M = A.map((r, i) => [...r, b[i]]);
    for (let c = 0; c < n; c++) {
        let p = c;
        for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
        if (Math.abs(M[p][c]) < 1e-12) return null;
        [M[c], M[p]] = [M[p], M[c]];
        for (let r = 0; r < n; r++) {
            if (r === c) continue;
            const k = M[r][c] / M[c][c];
            for (let j = c; j <= n; j++) M[r][j] -= k * M[c][j];
        }
    }
    return M.map((r, i) => r[n] / r[i]);
}
// f = Σ P(x)·e^(αx)·cos/sin(βx) → groups [{alpha, beta, deg}] (Q values), or null
function rhsGroups(f, x) {
    let e;
    try {
        e = simpO(expand(f));
    } catch {
        return null;
    }
    const terms = e.type === 'add' ? e.args : [e];
    const groups = new Map();
    for (const t0 of terms) {
        const t = t0.type === 'neg' ? t0.arg : t0;
        const fs = t.type === 'mul' ? t.args : [t];
        let alpha = Q.ZERO;
        let beta = Q.ZERO;
        let deg = 0;
        for (const g of fs) {
            if (!containsVar(g, x)) continue;
            const lin = (u) => {
                const k = simpO(div(u, sym(x)));
                return containsVar(k, x) ? null : numValue(k);
            };
            if (g.type === 'pow' && g.base.type === 'sym' && g.base.name === 'e') {
                const k = lin(g.exp);
                if (!k) return null;
                alpha = alpha.add(k);
            } else if (g.type === 'fn' && (g.name === 'sin' || g.name === 'cos')) {
                const k = lin(g.args[0]);
                if (!k || !beta.isZero()) return null;
                beta = k.abs();
            } else if (g.type === 'sym' && g.name === x) deg += 1;
            else if (g.type === 'pow' && g.base.type === 'sym' && g.base.name === x && numValue(g.exp)?.isInt() && numValue(g.exp).isPos()) deg += Number(numValue(g.exp).n);
            else return null;
        }
        const key = `${alpha}|${beta}`;
        const prev = groups.get(key);
        groups.set(key, { alpha, beta, deg: Math.max(deg, prev?.deg ?? 0) });
    }
    return [...groups.values()];
}
/**
 * The method of undetermined coefficients: y_p = x^s·e^(αx)·(A(x)cos βx + B(x)sin βx) for each group of the
 * right-hand side, s the multiplicity of α + βi among the characteristic roots. The coefficients come from
 * matching L[y_p] = f at sample points and must be simple fractions; the result is checked at other points.
 */
function undetermined(a, b, c, f, x) {
    const groups = rhsGroups(f, x);
    if (!groups || !groups.length) return null;
    const [av, bv, cv] = [val(a, {}), val(b, {}), val(c, {})];
    const X = sym(x);
    const basis = [];
    const names = [];
    const trials = [];
    const letters = 'ABCDEFGHKLMNPR';
    for (const g of groups) {
        const al = g.alpha.toNumber();
        const be = g.beta.toNumber();
        let s = 0;
        if (be === 0) {
            if (Math.abs(av * al * al + bv * al + cv) < 1e-12) s = Math.abs(2 * av * al + bv) < 1e-12 ? 2 : 1;
        } else {
            const disc = bv * bv - 4 * av * cv;
            if (disc < 0 && Math.abs(al + bv / (2 * av)) < 1e-12 && Math.abs(be * be - (-disc) / (4 * av * av)) < 1e-12) s = 1;
        }
        const ex = g.alpha.isZero() ? null : pow(E_, simpO(mul(num(g.alpha), X)));
        const parts = be === 0 ? [null] : [fn('cos', simpO(mul(num(g.beta), X))), fn('sin', simpO(mul(num(g.beta), X)))];
        const groupTrial = [];
        for (const tr of parts) {
            const poly = [];
            for (let j = 0; j <= g.deg; j++) {
                const xp = s + j === 0 ? null : s + j === 1 ? X : pow(X, num(s + j));
                const phi = mul([xp, ex, tr].filter(Boolean).length ? [xp, ex, tr].filter(Boolean) : [N1]);
                const nm = letters[names.length] ?? `A_${names.length}`;
                names.push(nm);
                basis.push(phi);
                poly.push(j === 0 ? sym(nm) : mul(sym(nm), j === 1 ? X : pow(X, num(j))));
            }
            const P = poly.length === 1 ? poly[0] : add(poly.reverse());
            groupTrial.push(tr ? mul(P, tr) : P);
        }
        const body = groupTrial.length === 1 ? groupTrial[0] : add(groupTrial);
        const xs = s === 0 ? null : s === 1 ? X : pow(X, num(s));
        const fs = [...(xs ? [xs] : []), body, ...(ex ? [ex] : [])];
        trials.push({ node: fs.length === 1 ? fs[0] : mul(fs), s, g });
    }
    const m = basis.length;
    if (m > 12) return null;
    const Lb = basis.map((phi) => simpO(add(mul(a, d(d(phi, x), x)), mul(b, d(phi, x)), mul(c, phi))));
    const pts = Array.from({ length: m + 4 }, (_, i) => -0.9 + (1.8 * (i + 0.5)) / (m + 4));
    const rows = pts.map((p) => Lb.map((l) => val(l, { [x]: p })));
    const rhs = pts.map((p) => val(f, { [x]: p }));
    if (rows.flat().some((z) => !Number.isFinite(z)) || rhs.some((z) => !Number.isFinite(z))) return null;
    // least squares through the normal equations
    const AtA = basis.map((_, i) => basis.map((__, j) => rows.reduce((acc, r) => acc + r[i] * r[j], 0)));
    const Atb = basis.map((_, i) => rows.reduce((acc, r, k) => acc + r[i] * rhs[k], 0));
    const sol = solveLin(AtA, Atb);
    if (!sol) return null;
    const qs = sol.map(rationalize);
    if (qs.some((z) => !z)) return null;
    const yp = tidy(add(basis.map((phi, i) => mul(num(qs[i]), phi))));
    // the check at other points
    for (const p of [0.123, -0.77, 1.31, 2.05]) {
        const lhs = val(add(mul(a, d(d(yp, x), x)), mul(b, d(yp, x)), mul(c, yp)), { [x]: p });
        const r = val(f, { [x]: p });
        if (!(Math.abs(lhs - r) < 1e-7 * Math.max(1, Math.abs(r)))) return null;
    }
    return { yp, trials, names, values: qs };
}

function solveSecond(E, x, y, conds) {
    const a = d(E, YPP);
    const b = d(E, YP);
    const c = d(E, y);
    const X = sym(x);
    if (![a, b, c].every((k) => free(k, x, y, YP, YPP))) return null;
    const f = simpO(neg(add(E, neg(mul(a, sym(YPP))), neg(mul(b, sym(YP))), neg(mul(c, sym(y))))));
    if (containsVar(f, y) || containsVar(f, YP) || containsVar(f, YPP)) return null;
    const homog = isZ(f);
    const K = sym('k');
    const charEq = rel('=', add(mul(a, pow(K, N2)), mul(b, K), c), N0);
    const steps = [];
    steps.push(step({
        title: L('Линейное однородное уравнение с постоянными коэффициентами', 'A linear homogeneous equation with constant coefficients'),
        text: L('Ищем решения вида $y = e^{kx}$: подстановка даёт характеристическое уравнение.', 'Look for solutions $y = e^{kx}$: substituting gives the characteristic equation.'),
        tex: bt((l) => tex(simpO(charEq.lhs), l) + ' = 0'),
    }));
    const av = val(a, {});
    const bv = val(b, {});
    const cv = val(c, {});
    const D = bv * bv - 4 * av * cv;
    const Dn = simpO(add(mul(b, b), neg(mul(num(4), a, c))));
    const C1 = sym('C_1');
    const C2 = sym('C_2');
    let y1;
    let y2;
    let text;
    if (Math.abs(D) < 1e-12) {
        const k = simpO(div(neg(b), mul(N2, a)));
        y1 = pow(E_, mul(k, X));
        y2 = mul(X, pow(E_, mul(k, X)));
        steps.push(step({ title: L('Один корень кратности 2', 'A double root'), tex: bt((l) => `D = 0,\\quad k = ${tex(k, l)}`) }));
        text = L('Кратному корню $k$ соответствуют решения $e^{kx}$ и $xe^{kx}$.', 'A double root $k$ gives the solutions $e^{kx}$ and $xe^{kx}$.');
    } else if (D > 0) {
        const r = solveEquation(charEq, 'k', { steps: true });
        if (r.kind !== 'roots' || r.roots.length !== 2) return null;
        const [k1, k2] = r.roots.map((z) => z.node);
        y1 = pow(E_, mul(k1, X));
        y2 = pow(E_, mul(k2, X));
        steps.push(step({ title: L('Два действительных корня', 'Two real roots'), tex: bt((l) => `k_1 = ${tex(k1, l)},\\quad k_2 = ${tex(k2, l)}`), sub: r.steps.slice(0, -1) }));
        text = L('Разным корням соответствуют решения $e^{k_1 x}$ и $e^{k_2 x}$.', 'Distinct roots give the solutions $e^{k_1 x}$ and $e^{k_2 x}$.');
    } else {
        const al = simpO(div(neg(b), mul(N2, a)));
        const be = simpO(div(pow(neg(Dn), num(Q.HALF)), mul(N2, a)));
        const ex = isZ(al) ? null : pow(E_, mul(al, X));
        const cosN = fn('cos', mul(be, X));
        const sinN = fn('sin', mul(be, X));
        y1 = ex ? mul(ex, cosN) : cosN;
        y2 = ex ? mul(ex, sinN) : sinN;
        steps.push(step({ title: L('Комплексные корни', 'Complex roots'), tex: bt((l) => `D = ${tex(Dn, l)} < 0,\\quad k = ${tex(al, l)} \\pm ${tex(be, l)}\\,i`) }));
        text = L('Корням $\\alpha \\pm \\beta i$ соответствуют решения $e^{\\alpha x}\\cos\\beta x$ и $e^{\\alpha x}\\sin\\beta x$.', 'The roots $\\alpha \\pm \\beta i$ give $e^{\\alpha x}\\cos\\beta x$ and $e^{\\alpha x}\\sin\\beta x$.');
    }
    y1 = simpO(y1);
    y2 = simpO(y2);
    const cm = (c, f) => (numValue(f)?.isOne() ? c : f.type === 'mul' ? mul(c, ...f.args) : mul(c, f));
    const general0 = add(cm(C1, y1), cm(C2, y2));
    steps.push(step({ title: homog ? L('Общее решение', 'The general solution') : L('Общее решение однородного уравнения', 'The general solution of the homogeneous equation'), tex: bt((l) => `${homog ? y : `${y}_{0}`} = ${tex(general0, l)}`), text }));
    // a right-hand side: variation of parameters, y_p = −y₁∫y₂f/(aW) + y₂∫y₁f/(aW), W = y₁y₂' − y₁'y₂
    let yp = null;
    const uc = homog ? null : undetermined(a, b, c, f, x);
    if (uc) {
        yp = uc.yp;
        const trialNode = add(uc.trials.map((t) => t.node));
        const sNote = uc.trials.filter((t) => t.s > 0);
        steps.push(step({
            title: L('Частное решение по виду правой части', 'A particular solution from the form of the right-hand side'),
            tex: bt((l) => `${y}_{${l === 'ru' ? '\\text{ч}' : 'p'}} = ${tex(trialNode, l)}`),
            text: sNote.length
                ? L(`Правая часть — многочлен на экспоненту (синус, косинус), поэтому частное решение ищем в том же виде. Число $${tex(simpO(add(num(sNote[0].g.alpha), mul(num(sNote[0].g.beta), sym('i')))))}$ — корень характеристического уравнения кратности ${sNote[0].s}, поэтому добавлен множитель $x${sNote[0].s > 1 ? '^' + sNote[0].s : ''}$.`, `The right-hand side is a polynomial times an exponential (sine, cosine), so a particular solution has the same form. The number $${tex(simpO(add(num(sNote[0].g.alpha), mul(num(sNote[0].g.beta), sym('i')))), 'en')}$ is a characteristic root of multiplicity ${sNote[0].s}, hence the factor $x${sNote[0].s > 1 ? '^' + sNote[0].s : ''}$.`)
                : L('Правая часть — многочлен на экспоненту (синус, косинус), поэтому частное решение ищем в том же виде с неизвестными коэффициентами.', 'The right-hand side is a polynomial times an exponential (sine, cosine), so a particular solution has the same form with unknown coefficients.'),
        }));
        steps.push(step({
            title: L('Подставляем в уравнение и приравниваем коэффициенты', 'Substitute and match the coefficients'),
            tex: bt((l) => `${uc.names.map((nm, i) => `${nm} = ${uc.values[i].toTex(l)}`).join(',\\ ')} \\;\\Rightarrow\\; ${y}_{${l === 'ru' ? '\\text{ч}' : 'p'}} = ${tex(yp, l)}`),
        }));
    } else if (!homog) {
        const W = tidy(add(mul(y1, d(y2, x)), neg(mul(d(y1, x), y2))));
        if (isZ(W)) return null;
        const g = simpO(div(f, a));
        const i1 = integrate(tidy(div(mul(y2, g), W)), x, { steps: true });
        const i2 = integrate(tidy(div(mul(y1, g), W)), x, { steps: true });
        if (!i1.result || !i2.result) return null;
        yp = tidy(add(neg(mul(y1, i1.result)), mul(y2, i2.result)));
        steps.push(step({
            title: L('Частное решение: вариация постоянных', 'A particular solution: variation of parameters'),
            tex: bt((l) => `W = ${tex(W, l)},\\quad ${y}_{\\text{ч}} = -${tex(y1, l)}\\int \\frac{${tex(y2, l)} \\cdot ${tex(g, l)}}{W}\\,d${x} + ${tex(y2, l)}\\int \\frac{${tex(y1, l)} \\cdot ${tex(g, l)}}{W}\\,d${x} = ${tex(yp, l)}`.replace('\\text{ч}', l === 'ru' ? '\\text{ч}' : 'p')),
            text: L('Ищем решение в виде $C_1(x)y_1 + C_2(x)y_2$: условие $C_1\'y_1 + C_2\'y_2 = 0$ и уравнение дают $C_1\' = -\\frac{y_2 f}{aW}$, $C_2\' = \\frac{y_1 f}{aW}$ ($W$ — определитель Вронского).', 'Look for $C_1(x)y_1 + C_2(x)y_2$: the condition $C_1\'y_1 + C_2\'y_2 = 0$ and the equation give $C_1\' = -\\frac{y_2 f}{aW}$, $C_2\' = \\frac{y_1 f}{aW}$ ($W$ is the Wronskian).'),
        }));
    }
    const general = yp ? add([...general0.args, ...(yp.type === 'add' ? yp.args : [yp])]) : general0;
    if (yp) steps.push(step({ title: L('Общее решение', 'The general solution'), tex: bt((l) => `${y} = ${tex(general, l)}`), text: L('Общее решение неоднородного уравнения = общее решение однородного + частное решение.', 'The general solution = the general solution of the homogeneous equation + a particular solution.') }));
    const res = { general, steps, type: uc ? 'undetermined-coefficients' : yp ? 'variation-of-parameters' : 'constant-coefficients' };
    const c0 = conds.find((z) => z.order === 0);
    const c1 = conds.find((z) => z.order === 1);
    if (!c0 || !c1) return res;
    // C₁y₁(x₀) + C₂y₂(x₀) = y₀, C₁y₁'(x₀) + C₂y₂'(x₀) = y₁ (Cramer)
    const at = (n, p) => simpO(substitute(n, { [x]: p }));
    const m11 = at(y1, c0.at);
    const m12 = at(y2, c0.at);
    const m21 = at(d(y1, x), c1.at);
    const m22 = at(d(y2, x), c1.at);
    const det = simpO(add(mul(m11, m22), neg(mul(m12, m21))));
    if (Math.abs(val(det, {})) < 1e-12) return null;
    // with a particular solution the right-hand sides shift by y_p(x₀), y_p'(x₀)
    const r0 = yp ? simpO(add(c0.value, neg(at(yp, c0.at)))) : c0.value;
    const r1 = yp ? simpO(add(c1.value, neg(at(d(yp, x), c1.at)))) : c1.value;
    const k1 = simpO(div(add(mul(r0, m22), neg(mul(m12, r1))), det));
    const k2 = simpO(div(add(mul(m11, r1), neg(mul(r0, m21))), det));
    const Y = tidy(add([mul(k1, y1), mul(k2, y2), ...(yp ? [yp] : [])]));
    steps.push(step({
        title: L('Начальные условия', 'The initial conditions'),
        tex: bt((l) => `\\begin{cases} ${tex(add(mul(C1, m11), mul(C2, m12)), l)} = ${tex(r0, l)} \\\\ ${tex(add(mul(C1, m21), mul(C2, m22)), l)} = ${tex(r1, l)} \\end{cases} \\;\\Rightarrow\\; C_1 = ${tex(k1, l)},\\ C_2 = ${tex(k2, l)}`),
        text: L(`Подставляем $x = ${tex(c0.at)}$ в решение и в его производную.`, `Substitute $x = ${tex(c0.at, 'en')}$ into the solution and its derivative.`),
    }));
    return { ...res, expr: Y };
}

/* ------------------------------------------------------------------ shared ending */

function finish(o) {
    const { cond, x, y, steps } = o;
    const res = { general: o.general, steps, type: o.type, implicit: !!o.implicit };
    if (!cond) return res;
    // the constant from y(x₀) = y₀
    const x0 = cond.at;
    const y0 = cond.value;
    let c0 = null;
    if (o.constFromIc) c0 = o.constFromIc(x0, y0);
    else if (o.lnForm) c0 = simpO(div(y0, pow(E_, substitute(o.F, { [x]: x0 }))));
    else if (o.type === 'separable' && o.G) c0 = simpO(add(substitute(o.G, { [y]: y0 }), neg(substitute(o.F, { [x]: x0 }))));
    else {
        // the solution is linear in C: C = (y₀ − Y(x₀; 0)) / (Y(x₀; 1) − Y(x₀; 0))
        const Y0 = o.solveC(N0);
        const Y1 = o.solveC(N1);
        if (!Y0 || !Y1) return res;
        const a0 = simpO(substitute(Y0, { [x]: x0 }));
        const a1 = simpO(substitute(Y1, { [x]: x0 }));
        const slope = simpO(add(a1, neg(a0)));
        if (Math.abs(val(slope, {})) < 1e-12) return res;
        c0 = simpO(div(add(y0, neg(a0)), slope));
        // check linearity in C at another value
        const Y2 = o.solveC(N2);
        if (!Y2 || Math.abs(val(substitute(Y2, { [x]: x0 }), {}) - (val(a0, {}) + 2 * val(slope, {}))) > 1e-9) c0 = null;
    }
    if (!c0) return res;
    const Y = o.solveC(c0);
    if (!Y) return res;
    steps.push(step({ title: L('Начальное условие', 'The initial condition'), tex: bt((l) => `${y}(${tex(x0, l)}) = ${tex(y0, l)} \\;\\Rightarrow\\; C = ${tex(c0, l)}`) }));
    return { ...res, expr: tidy(Y) };
}

/**
 * Solve an ordinary differential equation (first order, or second order linear with constant coefficients),
 * with initial conditions after «;».
 */
export function solveOde(input, opts = {}) {
    const lang = opts.lang === 'en' ? 'en' : 'ru';
    let inp;
    try {
        inp = readInput(typeof input === 'object' && input?.task ? input.task : input);
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        return { kind: 'unsupported', reason: e.msg, steps: [] };
    }
    const { eq, conds, x, y } = inp;
    const E = simpO(add(eq.lhs, neg(eq.rhs)));
    const order = containsVar(E, YPP) ? 2 : 1;
    let r = null;
    try {
        if (order === 1) r = solveFirst(E, x, y, conds.find((c) => c.order === 0) ?? null, eq.lhs.type === 'sym' && eq.lhs.name === YP && !containsVar(eq.rhs, YP));
        else r = solveSecond(E, x, y, conds);
    } catch (e) {
        if (!(e instanceof MathError)) throw e;
        r = null;
    }
    if (!r) return { kind: 'unsupported', reason: L('Такой тип уравнения пока не поддерживается.', 'This kind of equation is not supported yet.'), steps: [] };
    const eqDisp = substitute(eq, { [YP]: sym(`${y}'`), [YPP]: sym(`${y}''`) });
    const steps = [step({ title: L('Уравнение', 'The equation'), tex: bt((l) => tex(eqDisp, l)) }), ...r.steps];
    // the check: substitute back
    if (r.expr && !satisfies({ lhs: E, rhs: N0 }, r.expr, x, y)) return { kind: 'unsupported', reason: L('Не удалось проверить решение.', 'Could not verify the solution.'), steps: [] };
    if (r.expr) {
        for (const c of conds) {
            const Yc = c.order === 0 ? r.expr : c.order === 1 ? d(r.expr, x) : d(d(r.expr, x), x);
            if (Math.abs(val(Yc, { [x]: val(c.at, {}) }) - val(c.value, {})) > 1e-8) return { kind: 'unsupported', reason: L('Решение не удовлетворяет начальному условию.', 'The solution does not meet the initial condition.'), steps: [] };
        }
    }
    const answer = r.expr ?? r.general;
    const answerTex = r.implicit && !r.expr ? bt((l) => tex(answer, l)) : bt((l) => `${y} = ${tex(answer, l)}`);
    steps.push(step({ title: L('Ответ', 'Answer'), tex: answerTex }));
    steps[steps.length - 1].final = true;
    return {
        kind: r.expr ? 'solution' : 'general',
        expr: r.expr ?? null,
        general: r.general,
        type: r.type,
        steps,
        tex: answerTex,
        text: toText(answer, { lang: 'en' }),
    };
}
