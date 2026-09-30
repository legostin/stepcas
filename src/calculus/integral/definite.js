// integral/definite — definite integrals: Newton–Leibniz with jumps and singular points, improper integrals as
// limits, numeric values marked ≈, and the area between two curves.

import { sym, neg, isConst, containsVar, fn, nodeChildren, num, mul, substitute, freeVars, add } from '../../core/ast.js';
import { evaluate, compile } from '../../core/evaluate.js';
import { MathError, Q } from '../../core/rational.js';
import { Poly } from '../../core/poly.js';
import { numFindRoots, numIntegrate } from '../../numbers/numeric.js';
import { limit } from '../limit.js';
import { step } from '../../core/steps.js';
import { niceForm, prettyForm } from '../derivative.js';
import { N0, PI, T_, asNode, bt, isNum, paren, q, simp, trySimp, tx } from './common.js';
import { answerStep, checkExpr, integrate } from './integrate.js';

// ---------------------------------------------------------------- definite integrals

function boundNode(x) {
    if (x === Infinity) return sym('inf');
    if (x === -Infinity) return neg(sym('inf'));
    return asNode(x);
}

function boundValue(n) {
    const s = trySimp(n) ?? n;
    if (isConst(s) && s.name === 'inf') return { node: s, x: Infinity };
    if (s.type === 'mul' && s.args.length === 2 && isNum(s.args[0]) && s.args[0].value.isNeg() && isConst(s.args[1]) && s.args[1].name === 'inf') return { node: s, x: -Infinity };
    const x = evaluate(s);
    if (!Number.isFinite(x)) throw new MathError({ ru: 'Пределы интегрирования — числа или ±∞', en: 'The limits of integration must be numbers or ±∞' }, null, null, 'range');
    return { node: s, x };
}

const boundTex = (b, L) => (b.x === Infinity ? '+\\infty' : b.x === -Infinity ? '-\\infty' : tx(b.node, L));

/** Candidate singular points of g on [lo, hi]: zeros of denominators and of log arguments, poles of tg/ctg/sec/cosec. */
function singularCandidates(g, v, lo, hi) {
    const bases = [];
    const walk = (n) => {
        if (n.type === 'pow' && isNum(n.exp) && n.exp.value.isNeg() && containsVar(n.base, v)) bases.push(n.base);
        if (n.type === 'fn' && (n.name === 'ln' || n.name === 'lg') && containsVar(n.args[0], v)) bases.push(n.args[0]);
        if (n.type === 'fn' && n.name === 'log' && containsVar(n.args[1], v)) bases.push(n.args[1]);
        if (n.type === 'fn' && (n.name === 'tan' || n.name === 'sec') && containsVar(n.args[0], v)) bases.push(fn('cos', n.args[0]));
        if (n.type === 'fn' && (n.name === 'cot' || n.name === 'csc') && containsVar(n.args[0], v)) bases.push(fn('sin', n.args[0]));
        if (n.type === 'fn' && n.name === 'abs' && containsVar(n.args[0], v)) bases.push(n.args[0]);
        nodeChildren(n).forEach(walk);
    };
    walk(g);
    const wl = Number.isFinite(lo) ? lo : -1000;
    const wh = Number.isFinite(hi) ? hi : 1000;
    const pts = [];
    for (const B of bases) {
        const P = Poly.fromNode(B, v);
        if (P && P.degree >= 1) {
            for (const { root } of P.rationalRoots()) {
                const x = root.toNumber();
                if (x >= wl && x <= wh) pts.push({ x, node: num(root) });
            }
        }
        let bc;
        try {
            bc = compile(B, [v]);
        } catch {
            continue;
        }
        try {
            for (const r of numFindRoots(bc, wl, wh, { samples: 2000 })) {
                if (r.kind === 'interval') continue;
                pts.push({ x: r.x, node: null });
            }
        } catch {
            // no roots found numerically
        }
    }
    return mergePoints(pts);
}

function mergePoints(list) {
    const sorted = [...list].sort((a, b) => a.x - b.x);
    const out = [];
    for (const p of sorted) {
        const last = out[out.length - 1];
        if (last && Math.abs(last.x - p.x) <= 1e-7 * Math.max(1, Math.abs(p.x))) {
            if (!last.node && p.node) out[out.length - 1] = p;
            continue;
        }
        out.push(p);
    }
    return out;
}

/** Points of [l, h] where F jumps although f stays bounded (a numeric scan refined by bisection). */
function jumpsOf(Fc, fc, l, h) {
    const N = 2000;
    const out = [];
    let prev = null;
    for (let i = 0; i <= N; i++) {
        const x = l + ((h - l) * (i + 0.37)) / (N + 1);
        const y = Fc(x);
        if (prev && Number.isFinite(y) && Number.isFinite(prev.y)) {
            const slope = Math.max(Math.abs(fc(x)), Math.abs(fc(prev.x)), Math.abs(fc((x + prev.x) / 2)), 1);
            if (Math.abs(y - prev.y) > 50 * slope * (x - prev.x) + 1e-6) {
                let a = prev.x;
                let b = x;
                const ya = prev.y;
                for (let k = 0; k < 80; k++) {
                    const m = (a + b) / 2;
                    const ym = Fc(m);
                    if (Number.isFinite(ym) && Math.abs(ym - ya) < Math.abs(Fc(b) - ym)) a = m;
                    else b = m;
                }
                out.push({ x: (a + b) / 2, node: null });
            }
        }
        prev = { x, y };
    }
    return out;
}

/** Snap a numeric point to a nice exact node (integers, simple fractions, multiples of π/12). */
function exactPoint(x) {
    for (const d of [1, 2, 3, 4, 5, 6, 8, 10, 12]) {
        const n = Math.round(x * d);
        if (Math.abs(n / d - x) < 1e-9 * Math.max(1, Math.abs(x))) return num(new Q(BigInt(n), BigInt(d)));
    }
    const k = Math.round((x / Math.PI) * 12);
    if (Math.abs((k / 12) * Math.PI - x) < 1e-9) return simp(mul(num(new Q(BigInt(k), 12n)), PI));
    return null;
}

/** Value of F at an end of a piece: exact substitution (unless forced), else a one-sided limit. */
function endValue(F, v, b, side, force) {
    if (Number.isFinite(b.x) && !force) {
        try {
            const s = simp(substitute(F, { [v]: b.node }));
            const x = evaluate(s);
            if (Number.isFinite(x)) return { kind: 'fin', node: s, x, how: 'subst' };
        } catch {
            // fall through to the limit
        }
    }
    const L = limit(F, v, b.node, { side });
    if (L.value === 'inf' || L.value === '-inf') return { kind: L.value, how: 'limit', lim: L };
    if (L.value && typeof L.value === 'object') {
        const x = evaluate(L.value);
        if (Number.isFinite(x)) return { kind: 'fin', node: L.value, x, how: 'limit', lim: L };
    }
    return { kind: 'unknown', how: 'limit', lim: L };
}

function numericValue(fc, lo, hi) {
    try {
        const r = numIntegrate(fc, lo, hi, { info: true });
        return Number.isFinite(r.value) ? r : null;
    } catch {
        return null;
    }
}

/** The numeric value with a convergence verdict ({value, ok, divergent, reason}), or null. */
function checkedValue(fc, lo, hi) {
    try {
        return numIntegrate(fc, lo, hi, { info: true, check: true });
    } catch {
        return null;
    }
}

/** For an improper integral computed numerically: do the partial integrals settle as the cut-off moves out? */
function improperSettles(fc, lo, hi) {
    const val = (a, b) => numericValue(fc, a, b)?.value ?? NaN;
    const seq = [];
    if (!Number.isFinite(hi) || !Number.isFinite(lo)) {
        for (const R of [1e2, 1e4, 1e6]) seq.push(val(Number.isFinite(lo) ? lo : -R, Number.isFinite(hi) ? hi : R));
    } else {
        const w = hi - lo;
        const l0 = !Number.isFinite(fc(lo)) || poleAt(fc, lo);
        const h0 = !Number.isFinite(fc(hi)) || poleAt(fc, hi);
        for (const e of [1e-2, 1e-4, 1e-6]) seq.push(val(l0 ? lo + e * w : lo, h0 ? hi - e * w : hi));
    }
    if (!seq.every(Number.isFinite)) return false;
    const d1 = Math.abs(seq[1] - seq[0]);
    const d2 = Math.abs(seq[2] - seq[1]);
    return d2 <= 1e-3 * Math.max(1, Math.abs(seq[2])) && d2 <= d1;
}

const poleAt = (fc, x) => {
    const d = 1e-8 * Math.max(1, Math.abs(x));
    const yl = fc(x - d);
    const yr = fc(x + d);
    return !Number.isFinite(yl) || !Number.isFinite(yr) || Math.abs(yl) > 1e6 || Math.abs(yr) > 1e6;
};

/**
 * ∫ₐᵇ f dv. a, b: numbers, strings or nodes (inf / -inf allowed). opts: {steps}.
 * → {value: node | 'inf' | '-inf' | null, numeric: number | null, exact: boolean, approx: boolean,
 *    converges: boolean | null, improper: boolean, antiderivative: node | null, method, steps, tex}.
 * Exact values come from Newton–Leibniz: the interval is split at the points where f blows up or the
 * antiderivative jumps, and every end of a piece that is infinite or singular is a one-sided limit of F
 * (an infinite limit means the integral diverges). The exact value is cross-checked numerically.
 * Otherwise a numeric value, marked ≈.
 */
// F(b′) − F(a′) against the quadrature on finite pieces [a′; b′] inside an improper interval (ends pulled in from
// infinity and away from poles): does the antiderivative really match f there?
function truncatedAgrees(F, fc, v, lo, hi, interior) {
    let Fc;
    try { Fc = compile(F, [v]); } catch { return false; }
    const ends = [lo, ...interior.filter((p) => p.pole), hi];
    for (let i = 0; i + 1 < ends.length; i++) {
        const a0 = ends[i].x, b0 = ends[i + 1].x;
        const tries = [];
        for (const far of [1e2, 1e4]) {
            const a = Number.isFinite(a0) ? a0 + (poleAt(fc, a0) ? 1e-3 * Math.max(1, Math.abs(a0)) : 0) : (Number.isFinite(b0) ? b0 : 0) - far;
            const b = Number.isFinite(b0) ? b0 - (poleAt(fc, b0) ? 1e-3 * Math.max(1, Math.abs(b0)) : 0) : (Number.isFinite(a0) ? a0 : 0) + far;
            if (!(b > a)) continue;
            let q;
            try { q = numIntegrate(fc, a, b, { tol: 1e-12 }); } catch { q = NaN; }
            const e = Fc(b) - Fc(a);
            if (!Number.isFinite(q) || !Number.isFinite(e)) return false;
            tries.push(Math.abs(q - e) <= 1e-7 * Math.max(1, Math.abs(e)));
        }
        if (!tries.length || !tries.every(Boolean)) return false;
    }
    return true;
}

export function integrateDefinite(node, v = 'x', a = 0, b = 1, opts = {}) {
    node = asNode(node);
    checkExpr(node);
    const f = simp(node);
    const A = boundValue(boundNode(a));
    const B = boundValue(boundNode(b));
    const steps = [];
    const wantSteps = !!opts.steps;
    const head = (L) => `\\int_{${boundTex(A, L)}}^{${boundTex(B, L)}} ${f.type === 'add' ? paren(tx(node, L)) : tx(node, L)}\\,d${v}`;
    if (wantSteps) {
        steps.push(step({
            title: T_('Что считаем', 'What we compute'),
            tex: bt(head),
            text: T_('Находим первообразную F и пользуемся формулой Ньютона — Лейбница: ∫ₐᵇ f dx = F(b) − F(a). Если предел бесконечен или функция на отрезке не ограничена, интеграл несобственный — вместо значений F берём пределы.',
                'Find an antiderivative F and use the Newton–Leibniz formula: ∫ₐᵇ f dx = F(b) − F(a). If a limit is infinite or the function is unbounded on the interval, the integral is improper and F is replaced by limits.'),
            rule: 'start',
        }));
    }
    const out = (o) => ({ value: null, numeric: null, exact: false, approx: false, converges: null, improper: false, antiderivative: null, method: null, steps, tex: null, ...o });
    if (A.x === B.x) {
        return out({ value: N0, numeric: 0, exact: true, converges: true, method: 'equal-limits', tex: bt((L) => `${head(L)} = 0`) });
    }
    const flip = A.x > B.x;
    const lo = flip ? B : A;
    const hi = flip ? A : B;
    const others = freeVars(f).filter((w) => w !== v);
    if (others.length) throw new MathError({ ru: `Для определённого интеграла нужны числовые значения букв: ${others.join(', ')}`, en: `A definite integral needs numeric values for: ${others.join(', ')}` }, null, null, 'unbound');
    const fc = compile(f, [v]);
    // domain: f must be defined almost everywhere on the interval
    const pa = Number.isFinite(lo.x) ? lo.x : Math.min(-1, hi.x - 1000);
    const pb = Number.isFinite(hi.x) ? hi.x : Math.max(1, lo.x + 1000);
    let nan = 0;
    for (let i = 1; i < 200; i++) if (Number.isNaN(fc(pa + ((pb - pa) * i) / 200))) nan++;
    if (nan > 4) {
        return out({
            method: 'undefined',
            steps: wantSteps ? [step({ title: T_('Функция не определена', 'The function is not defined'), text: T_('Подынтегральная функция не определена на части отрезка интегрирования, поэтому такой интеграл (в действительных числах) не имеет смысла.', 'The integrand is undefined on part of the interval, so this integral makes no sense over the reals.'), rule: 'fail' })] : [],
        });
    }
    const inside = (x) => x > lo.x + 1e-9 * Math.max(1, Math.abs(lo.x)) && x < hi.x - 1e-9 * Math.max(1, Math.abs(hi.x));
    const fPoles = singularCandidates(f, v, lo.x, hi.x).filter((p) => inside(p.x) && poleAt(fc, p.x));
    let improper = !Number.isFinite(lo.x) || !Number.isFinite(hi.x) || !Number.isFinite(fc(lo.x)) || !Number.isFinite(fc(hi.x)) || poleAt(fc, lo.x) || poleAt(fc, hi.x) || fPoles.length > 0;
    const anti = integrate(node, v, { steps: wantSteps });
    let exactNode = null;
    let diverges = null;
    let unknown = false;
    let interior = fPoles;
    let parts = [];
    if (anti.result) {
        const F = anti.result;
        const Fs = trySimp(F) ?? F;
        let Fc = null;
        try {
            Fc = compile(Fs, [v]);
        } catch {
            Fc = null;
        }
        let cand = [...fPoles, ...singularCandidates(Fs, v, lo.x, hi.x).filter((p) => inside(p.x))];
        if (Fc) {
            const l = Number.isFinite(lo.x) ? lo.x : Math.min(hi.x, 0) - 100;
            const h = Number.isFinite(hi.x) ? hi.x : Math.max(lo.x, 0) + 100;
            cand.push(...jumpsOf(Fc, fc, l, h).filter((p) => inside(p.x)));
        }
        cand = mergePoints(cand);
        // keep the points where F is not continuous (or f blows up); a point needs an exact position
        interior = [];
        for (const p of cand) {
            const d = 1e-7 * Math.max(1, Math.abs(p.x));
            const yl = Fc ? Fc(p.x - d) : NaN;
            const yr = Fc ? Fc(p.x + d) : NaN;
            const smooth = Number.isFinite(yl) && Number.isFinite(yr) && Math.abs(yl - yr) < 1e-5 * Math.max(1, Math.abs(yl)) && !poleAt(fc, p.x);
            if (smooth) continue;
            const nodeX = p.node ?? exactPoint(p.x);
            if (!nodeX) {
                unknown = true;
                break;
            }
            interior.push({ x: p.x, node: nodeX, pole: poleAt(fc, p.x) });
        }
        if (!unknown) {
            const pts = [lo, ...interior, hi];
            for (let i = 0; i + 1 < pts.length; i++) {
                const p = pts[i];
                const r = pts[i + 1];
                const forceTop = i + 1 < pts.length - 1 || !Number.isFinite(fc(r.x)) || poleAt(fc, r.x);
                const forceBot = i > 0 || !Number.isFinite(fc(p.x)) || poleAt(fc, p.x);
                const top = endValue(F, v, r, 'left', forceTop);
                const bot = endValue(F, v, p, 'right', forceBot);
                parts.push({ p, r, top, bot });
                if (['inf', '-inf'].includes(top.kind) || ['inf', '-inf'].includes(bot.kind)) diverges = diverges ?? { p, r, top, bot };
                if (top.kind === 'unknown' || bot.kind === 'unknown') unknown = true;
            }
            if (!diverges && !unknown) {
                exactNode = trySimp(add(parts.map((x) => add(x.top.node, neg(x.bot.node)))));
                if (exactNode && flip) exactNode = trySimp(neg(exactNode));
            }
        }
        if (interior.some((p) => p.pole)) improper = true;
        if (wantSteps && (exactNode || diverges)) {
            steps.push(step({
                title: T_('Первообразная', 'Antiderivative'),
                tex: bt((L) => `F(${v}) = ${tx(F, L)}`),
                rule: 'antiderivative',
                sub: anti.steps.filter((s) => s.rule !== 'answer' && s.rule !== 'start'),
            }));
            if (flip) {
                steps.push(step({
                    title: T_('Меняем пределы местами', 'Swap the limits'),
                    tex: bt((L) => `\\int_{${boundTex(A, L)}}^{${boundTex(B, L)}} = -\\int_{${boundTex(B, L)}}^{${boundTex(A, L)}}`),
                    text: T_('Нижний предел больше верхнего: переставляем пределы и меняем знак.', 'The lower limit is larger than the upper one: swap them and change the sign.'),
                    rule: 'swap',
                }));
            }
            if (interior.length) {
                const poles = interior.some((p) => p.pole);
                steps.push(step({
                    title: poles ? T_('Особые точки внутри отрезка', 'Singular points inside the interval') : T_('Разрыв первообразной', 'A jump of the antiderivative'),
                    tex: bt((L) => `${v} = ${interior.map((p) => tx(p.node, L)).join(L === 'ru' ? ';\\ ' : ',\\ ')}`),
                    text: poles
                        ? T_('Внутри отрезка функция обращается в бесконечность. Формулу Ньютона — Лейбница через такую точку применять нельзя: разбиваем интеграл на части и каждую считаем как несобственный интеграл (через пределы).',
                            'The function blows up inside the interval. Newton–Leibniz cannot be applied across such a point: split the integral and treat each part as an improper integral (through limits).')
                        : T_('Найденная первообразная делает скачок внутри отрезка (так бывает после замены t = tg(x/2)). Разбиваем отрезок в этой точке и на каждой части берём пределы первообразной.',
                            'The antiderivative jumps inside the interval (this happens after the substitution t = tan(x/2)). Split the interval there and take limits of the antiderivative on each part.'),
                    rule: 'split',
                }));
            }
            for (const x of parts) {
                const lim = (e, pt, sideSign) => (e.how === 'limit' ? `\\lim_{${v} \\to ${Number.isFinite(pt.x) ? `{${tx(pt.node, 'en')}}^{${sideSign}}` : boundTex(pt, 'en')}} F(${v})` : null);
                const val = (e) => (e.kind === 'fin' ? null : e.kind === 'inf' ? '+\\infty' : e.kind === '-inf' ? '-\\infty' : '?');
                const isLim = x.top.how === 'limit' || x.bot.how === 'limit';
                steps.push(step({
                    title: isLim ? T_('Несобственный интеграл: пределы', 'Improper integral: limits') : T_('Формула Ньютона — Лейбница', 'Newton–Leibniz formula'),
                    tex: bt((L) => {
                        const upper = x.top.kind === 'fin' ? tx(x.top.node, L) : val(x.top);
                        const lower = x.bot.kind === 'fin' ? tx(x.bot.node, L) : val(x.bot);
                        const lu = lim(x.top, x.r, '-') ?? `F\\left(${boundTex(x.r, L)}\\right)`;
                        const ll = lim(x.bot, x.p, '+') ?? `F\\left(${boundTex(x.p, L)}\\right)`;
                        const both = x.top.kind === 'fin' && x.bot.kind === 'fin' ? trySimp(add(x.top.node, neg(x.bot.node))) : null;
                        return `\\int_{${boundTex(x.p, L)}}^{${boundTex(x.r, L)}} f\\,d${v} = ${lu} - ${ll} = ${upper} - ${/^-/.test(lower) ? `\\left(${lower}\\right)` : lower}${both ? ` = ${tx(niceForm(both), L)}` : ''}`;
                    }),
                    text: isLim
                        ? T_('На бесконечном пределе, в точке, где функция не ограничена, или в точке скачка первообразной её значение заменяем односторонним пределом.', 'At an infinite limit, at a point where the function is unbounded, or where the antiderivative jumps, its value is replaced by a one-sided limit.')
                        : T_('Первообразная непрерывна на отрезке, поэтому интеграл равен F(b) − F(a).', 'The antiderivative is continuous on the interval, so the integral equals F(b) − F(a).'),
                    rule: 'newton-leibniz',
                }));
            }
        }
    }
    if (diverges) {
        const signOf = (k) => (k === 'inf' ? 1 : k === '-inf' ? -1 : 0);
        const contributions = parts.map((x) => signOf(x.top.kind) - signOf(x.bot.kind)).filter((c) => c !== 0);
        const same = contributions.length && contributions.every((c) => Math.sign(c) === Math.sign(contributions[0]));
        const val = same ? ((flip ? -1 : 1) * Math.sign(contributions[0]) > 0 ? 'inf' : '-inf') : null;
        const tex = bt((L) => `${head(L)}\\ ${L === 'ru' ? '\\text{расходится}' : '\\text{diverges}'}`);
        if (wantSteps) {
            const s = answerStep(T_('Интеграл расходится', 'The integral diverges'), tex);
            s.text = T_('Предел первообразной бесконечен, значит, несобственный интеграл расходится (площадь под графиком бесконечна).', 'The limit of the antiderivative is infinite, so the improper integral diverges (the area under the graph is infinite).');
            steps.push(s);
        }
        return out({ value: val, converges: false, improper: true, antiderivative: anti.result, method: 'improper', tex });
    }
    // numeric value: for the cross-check, or as the answer
    const cuts = [lo, ...mergePoints([...interior, ...fPoles]).filter((p) => inside(p.x)), hi];
    let numeric = 0;
    let numOk = true;
    let checked = true; // every piece passed the numeric convergence check
    let numDiverges = null; // a piece the check calls divergent
    for (let i = 0; i + 1 < cuts.length; i++) {
        const piece = checkedValue(fc, cuts[i].x, cuts[i + 1].x);
        if (piece?.divergent) numDiverges = numDiverges ?? piece;
        if (!piece?.ok) checked = false;
        const res = piece && Number.isFinite(piece.value) ? piece : numericValue(fc, cuts[i].x, cuts[i + 1].x);
        if (!res) {
            numOk = false;
            break;
        }
        numeric += res.value;
    }
    if (flip) numeric = -numeric;
    if (improper && !exactNode && numDiverges) {
        // no exact verdict (the limit of F does not exist, or there is no F), but the tail visibly does not settle
        const s = numDiverges.value === Infinity ? 1 : numDiverges.value === -Infinity ? -1 : 0;
        const val = s ? ((flip ? -s : s) > 0 ? 'inf' : '-inf') : null;
        const tex = bt((L) => `${head(L)}\ ${L === 'ru' ? '\text{расходится}' : '\text{diverges}'}`);
        if (wantSteps) {
            const st = answerStep(T_('Интеграл расходится', 'The integral diverges'), tex);
            st.text = numDiverges.reason === 'pole'
                ? T_('Функция растёт у особой точки так быстро, что площадь рядом с ней бесконечна: интеграл расходится.', 'The function grows so fast near the singular point that the area there is infinite: the integral diverges.')
                : s ? T_('На бесконечности функция убывает недостаточно быстро: площадь под графиком бесконечна.', 'The function does not decay fast enough at infinity: the area under the graph is infinite.')
                    : T_('Интегралы по всё более длинным отрезкам не стремятся ни к какому числу: волны не затухают, и площадь под графиком то набирается, то убывает. Несобственный интеграл расходится.', 'The integrals over longer and longer intervals do not tend to any number: the waves do not die down, and the area keeps growing and shrinking. The improper integral diverges.');
            steps.push(st);
        }
        return out({ value: val, converges: false, improper: true, antiderivative: anti.result, method: 'improper-numeric', tex });
    }
    if (exactNode) {
        const ex = evaluate(exactNode);
        const tol = improper ? 1e-4 : 1e-6;
        // A slowly decaying tail (1/(x ln²x) on [e; ∞)) fools the quadrature: then check the antiderivative on a long
        // finite piece, where the numbers are reliable, instead of letting a bad number veto a verified answer.
        const agrees = Number.isFinite(ex) && (!numOk || Math.abs(ex - numeric) <= tol * Math.max(1, Math.abs(ex)) || (improper && truncatedAgrees(anti.result, fc, v, lo, hi, interior)));
        if (agrees) {
            const value = niceForm(exactNode);
            const tex = bt((L) => `${head(L)} = ${tx(value, L)}${isNum(trySimp(value) ?? value) && (trySimp(value) ?? value).value.isInt() ? '' : ` \\approx ${fmtNum(ex, L)}`}`);
            if (wantSteps) steps.push(answerStep(T_('Ответ', 'Answer'), tex));
            return out({ value, numeric: ex, exact: true, converges: true, improper, antiderivative: anti.result, method: improper ? 'improper' : interior.length ? 'newton-leibniz-pieces' : 'newton-leibniz', tex });
        }
    }
    const poles = fPoles.length > 0;
    const tailOk = !improper || exactNode || checked || improperSettles(fc, lo.x, hi.x);
    if (!numOk || !Number.isFinite(numeric) || (poles && !exactNode) || !tailOk) {
        if (wantSteps) {
            steps.push(step({
                title: T_('Не получилось', 'Not found'),
                text: poles || !tailOk
                    ? T_('Интеграл несобственный, а точно проверить его сходимость не удалось; численно он не устанавливается (похоже, расходится). Ненадёжное число не приводим.', 'The integral is improper and its convergence could not be checked exactly; numerically it does not settle (it seems to diverge). No unreliable number is given.')
                    : T_('Ни точно, ни численно посчитать этот интеграл не удалось (возможно, он расходится).', 'This integral could not be computed exactly or numerically (it may diverge).'),
                rule: 'fail',
            }));
        }
        return out({ improper, antiderivative: anti.result, method: 'failed' });
    }
    const tex = bt((L) => `${head(L)} \\approx ${fmtNum(numeric, L)}`);
    if (wantSteps) {
        if (!anti.result && anti.reason) steps.push(step({ title: T_('Первообразная', 'Antiderivative'), text: anti.reason, rule: 'antiderivative' }));
        steps.push(step({
            title: T_('Численное интегрирование', 'Numerical integration'),
            text: !anti.result
                ? T_('Первообразную в элементарных функциях найти не удалось, поэтому считаем интеграл численно (адаптивная квадратура Гаусса — Кронрода). Значение приближённое.', 'No elementary antiderivative was found, so the integral is computed numerically (adaptive Gauss–Kronrod quadrature). The value is approximate.')
                : T_('Точное значение подтвердить не удалось, поэтому приводим численное (приближённое).', 'The exact value could not be confirmed, so a numeric (approximate) value is given.'),
            rule: 'numeric',
        }));
        steps.push(answerStep(T_('Ответ (приближённо)', 'Answer (approximate)'), tex));
    }
    return out({ numeric, approx: true, converges: true, improper, antiderivative: anti.result, method: 'numeric', tex });
}

function fmtNum(x, L) {
    let s = x.toFixed(6);
    if (s.includes('.')) s = s.replace(/\.?0+$/, '');
    if (s === '-0') s = '0';
    return L === 'ru' ? s.replace('.', '{,}') : s;
}

/**
 * Area between y = f and y = g for v in [a, b] (∫|f − g|). a, b optional: then the outermost intersection
 * points are used. → {value: node | null, numeric, exact, approx, points: [nodes], pieces, steps, tex}.
 */
export function areaBetween(f, g, v = 'x', a = null, b = null, opts = {}) {
    f = asNode(f);
    g = asNode(g);
    const d = simp(add(f, neg(g)));
    const dc = compile(d, [v]);
    let lo;
    let hi;
    const cross = [];
    const P = Poly.fromNode(d, v);
    const exactRoots = P && P.degree >= 1 ? P.rationalRoots().map((r) => r.root) : null;
    if (a === null || b === null) {
        let roots;
        if (P && exactRoots && exactRoots.length >= 2) roots = exactRoots.map((r) => ({ node: num(r), x: r.toNumber() }));
        else roots = numFindRoots(dc, -50, 50).filter((r) => r.kind !== 'interval').map((r) => ({ node: exactPoint(r.x) ?? num(Q.of(r.x.toFixed(10))), x: r.x }));
        if (roots.length < 2) throw new MathError({ ru: 'Графики пересекаются меньше чем в двух точках — укажите границы', en: 'The graphs meet at fewer than two points: give the bounds' }, null, null, 'no-bounds');
        lo = roots[0];
        hi = roots[roots.length - 1];
    } else {
        lo = boundValue(boundNode(a));
        hi = boundValue(boundNode(b));
        if (lo.x > hi.x) [lo, hi] = [hi, lo];
    }
    for (const r of numFindRoots(dc, lo.x, hi.x)) {
        if (r.kind === 'interval' || r.x <= lo.x + 1e-9 || r.x >= hi.x - 1e-9) continue;
        const ex = exactRoots?.find((z) => Math.abs(z.toNumber() - r.x) < 1e-8);
        cross.push({ node: ex ? num(ex) : exactPoint(r.x) ?? num(Q.of(r.x.toFixed(12))), x: r.x });
    }
    const pts = [lo, ...cross, hi];
    const pieces = [];
    let total = null;
    let numeric = 0;
    let exact = true;
    const steps = [];
    for (let i = 0; i + 1 < pts.length; i++) {
        const p = pts[i];
        const r = pts[i + 1];
        const mid = dc((p.x + r.x) / 2);
        const upper = mid >= 0 ? d : simp(neg(d));
        const res = integrateDefinite(upper, v, p.node, r.node, { steps: false });
        pieces.push({ from: p.node, to: r.node, upper: mid >= 0 ? 'f' : 'g', value: res.value, numeric: res.numeric });
        if (!res.exact) exact = false;
        numeric += res.numeric ?? NaN;
        if (res.exact && total !== null) total = add(total, res.value);
        else if (res.exact && i === 0) total = res.value;
        else total = null;
    }
    const value = exact && total ? niceForm(total) : null;
    const tex = bt((L) => `S = \\int_{${tx(lo.node, L)}}^{${tx(hi.node, L)}} \\left|${tx(prettyForm(d), L)}\\right|\\,d${v} ${value ? '= ' + tx(value, L) : '\\approx ' + fmtNum(numeric, L)}`);
    if (opts.steps) {
        steps.push(step({
            title: T_('Разность функций', 'Difference of the functions'),
            tex: bt((L) => `f(${v}) - g(${v}) = ${tx(prettyForm(d), L)}`),
            text: T_('Площадь между графиками — интеграл от модуля разности: на каждом участке из верхней функции вычитаем нижнюю.', 'The area between the graphs is the integral of the absolute difference: on each piece subtract the lower function from the upper one.'),
            rule: 'difference',
        }));
        if (cross.length || a === null) {
            steps.push(step({
                title: T_('Точки пересечения', 'Intersection points'),
                tex: bt((L) => `${v} = ${pts.map((p) => tx(p.node, L)).join(L === 'ru' ? ';\\ ' : ',\\ ')}`),
                text: T_('Между точками пересечения разность сохраняет знак.', 'Between the intersection points the difference keeps its sign.'),
                rule: 'intersections',
            }));
        }
        for (const pc of pieces) {
            steps.push(step({
                title: T_('Участок', 'Piece'),
                tex: bt((L) => `\\int_{${tx(pc.from, L)}}^{${tx(pc.to, L)}} ${pc.upper === 'f' ? '(f - g)' : '(g - f)'}\\,d${v} = ${pc.value && typeof pc.value === 'object' ? tx(pc.value, L) : '\\approx ' + fmtNum(pc.numeric ?? NaN, L)}`),
                rule: 'piece',
            }));
        }
        steps.push(answerStep(T_('Площадь', 'Area'), tex));
    }
    return { value, numeric, exact: !!value, approx: !value, points: pts.map((p) => p.node), pieces, steps, tex };
}