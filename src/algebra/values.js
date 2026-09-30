// The value of a numeric expression step by step — the way a school solution goes (ЕГЭ task 7, ОГЭ, ЕНТ):
// one named rule per step, each shown as «before = after» with the reason.
//
//   evaluateSteps(input, {lang, maxSteps = 40}) → {value (node), approx, exact, steps}
//
// Rules, tried on the outermost node first: logarithms of one base added or subtracted, change of base, the
// basic identity a^(log_a b) = b (also when a is a power of the log's base), the log of a power of the base,
// powers brought to one base (or to primes) and multiplied, a power of a power, rational powers of exact
// powers, roots multiplied, squared or taken out, the difference of squares both ways, the square of a sum,
// trigonometric values through reduction formulas, the double angle, lowering the power. Between them plain
// arithmetic, one layer at a time; the engine's simplify last. The value is always the engine's exact value —
// the steps only explain how to get there, and a step that changes the value is never taken.
import { Q } from '../core/rational.js';
import { num, sym, add, mul, div, neg, pow, fn, nodeKey, freeVars, numValue, withChildren, nodeChildren, nodeSome } from '../core/ast.js';
import { parse } from '../core/parse.js';
import { toTex } from '../core/print.js';
import { L, step } from '../core/steps.js';
import { trySimplify, approx } from '../core/safe.js';

const TRIG = new Set(['sin', 'cos', 'tan', 'cot']);
const qv = (n) => numValue(n);
const isE = (n) => n?.type === 'sym' && n.name === 'e' && !n.var;
const same = (a, b) => nodeKey(trySimplify(a)) === nodeKey(trySimplify(b));
const tx = (n) => toTex(n);
const qt = (q) => q.toTex('ru');
const hasTrigOrLog = (n) => nodeSome(n, (m) => m.type === 'fn' && (TRIG.has(m.name) || m.name === 'log' || m.name === 'ln' || m.name === 'lg'));

/* ------------------------------------------------------------------ exact powers of rationals */

// q = p^M with the largest M (p is then not a perfect power) → {p, M}; q positive and ≠ 1
function primitive(q) {
    if (!q || !q.isPos() || q.isOne()) return null;
    const bits = Math.max(q.n.toString(2).length, q.d.toString(2).length);
    for (let M = Math.min(bits, 64); M >= 2; M--) {
        const r = q.exactRoot(M);
        if (r) return { p: r, M };
    }
    return { p: q, M: 1 };
}
// the integer n with p^n = q, or null
function intLog(p, q) {
    const n = Math.round(Math.log(q.toNumber()) / Math.log(p.toNumber()));
    if (!Number.isFinite(n) || Math.abs(n) > 4096) return null;
    try {
        return p.pow(n).eq(q) ? n : null;
    } catch {
        return null;
    }
}
// the rational k with base^k = q, or null (log_4 8 = 3/2, log_{1/4} 8 = −3/2, lg 0.001 = −3)
function logExact(base, q) {
    if (!base || !q || !q.isPos() || !base.isPos() || base.isOne()) return null;
    if (q.isOne()) return Q.ZERO;
    const pr = primitive(base);
    const n = intLog(pr.p, q);
    return n === null ? null : new Q(BigInt(n), BigInt(pr.M));
}
// prime factorisation of a positive rational → Map(prime bigint → exponent number), or null for big primes
function primeFactors(q) {
    const out = new Map();
    const run = (x, s) => {
        for (let p = 2n; p * p <= x && p < 100000n; p += p === 2n ? 1n : 2n) {
            while (x % p === 0n) {
                out.set(p, (out.get(p) ?? 0) + s);
                x /= p;
            }
        }
        if (x > 1n) {
            if (x >= 10000000000n) return false;
            out.set(x, (out.get(x) ?? 0) + s);
        }
        return true;
    };
    return q.isPos() && run(q.n, 1) && run(q.d, -1) ? out : null;
}
// a node as q^e with q, e rational: 8, √8, ∛8, 8^(2/3), 1/8 → {q, e}
function asQPow(n) {
    const v = qv(n);
    if (v) return { q: v, e: Q.ONE };
    if (n.type === 'fn' && n.name === 'sqrt' && qv(n.args[0])) return { q: qv(n.args[0]), e: new Q(1n, 2n) };
    if (n.type === 'fn' && n.name === 'cbrt' && qv(n.args[0])) return { q: qv(n.args[0]), e: new Q(1n, 3n) };
    if (n.type === 'fn' && n.name === 'root' && qv(n.args[0]) && qv(n.args[1])?.isInt()) return { q: qv(n.args[0]), e: Q.ONE.div(qv(n.args[1])) };
    if (n.type === 'pow' && qv(n.base) && qv(n.exp)) return { q: qv(n.base), e: qv(n.exp) };
    return null;
}
const powTex = (p, k) => (k.isOne() ? qt(p) : `${p.isInt() ? qt(p) : `\\left(${qt(p)}\\right)`}^{${qt(k)}}`);

/* ------------------------------------------------------------------ logarithms */

function logParts(n) {
    if (n?.type !== 'fn') return null;
    if (n.name === 'log') return { base: n.args[0], arg: n.args[1] };
    if (n.name === 'ln') return { base: sym('e'), arg: n.args[0] };
    if (n.name === 'lg') return { base: num(10), arg: n.args[0] };
    return null;
}
function mkLog(base, arg) {
    if (isE(base)) return fn('ln', arg);
    if (qv(base)?.eq(10)) return fn('lg', arg);
    return fn('log', base, arg);
}
// k·log (k a number) → {k, lp}
function scaledLog(t) {
    let sign = 1;
    let core = t;
    if (core.type === 'neg') {
        sign = -1;
        core = core.arg;
    }
    let k = Q.ONE;
    if (core.type === 'mul' && core.args.length === 2 && qv(core.args[0]) && logParts(core.args[1])) {
        k = qv(core.args[0]);
        core = core.args[1];
    }
    const lp = logParts(core);
    return lp ? { k: sign < 0 ? k.neg() : k, lp } : null;
}

const LOG_RULES = L('$\\log_a x + \\log_a y = \\log_a(xy)$, $\\log_a x - \\log_a y = \\log_a \\dfrac{x}{y}$, $k\\log_a x = \\log_a x^k$.');

// log_a x ± log_a y (± k log_a z) → log_a(x·y/z^k)
function ruleLogSum(n) {
    if (n.type !== 'add') return null;
    const terms = n.args.map((t) => ({ t, s: scaledLog(t) }));
    const logs = terms.filter((x) => x.s);
    for (const first of logs) {
        const group = logs.filter((x) => same(x.s.lp.base, first.s.lp.base));
        if (group.length < 2) continue;
        const top = [];
        const bottom = [];
        for (const { s } of group) {
            const a = s.k.abs().isOne() ? s.lp.arg : pow(s.lp.arg, num(s.k.abs()));
            (s.k.isNeg() ? bottom : top).push(a);
        }
        const upper = top.length ? mul(top) : num(1);
        const arg = bottom.length ? div(upper, mul(bottom)) : upper;
        const combined = mkLog(first.s.lp.base, arg);
        const rest = terms.filter((x) => !group.includes(x)).map((x) => x.t);
        return { node: rest.length ? add([combined, ...rest]) : combined, title: L('Сумма и разность логарифмов с одним основанием', 'Logarithms with one base added and subtracted'), text: LOG_RULES };
    }
    return null;
}

// log_c b / log_c a → log_a b
function ruleChangeBase(n) {
    if (n.type !== 'div') return null;
    const p = logParts(n.num);
    const q = logParts(n.den);
    if (!p || !q || !same(p.base, q.base)) return null;
    return { node: mkLog(q.arg, p.arg), title: L('Переход к новому основанию', 'Change of base'), text: L('$\\dfrac{\\log_c b}{\\log_c a} = \\log_a b$.') };
}

// B^(k·log_c b + r), B = c^m → b^(km) · B^r
function ruleLogIdentity(n) {
    if (n.type !== 'pow') return null;
    const B = qv(n.base);
    if (!B && !isE(n.base)) return null;
    const parts = n.exp.type === 'add' ? n.exp.args : [n.exp];
    let found = null;
    const rest = [];
    for (const t of parts) {
        const s = !found && scaledLog(t);
        if (s) {
            const m = isE(n.base) ? (isE(s.lp.base) ? Q.ONE : null) : logExact(qv(s.lp.base), B);
            if (m && !m.isZero()) {
                found = { ...s, m };
                continue;
            }
        }
        rest.push(t);
    }
    if (!found) return null;
    const e = found.k.mul(found.m);
    const main = e.isOne() ? found.lp.arg : pow(found.lp.arg, num(e));
    const node = rest.length ? mul(main, pow(n.base, add(rest))) : main;
    const c = tx(found.lp.base);
    const lines = [];
    if (!found.m.isOne()) lines.push(L(`Основание степени — степень основания логарифма: $${tx(n.base)} = ${c}^{${qt(found.m)}}$.`, `The base of the power is a power of the log's base: $${tx(n.base)} = ${c}^{${qt(found.m)}}$.`));
    lines.push(L('$a^{\\log_a b} = b$, поэтому $a^{k\\log_a b} = \\left(a^{\\log_a b}\\right)^k = b^k$.', '$a^{\\log_a b} = b$, so $a^{k\\log_a b} = \\left(a^{\\log_a b}\\right)^k = b^k$.'));
    if (rest.length) lines.push(L('Сумма в показателе: $a^{x + y} = a^x \\cdot a^y$.', 'A sum in the exponent: $a^{x + y} = a^x \\cdot a^y$.'));
    return { node, title: L('Основное логарифмическое тождество', 'The basic logarithmic identity'), text: L(lines.map((l) => l.ru).join(' '), lines.map((l) => l.en).join(' ')) };
}

// log_a(a^k) → k: log_2 8 = 3, lg 0.001 = −3, log_{1/4} 8 = −3/2, log_2 √8 = 3/2, ln e³ = 3
function ruleLogOfPower(n) {
    const lp = logParts(n);
    if (!lp) return null;
    if (isE(lp.base)) {
        if (isE(lp.arg)) return { node: num(1), title: L('Логарифм основания', 'The log of the base'), text: L('$\\ln e = 1$.') };
        if (lp.arg.type === 'pow' && isE(lp.arg.base)) return { node: lp.arg.exp, title: L('Логарифм степени основания', 'The log of a power of the base'), text: L('$\\ln e^k = k$.') };
        return null;
    }
    const b = qv(lp.base);
    // only a number as written (3, 1/9, √8, 2^5): an arithmetic argument is computed first
    const x = lp.arg;
    const simple = atomic(x) || (x.type === 'fn' && x.args.every(atomic)) || (x.type === 'pow' && atomic(x.base) && atomic(x.exp));
    const a = simple ? asQPow(x) : null;
    if (!b || !a) return null;
    const k0 = logExact(b, a.q);
    if (!k0) return null;
    const k = k0.mul(a.e);
    if (k.isOne()) return { node: num(1), title: L('Логарифм основания', 'The log of the base'), text: L('$\\log_a a = 1$.') };
    if (k.isZero()) return { node: num(0), title: L('Логарифм единицы', 'The log of one'), text: L('$\\log_a 1 = 0$.') };
    return {
        node: num(k),
        title: L('Логарифм степени основания', 'The log of a power of the base'),
        text: L(`$${tx(lp.arg)} = ${tx(pow(lp.base, num(k)))}$, а $\\log_a a^k = k$.`, `$${tx(lp.arg)} = ${tx(pow(lp.base, num(k)))}$, and $\\log_a a^k = k$.`),
    };
}

/* ------------------------------------------------------------------ powers and roots */

// factors of a product or a quotient with their signs (+1 upstairs, −1 downstairs)
function signedFactors(n) {
    const flat = (x) => (x.type === 'mul' ? x.args : [x]);
    if (n.type === 'mul') return n.args.map((f) => ({ f, s: 1 }));
    if (n.type === 'div') return [...flat(n.num).map((f) => ({ f, s: 1 })), ...flat(n.den).map((f) => ({ f, s: -1 }))];
    return null;
}

// products and quotients of powers: to one base (2^u · 8^v = 2^(u + 3v)) or, failing that, to primes
function rulePowers(n) {
    const fs = signedFactors(n);
    if (!fs) return null;
    const cand = fs.filter(({ f }) => f.type === 'pow' && qv(f.base)?.isPos() && !qv(f.base).isOne());
    if (cand.length < 2) return null;
    const bases = cand.map(({ f }) => qv(f.base));
    const allSame = bases.every((b) => b.eq(bases[0]));
    const anyFrac = cand.some(({ f }) => !qv(f.exp)?.isInt());
    if (!allSame && !anyFrac) return null; // 2^6 · 3^4 / 6^3 — plain arithmetic
    const term = (k, e, s) => {
        const t = k.isOne() ? e : qv(e) ? num(k.mul(qv(e))) : mul(num(k), e);
        return s < 0 ? neg(t) : t;
    };
    const others = fs.filter((x) => !cand.includes(x));
    const rebuild = (powers) => {
        const up = [...powers, ...others.filter((x) => x.s > 0).map((x) => x.f)];
        const down = others.filter((x) => x.s < 0).map((x) => x.f);
        return down.length ? div(mul(up), mul(down)) : mul(up);
    };
    const prims = bases.map(primitive);
    const p = allSame ? bases[0] : prims.every((x) => x.p.eq(prims[0].p)) ? prims[0].p : null;
    if (p) {
        const exps = cand.map(({ f, s }, i) => term(allSame ? Q.ONE : new Q(BigInt(prims[i].M)), f.exp, s));
        const conv = allSame ? [] : [...new Set(bases.filter((b) => !b.eq(p)).map((b) => `${qt(b)} = ${powTex(p, logExact(p, b))}`))];
        return {
            node: rebuild([pow(num(p), add(exps))]),
            title: allSame ? L('Степени с одним основанием', 'Powers of one base') : L('Приводим степени к одному основанию', 'Bring the powers to one base'),
            text: L(`${conv.length ? `$${conv.join(',\\ ')}$. ` : ''}При умножении степеней с одним основанием показатели складываются, при делении — вычитаются: $a^x \\cdot a^y = a^{x+y}$, $\\dfrac{a^x}{a^y} = a^{x-y}$.`, `${conv.length ? `$${conv.join(',\\ ')}$. ` : ''}Multiplying powers of one base adds the exponents, dividing subtracts them: $a^x \\cdot a^y = a^{x+y}$, $\\dfrac{a^x}{a^y} = a^{x-y}$.`),
        };
    }
    const fact = bases.map(primeFactors);
    if (fact.some((f) => !f)) return null;
    const primes = [...new Set(fact.flatMap((f) => [...f.keys()]))].sort((a, b) => (a < b ? -1 : 1));
    if (primes.length > 4) return null;
    const powers = primes.map((pr) => pow(num(new Q(pr)), add(cand.flatMap(({ f, s }, i) => (fact[i].has(pr) ? [term(new Q(BigInt(fact[i].get(pr))), f.exp, s)] : [])))));
    const isPrime = (b, i) => b.isInt() && fact[i].size === 1 && fact[i].get(b.n) === 1;
    const conv = [...new Set(bases.flatMap((b, i) => (isPrime(b, i) ? [] : [`${qt(b)} = ${[...fact[i]].map(([pr, e]) => powTex(new Q(pr), new Q(BigInt(e)))).join(' \\cdot ')}`])))];
    return {
        node: rebuild(powers),
        title: L('Раскладываем основания на простые множители', 'Factor the bases into primes'),
        text: L(`$${conv.join(',\\ ')}$. Затем $(ab)^x = a^x b^x$, и показатели при одном основании складываются.`, `$${conv.join(',\\ ')}$. Then $(ab)^x = a^x b^x$, and the exponents of one base add up.`),
    };
}

// (a^m)^n → a^(mn)
function rulePowPow(n) {
    if (n.type !== 'pow' || n.base.type !== 'pow') return null;
    return { node: pow(n.base.base, mul(n.base.exp, n.exp)), title: L('Степень степени', 'A power of a power'), text: L('$(a^m)^n = a^{mn}$.') };
}

// (a·b)^k → a^k·b^k when some factor is a root: (2√7)² = 2²·(√7)²
function rulePowProduct(n) {
    if (n.type !== 'pow' || n.base.type !== 'mul' || !qv(n.exp)?.isInt()) return null;
    if (!n.base.args.some((f) => f.type === 'fn' && f.name === 'sqrt')) return null;
    return { node: mul(n.base.args.map((f) => pow(f, n.exp))), title: L('Степень произведения', 'A power of a product'), text: L('$(ab)^n = a^n b^n$.') };
}

// q^(m/n) with an exact root: 27^(2/3) = 3² ; (√a)^k = a^(k/2)
function ruleRationalPower(n) {
    if (n.type !== 'pow') return null;
    const e = qv(n.exp);
    if (!e) return null;
    if (n.base.type === 'fn' && n.base.name === 'sqrt' && e.isInt()) {
        const half = e.div(2);
        return { node: half.isOne() ? n.base.args[0] : pow(n.base.args[0], num(half)), title: L('Квадрат корня', 'The square of a root'), text: L('$\\left(\\sqrt{a}\\right)^2 = a$.'), quiet: true };
    }
    const b = qv(n.base);
    if (!b || e.isInt() || !b.isPos()) return null;
    const r = b.exactRoot(Number(e.d));
    if (!r) return null;
    const res = e.n === 1n ? num(r) : pow(num(r), num(new Q(e.n)));
    return { node: res, title: L('Степень с дробным показателем', 'A fractional power'), text: L(`$a^{\\frac{m}{n}} = \\left(\\sqrt[n]{a}\\right)^m$, $\\sqrt[${e.d}]{${qt(b)}} = ${qt(r)}$.`) };
}

// √a · √b → √(ab)
function ruleSqrtProduct(n) {
    if (n.type !== 'mul') return null;
    const roots = n.args.filter((f) => f.type === 'fn' && f.name === 'sqrt' && qv(f.args[0])?.isPos());
    if (roots.length < 2) return null;
    const rest = n.args.filter((f) => !roots.includes(f));
    const r = fn('sqrt', mul(roots.map((f) => f.args[0])));
    return { node: rest.length ? mul([...rest, r]) : r, title: L('Произведение корней', 'A product of roots'), text: L('$\\sqrt{a}\\cdot\\sqrt{b} = \\sqrt{ab}$.') };
}

// √q: an exact root, or a square factor taken out (√18 = 3√2)
function ruleSqrtValue(n) {
    if (n.type !== 'fn' || n.name !== 'sqrt' || n.args[0].type !== 'num') return null;
    const v = n.args[0].value;
    if (v.isNeg()) return null;
    const r = v.exactRoot(2);
    if (r) return { node: num(r), title: L('Извлекаем корень', 'Take the root'), text: L(`$${qt(r)}^2 = ${qt(v)}$.`), quiet: true };
    if (!v.isInt()) return null;
    let out = 1n;
    let inner = v.n;
    for (let p = 2n; p * p <= inner && p < 10000n; p++) {
        while (inner % (p * p) === 0n) {
            inner /= p * p;
            out *= p;
        }
    }
    if (out === 1n) return null;
    return { node: mul(num(new Q(out)), fn('sqrt', num(new Q(inner)))), title: L('Выносим множитель из-под корня', 'Take a factor out of the root'), text: L(`$${v.n} = ${out * out} \\cdot ${inner}$, $\\sqrt{a^2 b} = a\\sqrt{b}$.`) };
}

// (a − b)(a + b) → a² − b²
function ruleDiffSquares(n) {
    if (n.type !== 'mul' || n.args.length !== 2) return null;
    const [u, w] = n.args;
    if (u.type !== 'add' || w.type !== 'add' || u.args.length !== 2 || w.args.length !== 2) return null;
    if (u.args.every((x) => isArith(x))) return null; // (65 − 56)(65 + 56) is just arithmetic
    for (const [[a1, b1], [a2, b2]] of [[u.args, w.args], [w.args, u.args]]) {
        if (same(a1, a2) && same(b1, neg(b2))) {
            const pos = b1.type === 'neg' ? b1.arg : b1;
            return { node: add(pow(a1, num(2)), neg(pow(pos, num(2)))), title: L('Разность квадратов', 'The difference of squares'), text: L('$(a - b)(a + b) = a^2 - b^2$.') };
        }
    }
    return null;
}

// a² − b² of integers → (a − b)(a + b): √(65² − 56²)
function ruleFactorSquares(n) {
    if (n.type !== 'add' || n.args.length !== 2) return null;
    const [p, q] = n.args;
    const sq = (x) => (x.type === 'pow' && qv(x.exp)?.eq(2) && qv(x.base)?.isInt() ? x.base : null);
    const a = sq(p);
    const b = q.type === 'neg' ? sq(q.arg) : null;
    if (!a || !b || qv(a).abs().lt(10)) return null;
    return { node: mul(add(a, neg(b)), add(a, b)), title: L('Разность квадратов', 'The difference of squares'), text: L('$a^2 - b^2 = (a - b)(a + b)$ — так считать проще.', '$a^2 - b^2 = (a - b)(a + b)$ — easier to compute.') };
}

// (a ± b)² with roots → a² ± 2ab + b²
function ruleSquareSum(n) {
    if (n.type !== 'pow' || !qv(n.exp)?.eq(2) || n.base.type !== 'add' || n.base.args.length !== 2) return null;
    if (!nodeSome(n.base, (m) => m.type === 'fn' && m.name === 'sqrt') || freeVars(n).length) return null;
    const [a, b0] = n.base.args;
    const minus = b0.type === 'neg';
    const b = minus ? b0.arg : b0;
    const mid = mul(num(2), a, b);
    return {
        node: add(pow(a, num(2)), minus ? neg(mid) : mid, pow(b, num(2))),
        title: minus ? L('Квадрат разности', 'The square of a difference') : L('Квадрат суммы', 'The square of a sum'),
        text: minus ? L('$(a - b)^2 = a^2 - 2ab + b^2$.') : L('$(a + b)^2 = a^2 + 2ab + b^2$.'),
    };
}

// √(a ± k√b) = √x ± √y when x + y = a, 4xy = k²b: √(3 + 2√2) = √2 + 1
function ruleDenest(n) {
    if (n.type !== 'fn' || n.name !== 'sqrt' || n.args[0].type !== 'add' || n.args[0].args.length !== 2) return null;
    const [p, t] = n.args[0].args;
    const a = qv(p);
    if (!a) return null;
    let sign = 1;
    let r = t;
    if (r.type === 'neg') {
        sign = -1;
        r = r.arg;
    }
    let k = Q.ONE;
    if (r.type === 'mul' && r.args.length === 2 && qv(r.args[0])) {
        k = qv(r.args[0]);
        r = r.args[1];
    }
    if (r.type !== 'fn' || r.name !== 'sqrt' || !qv(r.args[0])) return null;
    const b = qv(r.args[0]);
    const D = a.mul(a).sub(k.mul(k).mul(b));
    const sd = D.isNeg() ? null : D.exactRoot(2);
    if (!sd) return null;
    const x = a.add(sd).div(2);
    const y = a.sub(sd).div(2);
    if (y.isNeg()) return null;
    const root = (q) => (q.exactRoot(2) ? num(q.exactRoot(2)) : fn('sqrt', num(q)));
    const rx = root(x);
    const ry = root(y);
    const inner = sign > 0 ? add(rx, ry) : add(rx, neg(ry));
    const sq = (lang) => `${toTex(n.args[0], { lang })} = ${toTex(pow(inner, num(2)), { lang })}`;
    return {
        node: inner,
        title: L('Выделяем полный квадрат под корнем', 'A perfect square under the root'),
        text: L(`$${sq('ru')}$: $${toTex(pow(rx, num(2)))} + ${toTex(pow(ry, num(2)))} = ${qt(a)}$, $2 \\cdot ${toTex(mul(rx, ry))} = ${toTex(sign > 0 ? t : t.arg)}$. Так как $\\sqrt{c^2} = |c|$ и $${toTex(inner)} \\ge 0$, корень равен $${toTex(inner)}$.`,
            `$${sq('en')}$: $${toTex(pow(rx, num(2)))} + ${toTex(pow(ry, num(2)))} = ${qt(a)}$, $2 \\cdot ${toTex(mul(rx, ry))} = ${toTex(sign > 0 ? t : t.arg)}$. As $\\sqrt{c^2} = |c|$ and $${toTex(inner)} \\ge 0$, the root is $${toTex(inner)}$.`),
    };
}

/* ------------------------------------------------------------------ trigonometry */

const FN_TEX = { sin: '\\sin', cos: '\\cos', tan: '\\operatorname{tg}', cot: '\\operatorname{ctg}' };
const FN_TEX_EN = { sin: '\\sin', cos: '\\cos', tan: '\\tan', cot: '\\cot' };
// In degree mode (the input wrote 135°) angles stay k·π/180, printed back as k°.
let DEG = false;
const isDegNode = (n) => n.type === 'div' && n.den.type === 'num' && n.den.value.eq(180) && n.num.type === 'mul' && n.num.args.length === 2 && n.num.args[0].type === 'num' && n.num.args[1].type === 'sym' && n.num.args[1].name === 'pi';
const piNode = (q) => (DEG && q.mul(180).isInt() && !q.isZero() ? degNode(q) : trySimplify(mul(num(q), sym('pi'))));
function degNode(q) {
    const k = q.mul(180);
    const d = div(mul(num(k.abs()), sym('pi')), num(180));
    return k.isNeg() ? neg(d) : d;
}
const DEG_RE = /\\frac\{([0-9]+)\\pi\}\{180\}/g;
const degTex = (s) => (typeof s === 'string' ? s.replace(DEG_RE, '$1^\\circ') : s);
function degSteps(steps) {
    const fix = (v) => (typeof v === 'string' ? degTex(v) : v && typeof v === 'object' ? { ru: degTex(v.ru), en: degTex(v.en) } : v);
    return steps.map((st) => ({ ...st, title: fix(st.title), ...(st.tex !== undefined ? { tex: fix(st.tex) } : {}), ...(st.text ? { text: fix(st.text) } : {}) }));
}
// 2u for an angle u, kept in degrees in degree mode
function double(u) {
    const q = piMultiple(u);
    return q ? piNode(q.mul(2)) : trySimplify(mul(num(2), u));
}
// the angle as a rational multiple of π, or null
const piMultiple = (angle) => qv(trySimplify(div(angle, sym('pi'))));

// f(qπ) → the chain of reduction formulas down to the table value
function trigChain(name, q) {
    const odd = name !== 'cos';
    const chain = [];
    const notes = [];
    let sign = 1;
    let a = q;
    const at = (x) => (sign < 0 ? neg(fn(name, x)) : fn(name, x));
    if (a.isNeg()) {
        a = a.neg();
        if (odd) sign = -sign;
        chain.push(at(piNode(a)));
        notes.push(odd ? L(`нечётность: $${FN_TEX[name]}(-\\alpha) = -${FN_TEX[name]}\\,\\alpha$`, `oddness: $${FN_TEX_EN[name]}(-\\alpha) = -${FN_TEX_EN[name]}\\,\\alpha$`) : L('чётность: $\\cos(-\\alpha) = \\cos\\alpha$', 'evenness: $\\cos(-\\alpha) = \\cos\\alpha$'));
    }
    const period = name === 'tan' || name === 'cot' ? Q.ONE : new Q(2n);
    if (a.ge(period)) {
        const k = a.div(period).floor();
        const r = a.sub(period.mul(k));
        chain.push(at(add(piNode(period.mul(k)), piNode(r))));
        a = r;
        chain.push(at(piNode(a)));
        notes.push(L(`период ${period.eq(1) ? '$\\pi$' : '$2\\pi$'}`, `the period ${period.eq(1) ? '$\\pi$' : '$2\\pi$'}`));
    }
    if (a.gt(new Q(1n, 2n))) {
        let beta;
        let form;
        let flip;
        if (period.eq(1)) {
            beta = Q.ONE.sub(a);
            form = add(piNode(Q.ONE), neg(piNode(beta)));
            flip = true;
        } else if (a.le(Q.ONE)) {
            beta = Q.ONE.sub(a);
            form = add(piNode(Q.ONE), neg(piNode(beta)));
            flip = name === 'cos';
        } else if (a.le(new Q(3n, 2n))) {
            beta = a.sub(Q.ONE);
            form = add(piNode(Q.ONE), piNode(beta));
            flip = true;
        } else {
            beta = new Q(2n).sub(a);
            form = add(piNode(new Q(2n)), neg(piNode(beta)));
            flip = name === 'sin';
        }
        chain.push(at(form));
        if (flip) sign = -sign;
        a = beta;
        chain.push(at(piNode(a)));
        notes.push(L('формула приведения', 'a reduction formula'));
    }
    const val = trySimplify(at(piNode(a)));
    if (nodeSome(val, (m) => m.type === 'fn' && TRIG.has(m.name))) return null;
    chain.push(val);
    return { chain, notes, value: val };
}

function ruleTrigValue(n) {
    if (n.type !== 'fn' || !TRIG.has(n.name) || freeVars(n).length) return null;
    const q = piMultiple(n.args[0]);
    if (!q) return null;
    const r = trigChain(n.name, q);
    if (!r) return null;
    const texChain = (lang) => [fn(n.name, piNode(q)), ...r.chain].map((x) => toTex(x, { lang })).filter((t, i, all) => i === 0 || t !== all[i - 1]).join(' = ');
    if (!r.notes.length) return { node: r.value, title: L('Табличное значение', 'A table value'), text: L(`$${texChain('ru')}$.`, `$${texChain('en')}$.`) };
    return {
        node: r.value,
        title: L('Формулы приведения', 'Reduction formulas'),
        text: L(`$${texChain('ru')}$ (${r.notes.map((x) => x.ru).join(', ')}).`, `$${texChain('en')}$ (${r.notes.map((x) => x.en).join(', ')}).`),
    };
}

// sin u · sin v with u + v = π/2 → sin u · cos u (sin 41° = sin(90° − 49°) = cos 49°); the same for cos · cos
function ruleCofunction(n) {
    const fs = n.type === 'mul' ? n.args : null;
    if (!fs) return null;
    const trig = fs.filter((f) => f.type === 'fn' && (f.name === 'sin' || f.name === 'cos') && piMultiple(f.args[0]));
    for (let i = 0; i < trig.length; i++) {
        for (let j = i + 1; j < trig.length; j++) {
            const f = trig[i];
            const g = trig[j];
            if (f.name !== g.name) continue;
            const qf = piMultiple(f.args[0]);
            const qg = piMultiple(g.args[0]);
            if (!qf.add(qg).eq(new Q(1n, 2n))) continue;
            const other = g.name === 'sin' ? 'cos' : 'sin';
            const repl = fn(other, f.args[0]);
            const via = fn(g.name, add(piNode(new Q(1n, 2n)), neg(f.args[0])));
            const texOf = (lang) => `${toTex(g, { lang })} = ${toTex(via, { lang })} = ${toTex(repl, { lang })}`;
            return {
                node: mul(fs.map((x) => (x === g ? repl : x))),
                title: L('Формулы приведения', 'Reduction formulas'),
                text: L(`$${texOf('ru')}$, так как $\\sin\\left(\\frac{\\pi}{2} - \\alpha\\right) = \\cos\\alpha$, $\\cos\\left(\\frac{\\pi}{2} - \\alpha\\right) = \\sin\\alpha$.`, `$${texOf('en')}$, since $\\sin\\left(\\frac{\\pi}{2} - \\alpha\\right) = \\cos\\alpha$, $\\cos\\left(\\frac{\\pi}{2} - \\alpha\\right) = \\sin\\alpha$.`),
            };
        }
    }
    return null;
}

// k·sin u·cos u → (k/2)·sin 2u ;  cos²u − sin²u → cos 2u
function ruleDoubleAngle(n) {
    if (n.type === 'mul') {
        const s = n.args.find((f) => f.type === 'fn' && f.name === 'sin');
        const c = s && n.args.find((f) => f.type === 'fn' && f.name === 'cos' && same(f.args[0], s.args[0]));
        if (!c) return null;
        const rest = n.args.filter((f) => f !== s && f !== c);
        const k = rest.length === 0 ? Q.ONE : rest.length === 1 ? qv(rest[0]) : null;
        if (!k) return null;
        const half = k.div(2);
        const s2 = fn('sin', double(s.args[0]));
        return { node: half.isOne() ? s2 : mul(num(half), s2), title: L('Синус двойного угла', 'The double-angle sine'), text: L('$2\\sin u \\cos u = \\sin 2u$.') };
    }
    if (n.type === 'add' && n.args.length === 2) {
        const sq = (f, name) => (f.type === 'pow' && qv(f.exp)?.eq(2) && f.base.type === 'fn' && f.base.name === name ? f.base.args[0] : null);
        const [p, q] = n.args;
        const u = sq(p, 'cos');
        const w = q.type === 'neg' ? sq(q.arg, 'sin') : null;
        if (u && w && same(u, w)) return { node: fn('cos', double(u)), title: L('Косинус двойного угла', 'The double-angle cosine'), text: L('$\\cos^2 u - \\sin^2 u = \\cos 2u$.') };
    }
    return null;
}

// cos²u, sin²u when u has no table value but 2u does → (1 ± cos 2u)/2
function ruleLowerPower(n) {
    if (n.type !== 'pow' || !qv(n.exp)?.eq(2) || n.base.type !== 'fn' || (n.base.name !== 'cos' && n.base.name !== 'sin')) return null;
    const u = n.base.args[0];
    if (freeVars(u).length || !nodeSome(trySimplify(n.base), (m) => m.type === 'fn' && TRIG.has(m.name))) return null;
    const c2 = fn('cos', double(u));
    if (nodeSome(trySimplify(c2), (m) => m.type === 'fn' && TRIG.has(m.name))) return null;
    const cos = n.base.name === 'cos';
    return {
        node: div(add(num(1), cos ? c2 : neg(c2)), num(2)),
        title: L('Формула понижения степени', 'Lowering the power'),
        text: cos ? L('$\\cos^2 u = \\dfrac{1 + \\cos 2u}{2}$.') : L('$\\sin^2 u = \\dfrac{1 - \\cos 2u}{2}$.'),
    };
}

/* ------------------------------------------------------------------ arithmetic */

// a number as written: 3, −3, 3/5
function atomic(n) {
    if (n.type === 'num') return true;
    if (n.type === 'neg') return (n.arg.type === 'num' || n.arg.type === 'div') && atomic(n.arg) && !n.arg.value?.isNeg();
    if (n.type !== 'div' || n.num.type !== 'num' || n.den.type !== 'num') return false;
    const a = n.num.value;
    const b = n.den.value;
    return a.isInt() && b.isInt() && b.isPos() && !b.isOne() && a.div(b).d === b.n; // 3/5 but not 36/4
}
function isArith(n) {
    if (n.type === 'num') return true;
    if (n.type === 'neg') return isArith(n.arg);
    if (n.type === 'add' || n.type === 'mul') return n.args.every(isArith);
    if (n.type === 'div') return isArith(n.num) && isArith(n.den) && !qv(n.den)?.isZero();
    if (n.type === 'pow') return isArith(n.base) && !!qv(n.exp)?.isInt() && qv(n.exp).abs().le(64);
    if (n.type === 'fn' && n.name === 'fact') return isArith(n.args[0]) && !!qv(n.args[0])?.isInt() && qv(n.args[0]).le(30);
    return false;
}
// one layer: every operation whose operands are already numbers is done at once
function arithLayer(n) {
    if (atomic(n)) return n;
    const kids = nodeChildren(n);
    if (kids.every(atomic)) {
        const v = trySimplify(n);
        return atomic(v) ? v : n;
    }
    return withChildren(n, kids.map(arithLayer));
}
function ruleArith(n) {
    if (atomic(n) || !isArith(n)) return null;
    const next = arithLayer(n);
    return nodeKey(next) === nodeKey(n) ? null : { node: next, quiet: true };
}

// a numeric subterm without logs and trigonometry that the engine makes shorter: exponents, roots
function ruleSimplifyPart(n) {
    if (atomic(n) || freeVars(n).length || hasTrigOrLog(n) || (DEG && isDegNode(n))) return null;
    const v = trySimplify(n);
    if (nodeKey(v) === nodeKey(n) || tx(v).length >= tx(n).length) return null;
    return { node: v, quiet: true };
}

const RULES = [ruleLogSum, ruleChangeBase, ruleLogIdentity, ruleLogOfPower, ruleDiffSquares, ruleFactorSquares, ruleSquareSum, rulePowers, rulePowPow, rulePowProduct, ruleRationalPower, ruleSqrtProduct, ruleSqrtValue, ruleDenest, ruleCofunction, ruleDoubleAngle, ruleLowerPower, ruleTrigValue];

// the first rewrite, outermost first; a whole arithmetic subtree goes one layer at a time
function rewriteOnce(n) {
    for (const rule of RULES) {
        const r = rule(n);
        if (r && nodeKey(r.node) !== nodeKey(n)) return r;
    }
    const a = ruleArith(n);
    if (a) return a;
    const kids = nodeChildren(n);
    for (let i = 0; i < kids.length; i++) {
        const r = rewriteOnce(kids[i]);
        if (r) {
            const next = kids.slice();
            next[i] = r.node;
            const node = n.type === 'neg' && r.node.type === 'num' ? num(r.node.value.neg()) : withChildren(n, next);
            return { ...r, node };
        }
    }
    const s = ruleSimplifyPart(n);
    return s && nodeKey(s.node) !== nodeKey(n) ? s : null;
}

const COMPUTE = L('Считаем', 'Compute');

/**
 * The value of a numeric expression with school-style steps.
 * @param {string|object} input  text or a node without free variables
 * @returns {{value: object, approx: number, exact: boolean, steps: object[]}}
 */
export function evaluateSteps(input, opts = {}) {
    const maxSteps = opts.maxSteps ?? 40;
    const start = typeof input === 'string' ? parse(input, { lang: opts.lang === 'en' ? 'en' : 'ru' }) : input;
    const want = approx(start);
    DEG = nodeSome(start, isDegNode);
    try {
        return run(start, want, maxSteps);
    } finally {
        DEG = false;
    }
}

function run(start, want, maxSteps) {
    const entries = []; // {title, named, texts, chain: nodes, quiet, rule}
    let cur = start;
    const seen = new Set([nodeKey(cur)]);
    for (let i = 0; i < maxSteps && !atomic(cur); i++) {
        let r = null;
        try {
            r = rewriteOnce(cur);
        } catch {
            r = null;
        }
        if (!r || seen.has(nodeKey(r.node))) break;
        seen.add(nodeKey(r.node));
        const got = approx(r.node);
        if (Number.isFinite(want) && !(Number.isFinite(got) && Math.abs(got - want) <= 1e-9 * Math.max(1, Math.abs(want)))) break;
        const last = entries[entries.length - 1];
        if (r.quiet && last?.quiet) {
            last.chain.push(r.node);
            if (r.text && !last.texts.some((t) => t.ru === r.text.ru)) last.texts.push(r.text);
        } else {
            entries.push({ title: r.title ?? COMPUTE, texts: r.text ? [r.text] : [], chain: [cur, r.node], quiet: !!r.quiet });
        }
        cur = r.node;
    }
    // the value: where the steps arrived when the engine agrees it is simpler, else the engine's own form
    const end = trySimplify(cur);
    const value = Number.isFinite(want) && tx(end).length > tx(trySimplify(start)).length ? trySimplify(start) : end;
    if (tx(value) !== tx(cur)) entries.push({ title: L('Упрощаем', 'Simplify'), texts: [], chain: [cur, value], rule: 'simplify' });
    const steps = entries.map((e) => {
        const title = e.quiet && e.chain.length > 2 ? COMPUTE : e.title;
        const text = e.texts.length ? L(e.texts.map((t) => t.ru).join(' '), e.texts.map((t) => t.en).join(' ')) : undefined;
        const chain = (lang) => e.chain.map((x) => toTex(x, { lang })).filter((t, i, all) => i === 0 || t !== all[i - 1]).join(' = ');
        return step({ title, tex: L(chain('ru'), chain('en')), text, rule: e.rule ?? (e.quiet ? 'arith' : 'rule') });
    });
    steps.push(step({ title: L('Ответ', 'Answer'), tex: L(`${toTex(start, { lang: 'ru' })} = ${toTex(value, { lang: 'ru' })}`, `${toTex(start, { lang: 'en' })} = ${toTex(value, { lang: 'en' })}`), rule: 'answer' }));
    steps[steps.length - 1].final = true;
    return { value, approx: want, exact: freeVars(value).length === 0, steps: DEG ? degSteps(steps) : steps };
}
