// generate/tasks — tasks built backwards from their answers, for trainers and for the bench.
//
//   generateTask('quadratic-eq', {seed: 7, level: 2}) → {family, level, seed, op, task, prompt (a message), answer, …}
//   TASK_KINDS — the list of kinds; generateSet(kind, {count, seed, level}) — a reproducible batch.
//
// Every answer comes from the construction (roots → equation, solution → system, critical points → cubic),
// never from the solver, so a generated task can check the solver. The same seed gives the same task.
// Level 1: small integers; level 2: wider ranges and the usual traps (an extraneous root, a negative leading
// coefficient); level 3: fractions and longer forms.
import { Q } from '../core/rational.js';
import { msg } from '../i18n/index.js';

const gcdInt = (a, b) => (b ? gcdInt(b, a % b) : Math.abs(a));

/* ------------------------------------------------------------------ randomness */

function mulberry32(seed) {
    let a = seed >>> 0;
    return () => {
        a = (a + 0x6d2b79f5) >>> 0;
        let t = a;
        t = Math.imul(t ^ (t >>> 15), t | 1);
        t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
}
function rng(seed) {
    const r = mulberry32(seed);
    const int = (a, b) => a + Math.floor(r() * (b - a + 1));
    const nz = (a, b) => {
        for (;;) {
            const x = int(a, b);
            if (x !== 0) return x;
        }
    };
    const pick = (arr) => arr[Math.floor(r() * arr.length)];
    const distinct = (n, a, b, avoid = []) => {
        const out = [];
        while (out.length < n) {
            const x = int(a, b);
            if (!out.includes(x) && !avoid.includes(x)) out.push(x);
        }
        return out;
    };
    return { r, int, nz, pick, distinct };
}

/* ------------------------------------------------------------------ writing expressions */

const q = (x) => Q.of(x);
const qs = (x) => q(x).toString(); // "3", "-3/4"
// a number as a factor or a term: fractions in brackets
// a polynomial from its coefficients, highest degree first: [1, -5, 6] → "x^2 - 5x + 6"
function poly(coeffs, v = 'x') {
    const n = coeffs.length - 1;
    let out = '';
    coeffs.forEach((c0, i) => {
        const c = q(c0);
        if (c.isZero()) return;
        const d = n - i;
        const neg = c.isNeg();
        const a = c.abs();
        const mono = d === 0 ? '' : d === 1 ? v : `${v}^${d}`;
        const coef = d > 0 && a.isOne() ? '' : a.isInt() || d === 0 ? a.toString() : `(${a.toString()})`;
        const term = `${coef}${mono}`;
        out += out ? (neg ? ` - ${term}` : ` + ${term}`) : neg ? `-${term}` : term;
    });
    return out || '0';
}
// (x − r) with r a rational: "x - 3", "x + 3", "2x - 1" for r = 1/2
function lin(r0, v = 'x') {
    const r = q(r0);
    if (r.isZero()) return v;
    const p = r.n;
    const d = r.d;
    const lead = d === 1n ? v : `${d}${v}`;
    return p < 0n ? `${lead} + ${-p}` : `${lead} - ${p}`;
}
// the product of (x − rᵢ) with integer-coefficient linear factors, expanded: coefficients high → low
function fromRoots(roots, k = 1) {
    let c = [q(k)];
    for (const r0 of roots) {
        const r = q(r0);
        const [a, b] = [new Q(r.d), new Q(-r.n)]; // d·x − n
        const next = new Array(c.length + 1).fill(Q.ZERO);
        c.forEach((ci, i) => {
            next[i] = next[i].add(ci.mul(a));
            next[i + 1] = next[i + 1].add(ci.mul(b));
        });
        c = next;
    }
    return c;
}
const setText = (parts) => parts.join(' U ');
const iv = (a, b, lc, hc) => `${lc ? '[' : '('}${a === null ? '-inf' : qs(a)}; ${b === null ? '+inf' : qs(b)}${hc ? ']' : ')'}`;
const SOLVE = msg('generate.tasks.solve_equation');
// k·x as an exponent or an argument: x, -x, 3x
const kx = (k, v = 'x') => (k === 1 ? v : k === -1 ? `-${v}` : `${k}${v}`);
// c·e^(kx) as a term: e^(x), -e^(-x), 3e^(2x); a constant when k = 0
const expTerm = (c, k) => (k === 0 ? String(c) : `${c === 1 ? '' : c === -1 ? '-' : c}e^(${kx(k)})`);
// a sum of terms c·rest with tidy signs: [[3, 'x^2'], [-2, 'x'], [5, '']] → "3x^2 - 2x + 5"
function sum(terms) {
    let out = '';
    for (const [c0, rest] of terms) {
        const c = q(c0);
        if (c.isZero()) continue;
        const a = c.abs();
        const coef = rest && a.isOne() ? '' : a.isInt() ? a.toString() : `(${a.toString()})`;
        const term = `${coef}${rest}`;
        out += out ? (c.isNeg() ? ` - ${term}` : ` + ${term}`) : c.isNeg() ? `-${term}` : term;
    }
    return out || '0';
}

/* ------------------------------------------------------------------ generators */

const GEN = {
    'linear-eq'(g, level) {
        const r = level >= 3 ? q(g.nz(-9, 9)).div(q(g.pick([2, 3, 4, 5]))) : q(g.int(-9, 9));
        const a = g.nz(-6, 6);
        let c = g.nz(-6, 6);
        if (c === a) c = a + 1 || 2;
        const b = g.int(-12, 12);
        const d = q(a - c)
            .mul(r)
            .add(q(b)); // a·r + b = c·r + d
        const task = `${poly([a, b])} = ${poly([c, d])}`;
        return { op: 'solve', task, answer: { roots: [qs(r)] }, prompt: SOLVE };
    },
    'quadratic-eq'(g, level) {
        if (level >= 2 && g.r() < 0.12) {
            // no real roots: (x − p)² + s with s > 0
            const p = g.int(-5, 5);
            const s = g.int(1, 9);
            return { op: 'solve', task: `${poly([1, -2 * p, p * p + s])} = 0`, answer: { none: true }, prompt: SOLVE };
        }
        const [r1, r2] = level >= 3 ? [q(g.nz(-7, 7)).div(q(g.pick([2, 3]))), q(g.int(-6, 6))] : g.distinct(2, -9, 9).map(q);
        const k = level >= 2 ? g.pick([1, -1, 2, 3]) : 1;
        const c = fromRoots([r1, r2], k);
        const task = level >= 2 && g.r() < 0.4 ? `${poly([c[0], c[1], 0])} = ${qs(c[2].neg())}` : `${poly(c)} = 0`;
        const roots = [r1, r2].filter((x, i, a) => a.findIndex((y) => y.eq(x)) === i).map(qs);
        return { op: 'solve', task, answer: { roots }, prompt: SOLVE };
    },
    'exp-eq'(g, level) {
        const b = g.pick([2, 3, 5, 7]);
        const x0 = level >= 3 ? q(g.nz(-5, 5)).div(q(2)) : q(g.int(-4, 5));
        const a = g.nz(-3, 3);
        const c = g.int(-5, 5);
        const k = q(a).mul(x0).add(q(c)); // the exponent at x0
        if (!k.isInt() || k.abs().gt(q(6))) return GEN['exp-eq'](g, level);
        const rhs = k.isNeg() ? `1/${b ** Number(-k.n)}` : `${b ** Number(k.n)}`;
        const base = level >= 2 && g.r() < 0.5 ? `(1/${b})` : `${b}`;
        const exp = base.startsWith('(') ? poly([-a, -c]) : poly([a, c]);
        return { op: 'solve', task: `${base}^(${exp}) = ${rhs}`, answer: { roots: [qs(x0)] }, prompt: SOLVE };
    },
    'log-eq'(g, level) {
        const b = g.pick([2, 3, 5]);
        const k = g.int(level >= 2 ? -2 : 0, 4);
        const a = level >= 2 ? g.nz(-3, 3) : 1;
        const c = g.int(-9, 9);
        const x0 = q(b).pow(k).sub(q(c)).div(q(a)); // a·x0 + c = b^k
        return { op: 'solve', task: `log_${b}(${poly([a, c])}) = ${k}`, answer: { roots: [qs(x0)] }, prompt: SOLVE };
    },
    'radical-eq'(g, level) {
        if (level === 1) {
            const c = g.int(1, 8);
            const a = g.nz(-4, 4);
            const x0 = g.int(-8, 8);
            const b = c * c - a * x0;
            return { op: 'solve', task: `sqrt(${poly([a, b])}) = ${c}`, answer: { roots: [String(x0)] }, prompt: SOLVE };
        }
        // √(ax + b) = x + c: a valid root r1 (r1 + c ≥ 0) and an extraneous r2 (r2 + c < 0)
        const c = g.int(-4, 4);
        const r1 = g.int(-c, -c + 8);
        const r2 = g.int(-c - 8, -c - 1);
        const a = r1 + r2 + 2 * c;
        const b = c * c - r1 * r2;
        return { op: 'solve', task: `sqrt(${poly([a, b])}) = ${poly([1, c])}`, answer: { roots: [String(r1)] }, prompt: SOLVE };
    },
    'quad-ineq'(g, level) {
        const [r1, r2] = g.distinct(2, -8, 8).sort((u, v) => u - v);
        const k = level >= 2 ? g.pick([1, -1, 2, -3]) : 1;
        const op = g.pick(['<', '<=', '>', '>=']);
        const c = fromRoots([r1, r2], k);
        const closed = op.length === 2;
        const inside = (op[0] === '<') === k > 0;
        const ans = inside ? iv(r1, r2, closed, closed) : setText([iv(null, r1, false, closed), iv(r2, null, closed, false)]);
        return { op: 'ineq', task: `${poly(c)} ${op} 0`, answer: { set: ans }, prompt: msg('generate.tasks.solve_inequality') };
    },
    'rat-ineq'(g) {
        const [p, s] = g.distinct(2, -7, 7);
        const op = g.pick(['<', '<=', '>', '>=']);
        const [lo, hi] = p < s ? [p, s] : [s, p];
        const closedP = op.length === 2; // the zero of the numerator; the pole is always open
        const cl = (x) => closedP && x === p;
        const inside = op[0] === '<';
        const ans = inside ? iv(lo, hi, cl(lo), cl(hi)) : setText([iv(null, lo, false, cl(lo)), iv(hi, null, cl(hi), false)]);
        return { op: 'ineq', task: `(${lin(p)})/(${lin(s)}) ${op} 0`, answer: { set: ans }, prompt: msg('generate.tasks.solve_inequality') };
    },
    'log-value'(g) {
        const b = g.pick([2, 3, 5, 6, 7]);
        const kind = g.int(0, 3);
        if (kind === 0) {
            // log_b(b^m·c) − log_b(c) = m
            const m = g.int(1, 3);
            const c = g.pick([3, 5, 7, 11, 13].filter((x) => x !== b));
            return { op: 'value', task: `log_${b}(${b ** m * c}) - log_${b}(${c})`, answer: { value: String(m) }, prompt: msg('generate.tasks.find_value') };
        }
        if (kind === 1) {
            // (b^2)^(log_b c) = c²
            const c = g.int(2, 9);
            return { op: 'value', task: `${b * b}^(log_${b}(${c}))`, answer: { value: String(c * c) }, prompt: msg('generate.tasks.find_value') };
        }
        if (kind === 2) {
            // log_b(p) + log_b(r) with p·r = b^m
            const m = g.int(2, 4);
            const divs = [];
            for (let d = 2; d < b ** m; d++) if (b ** m % d === 0) divs.push(d);
            const p = g.pick(divs);
            return { op: 'value', task: `log_${b}(${p}) + log_${b}(${b ** m / p})`, answer: { value: String(m) }, prompt: msg('generate.tasks.find_value') };
        }
        // b^(log_b c + k) = c·b^k
        const c = g.int(2, 9);
        const k = g.int(1, 2);
        return { op: 'value', task: `${b}^(log_${b}(${c}) + ${k})`, answer: { value: String(c * b ** k) }, prompt: msg('generate.tasks.find_value') };
    },
    'power-value'(g) {
        const a = g.pick([2, 3, 5]);
        const kind = g.int(0, 2);
        if (kind === 0) {
            // a^(m/n)·a^(p/n) with an integer total; both exponents positive fractions in lowest terms (no 3/3, 14/7, 0/7)
            const n = g.pick([3, 4, 5, 7]);
            const total = g.int(1, 3);
            const coprime = [];
            for (let m = 1; m < total * n; m++) if (gcdInt(m, n) === 1) coprime.push(m);
            const m = g.pick(coprime);
            const p = total * n - m;
            return {
                op: 'value',
                task: `${a}^(${m}/${n}) * ${a}^(${p}/${n})`,
                answer: { value: String(a ** total) },
                prompt: msg('generate.tasks.find_value'),
            };
        }
        if (kind === 1) {
            // (a^k)^(m/k), m/k in lowest terms: 8^(2/3), 27^(4/3), 9^(3/2) — not 9^(2/2)
            const k = g.pick([2, 3]);
            const m = g.pick(k === 2 ? [1, 3] : [1, 2, 4]);
            return { op: 'value', task: `${a ** k}^(${m}/${k})`, answer: { value: String(a ** m) }, prompt: msg('generate.tasks.find_value') };
        }
        // a^(u)·(a^2)^(v)/a^(w)
        const u = g.int(1, 6);
        const v = g.int(1, 3);
        const w = g.int(1, u + 2 * v - 1);
        const e = u + 2 * v - w;
        return { op: 'value', task: `${a}^${u} * ${a * a}^${v} / ${a}^${w}`, answer: { value: String(a ** e) }, prompt: msg('generate.tasks.find_value') };
    },
    'trig-value'(g) {
        // k·sqrt(2)·sin/cos(±45° + 180°n) and friends with integer answers
        const rows = [
            { f: 'sin', deg: 30, v: q(1).div(q(2)), root: '' },
            { f: 'cos', deg: 60, v: q(1).div(q(2)), root: '' },
            { f: 'sin', deg: 45, v: q(1).div(q(2)), root: 'sqrt(2)' },
            { f: 'cos', deg: 45, v: q(1).div(q(2)), root: 'sqrt(2)' },
            { f: 'tg', deg: 45, v: q(1), root: '' },
            { f: 'sin', deg: 60, v: q(1).div(q(2)), root: 'sqrt(3)' },
        ];
        const row = g.pick(rows);
        // reduction: θ = ±deg + 180n (sign from the quadrant)
        const n = g.int(-1, 2);
        const minus = g.r() < 0.5;
        const theta = (minus ? -row.deg : row.deg) + 180 * n;
        const rad = (theta * Math.PI) / 180;
        const exactSign = Math.sign(row.f === 'sin' ? Math.sin(rad) : row.f === 'cos' ? Math.cos(rad) : Math.tan(rad));
        const k = g.pick([2, 4, 6, 8, 10, 12]);
        // k·root·f(θ) = k·(root·value) where root·(√2/2) → the rows keep value·root² = integer/2
        const value = row.root
            ? q(k)
                  .mul(row.v)
                  .mul(q(row.root === 'sqrt(2)' ? 2 : 3))
            : q(k).mul(row.v);
        const task = `${k}${row.root ? row.root : ''} ${row.f}(${theta}°)`;
        return { op: 'value', task, answer: { value: qs(value.mul(q(exactSign))) }, prompt: msg('generate.tasks.find_value') };
    },
    extremum(g, level) {
        // f' = 3(x − p)(x − s): f = x³ − (3/2)(p + s)x² + 3ps·x + c, p + s even
        const p = g.int(-4, 3);
        const s = p + 2 * g.int(1, 3);
        const c = g.int(-10, 10);
        const A = [1, (-3 * (p + s)) / 2, 3 * p * s, c];
        const f = (x) => x ** 3 + A[1] * x * x + A[2] * x + c;
        const kind = g.pick(['max', 'min']);
        // a segment around one critical point
        const around = kind === 'max' ? p : s; // p is the local max, s the local min
        const lo = around - g.int(1, 2);
        const hi = around + g.int(1, level >= 2 ? 3 : 1);
        const cands = [lo, hi, ...[p, s].filter((x) => x > lo && x < hi)].map(f);
        const value = kind === 'max' ? Math.max(...cands) : Math.min(...cands);
        return {
            op: 'extremum',
            task: poly(A),
            answer: { value: String(value) },
            kind,
            segment: [String(lo), String(hi)],
            prompt: kind === 'max' ? msg('generate.tasks.find_greatest_value_on', { lo, hi }) : msg('generate.tasks.find_least_value_on', { lo, hi }),
        };
    },
    'definite-integral'(g, level) {
        const deg = level >= 2 ? 3 : 2;
        const cs = Array.from({ length: deg + 1 }, () => g.int(-5, 5));
        if (cs[0] === 0) cs[0] = 1;
        const a = g.int(-2, 1);
        const b = a + g.int(1, 3);
        // ∫ Σ c_i x^(deg−i) = Σ c_i x^(deg−i+1)/(deg−i+1)
        const F = (x) =>
            cs.reduce(
                (acc, c, i) =>
                    acc.add(
                        q(c)
                            .mul(q(x).pow(deg - i + 1))
                            .div(q(deg - i + 1)),
                    ),
                Q.ZERO,
            );
        const value = F(b).sub(F(a));
        return {
            op: 'integral',
            task: poly(cs),
            bounds: [String(a), String(b)],
            answer: { value: qs(value) },
            prompt: msg('generate.tasks.compute_integral_from_to', { a, b }),
        };
    },
    'linear-system'(g) {
        const x0 = g.int(-6, 6);
        const y0 = g.int(-6, 6);
        let a1;
        let b1;
        let a2;
        let b2;
        do {
            [a1, b1, a2, b2] = [g.nz(-5, 5), g.nz(-5, 5), g.nz(-5, 5), g.nz(-5, 5)];
        } while (a1 * b2 - a2 * b1 === 0);
        const eq = (a, b) => `${poly([a, 0])}${b < 0 ? ` - ${Math.abs(b) === 1 ? '' : Math.abs(b)}y` : ` + ${b === 1 ? '' : b}y`} = ${a * x0 + b * y0}`;
        return {
            op: 'system',
            task: [eq(a1, b1), eq(a2, b2)].join('; '),
            answer: { solutions: [[String(x0), String(y0)]] },
            prompt: msg('generate.tasks.solve_system'),
        };
    },
    factor(g, level) {
        const rs = g.distinct(level >= 2 ? 3 : 2, -6, 6);
        const k = level >= 3 ? g.pick([2, 3, -1]) : 1;
        const c = fromRoots(rs, k);
        const expr = `${k === 1 ? '' : k === -1 ? '-' : `${k}*`}${rs.map((r) => `(${lin(r)})`).join('*')}`;
        return { op: 'factor', task: poly(c), answer: { expr }, prompt: msg('generate.tasks.factor') };
    },
    'reduce-fraction'(g) {
        const [r1, r2, r3] = g.distinct(3, -6, 6);
        const top = fromRoots([r1, r2]);
        const bottom = fromRoots([r1, r3]);
        return {
            op: 'simplify',
            task: `(${poly(top)})/(${poly(bottom)})`,
            answer: { expr: `(${lin(r2)})/(${lin(r3)})` },
            prompt: msg('generate.tasks.reduce_fraction'),
        };
    },
    ode(g, level) {
        if (level === 1) {
            const k = g.nz(-3, 3);
            const c = g.nz(-5, 5);
            return {
                op: 'ode',
                task: `y' = ${k === 1 ? '' : k === -1 ? '-' : k}y; y(0) = ${c}`,
                answer: { expr: expTerm(c, k) },
                prompt: msg('generate.tasks.solve_initial_value_problem'),
            };
        }
        const [r1, r2] = g.distinct(2, -3, 3);
        const A = g.nz(-3, 3);
        const B = g.nz(-3, 3);
        const s = r1 + r2;
        const p = r1 * r2;
        const lhs = `y''${s === 0 ? '' : s > 0 ? ` - ${s === 1 ? '' : s}y'` : ` + ${-s === 1 ? '' : -s}y'`}${p === 0 ? '' : p > 0 ? ` + ${p === 1 ? '' : p}y` : ` - ${-p === 1 ? '' : -p}y`}`;
        return {
            op: 'ode',
            task: `${lhs} = 0; y(0) = ${A + B}; y'(0) = ${A * r1 + B * r2}`,
            answer: {
                expr: sum([
                    [A, r1 === 0 ? '' : `e^(${kx(r1)})`],
                    [B, r2 === 0 ? '' : `e^(${kx(r2)})`],
                ]),
            },
            prompt: msg('generate.tasks.solve_initial_value_problem'),
        };
    },
    'geometric-series'(g) {
        const den = g.pick([2, 3, 4, 5]);
        const num = g.nz(-(den - 1), den - 1);
        const ratio = q(num).div(q(den));
        const c = g.nz(-4, 4);
        const s = g.int(0, 2);
        const value = q(c).mul(ratio.pow(s)).div(Q.ONE.sub(ratio));
        return {
            op: 'series',
            task: `sum(${c}*(${num}/${den})^k, k, ${s}, inf)`,
            answer: { value: qs(value) },
            prompt: msg('generate.tasks.find_sum_of_series'),
        };
    },
    'param-two-roots'(g) {
        if (g.r() < 0.5) {
            const c = g.int(1, 6);
            return {
                op: 'param',
                task: `x^2 - 2a x + ${c * c} = 0`,
                param: 'a',
                want: 'two-roots',
                answer: { set: setText([iv(null, -c, false, false), iv(c, null, false, false)]) },
                prompt: msg('generate.tasks.for_which_are_there_two_roots'),
            };
        }
        const b = 2 * g.nz(-4, 4);
        return {
            op: 'param',
            task: `x^2 ${b < 0 ? '-' : '+'} ${Math.abs(b)}x + a = 0`,
            param: 'a',
            want: 'two-roots',
            answer: { set: iv(null, (b * b) / 4, false, false) },
            prompt: msg('generate.tasks.for_which_are_there_two_roots'),
        };
    },
    limit(g) {
        const kind = g.int(0, 2);
        if (kind === 0) {
            const r = g.nz(-6, 6);
            return {
                op: 'limit',
                task: `(x^2 - ${r * r})/(${lin(r)})`,
                at: String(r),
                answer: { value: String(2 * r) },
                prompt: msg('generate.tasks.find_limit_as_x', { r }),
            };
        }
        if (kind === 1) {
            const [a, d] = [g.nz(-6, 6), g.nz(-6, 6)];
            return {
                op: 'limit',
                task: `(${poly([a, g.int(-5, 5), g.int(-5, 5)])})/(${poly([d, g.int(-5, 5), g.nz(-5, 5)])})`,
                at: 'inf',
                answer: { value: qs(q(a).div(q(d))) },
                prompt: msg('generate.tasks.find_limit_as_x_2'),
            };
        }
        const [k, m] = [g.nz(1, 7), g.nz(1, 7)];
        return { op: 'limit', task: `sin(${k}x)/(${m}x)`, at: '0', answer: { value: qs(q(k).div(q(m))) }, prompt: msg('generate.tasks.find_limit_as_x_0') };
    },
    'trig-eq-interval'(g) {
        // k(t − c₁)(t − c₂) = 0 with t = cos x or sin x and table values; the roots on [Aπ; Bπ]
        const f = g.pick(['cos', 'sin']);
        // [value, arccos or arcsin of it in units of π]
        const vals =
            f === 'cos'
                ? [
                      [1, 0],
                      [-1, 1],
                      [0, 0.5],
                      [0.5, 1 / 3],
                      [-0.5, 2 / 3],
                  ]
                : [
                      [1, 0.5],
                      [-1, -0.5],
                      [0, 0],
                      [0.5, 1 / 6],
                      [-0.5, -1 / 6],
                  ];
        const [i1, i2] = g.distinct(2, 0, vals.length - 1);
        const [c1, c2] = [vals[i1][0], vals[i2][0]];
        const k = c1 % 1 !== 0 || c2 % 1 !== 0 ? 2 : 1;
        // k(t − c1)(t − c2) = k t² − k(c1 + c2)t + k c1 c2
        const A = k;
        const B = -k * (c1 + c2);
        const C = k * c1 * c2;
        const t = `${f}(x)`;
        const term = (c, pw) => (c === 0 ? '' : `${c < 0 ? ' - ' : ' + '}${Math.abs(c) === 1 && pw ? '' : Math.abs(c)}${pw}`);
        const task = `${A === 1 ? '' : A}${t}^2${term(B, t)}${term(C, '')} = 0`;
        const [lo, hi] = g.pick([
            [-2, -0.5],
            [0, 1.5],
            [1, 2.5],
            [-1, 0.5],
            [1.5, 3],
            [-3, -1.5],
        ]);
        const roots = [];
        for (const [c, base] of [vals[i1], vals[i2]]) {
            const bases = f === 'cos' ? [base, -base] : [base, 1 - base];
            for (const b0 of bases)
                for (let n = -4; n <= 4; n++) {
                    const x = b0 + 2 * n;
                    if (x >= lo - 1e-12 && x <= hi + 1e-12 && !roots.some((y) => Math.abs(y - x) < 1e-12)) roots.push(x);
                }
            void c;
        }
        const piText = (x) => {
            const r = q(Math.round(x * 6)).div(q(6));
            const num = r.n === 1n ? '' : r.n === -1n ? '-' : String(r.n);
            return r.isZero() ? '0' : r.isInt() ? `${num}pi` : `${num}pi/${r.d}`;
        };
        return {
            op: 'solve',
            task,
            interval: [piText(lo), piText(hi)],
            answer: { roots: roots.sort((u, v) => u - v).map(piText) },
            prompt: msg('generate.tasks.solve_and_find_roots_on', { lo: piText(lo), hi: piText(hi) }),
        };
    },
    'log-ineq'(g) {
        const small = g.r() < 0.4;
        const b = g.pick([2, 3, 5]);
        const base = small ? `1/${b}` : `${b}`;
        const k = g.int(0, 3);
        const a = g.nz(-3, 3);
        const c = g.int(-6, 6);
        const op = g.pick(['<', '<=', '>', '>=']);
        // log_base(ax + c) op k ⇔ ax + c op' base^k, with ax + c > 0
        const bound = small ? q(1).div(q(b ** k)) : q(b ** k);
        const up = (op[0] === '>') !== small; // ax + c above the bound
        const closed = op.length === 2;
        const z = q(-c).div(q(a)); // the domain edge
        const w = bound.sub(q(c)).div(q(a)); // where ax + c = bound
        let ans;
        if (a > 0) ans = up ? iv(w, null, closed, false) : iv(z, w, false, closed);
        else ans = up ? iv(null, w, false, closed) : iv(w, z, closed, false);
        return { op: 'ineq', task: `log_(${base})(${poly([a, c])}) ${op} ${k}`, answer: { set: ans }, prompt: msg('generate.tasks.solve_inequality') };
    },
    'exp-ineq'(g) {
        const small = g.r() < 0.4;
        const b = g.pick([2, 3, 5]);
        const base = small ? `(1/${b})` : `${b}`;
        const k = g.int(-2, 3);
        const a = g.nz(-3, 3);
        const c = g.int(-5, 5);
        const op = g.pick(['<', '<=', '>', '>=']);
        const rhs = k < 0 ? (small ? `${b ** -k}` : `1/${b ** -k}`) : small ? (k === 0 ? '1' : `1/${b ** k}`) : `${b ** k}`;
        // base^(ax + c) op base^k ⇔ ax + c op' k (flipped for a small base), then divide by a
        const up = (op[0] === '>') !== small;
        const closed = op.length === 2;
        const w = q(k - c).div(q(a));
        const right = up === a > 0; // x above w
        const ans = right ? iv(w, null, closed, false) : iv(null, w, false, closed);
        return { op: 'ineq', task: `${base}^(${poly([a, c])}) ${op} ${rhs}`, answer: { set: ans }, prompt: msg('generate.tasks.solve_inequality') };
    },
    'rational-eq'(g) {
        // (x − r)(x − s)/(x − r) = 0 written expanded: the root r is extraneous
        const [r, s] = g.distinct(2, -7, 7);
        const c = fromRoots([r, s]);
        return { op: 'solve', task: `(${poly(c)})/(${lin(r)}) = 0`, answer: { roots: [String(s)] }, prompt: SOLVE };
    },
    'nonlinear-system'(g) {
        const [u, w] = g.distinct(2, -6, 6);
        const s = u + w;
        const p = u * w;
        return {
            op: 'system',
            task: `x + y = ${s}; x y = ${p}`,
            answer: {
                solutions: [
                    [String(u), String(w)],
                    [String(w), String(u)],
                ],
            },
            prompt: msg('generate.tasks.solve_system'),
        };
    },
    'abs-eq'(g) {
        if (g.r() < 0.5) {
            const a = g.nz(-4, 4);
            const b = g.int(-8, 8);
            const c = g.int(1, 9);
            const roots = [q(c - b).div(q(a)), q(-c - b).div(q(a))].sort((u, v) => u.cmp(v)).map(qs);
            return { op: 'solve', task: `|${poly([a, b])}| = ${c}`, answer: { roots }, prompt: SOLVE };
        }
        const [a, b] = g.distinct(2, -8, 8);
        return {
            op: 'solve',
            task: `|x ${a < 0 ? '+' : '-'} ${Math.abs(a)}| = |x ${b < 0 ? '+' : '-'} ${Math.abs(b)}|`,
            answer: { roots: [qs(q(a + b).div(q(2)))] },
            prompt: SOLVE,
        };
    },
    antiderivative(g, level) {
        // f = F′ for a random F from a few shapes; F comes with the task (the check differentiates the answer)
        const a = g.nz(-4, 4);
        const b = g.int(-5, 5);
        const n = g.int(2, 5);
        const L = poly([a, b]);
        const R = poly([a, Math.abs(b) + 1]);
        const ax = kx(a);
        const shapes = [
            [`${a * n}(${L})^${n - 1}`, `(${L})^${n}`],
            [`${a}cos(${L})`, `sin(${L})`],
            [`(1 + ${a}x)e^(${ax})`, `x e^(${ax})`],
            [`${a}/(${L})`, `ln(abs(${L}))`],
            [`sin(${ax}) + ${a}x cos(${ax})`, `x sin(${ax})`],
            [`${a}/(2sqrt(${R}))`, `sqrt(${R})`],
            [`x e^(x^2)`, `e^(x^2)/2`],
            [`1/(x^2 + ${n * n})`, `atan(x/${n})/${n}`],
            [`x^2 sin(x^3)`, `-cos(x^3)/3`],
            [`ln(x)`, `x ln(x) - x`],
        ];
        const [f, F] = g.pick(level >= 2 ? shapes : shapes.slice(0, 4));
        return { op: 'integrate', task: f, answer: { expr: F }, prompt: msg('generate.tasks.find_antiderivative') };
    },
    'linear-ineq'(g, level) {
        // a·x + b op c·x + d with the boundary r: (a − c)·r + b = d
        const r = level >= 3 ? q(g.nz(-9, 9)).div(q(g.pick([2, 3, 4]))) : q(g.int(-9, 9));
        const a = g.nz(-6, 6);
        let c = level >= 2 ? g.int(-6, 6) : 0;
        if (c === a) c = a > 0 ? a - 1 : a + 1;
        const b = g.int(-12, 12);
        const d = q(a - c)
            .mul(r)
            .add(q(b));
        const op = g.pick(['<', '<=', '>', '>=']);
        // the inequality holds where (a − c)(x − r) op 0
        const closed = op.length === 2;
        const rightSide = (op[0] === '>') === a - c > 0;
        const set = rightSide ? iv(r, null, closed, false) : iv(null, r, false, closed);
        return { op: 'ineq', task: `${poly([a, b])} ${op} ${poly([c, d])}`, answer: { set }, prompt: msg('generate.tasks.solve_inequality') };
    },
    derivative(g, level) {
        // f and f′ written from the construction (the sum, product, quotient and chain rules by hand)
        const prompt = msg('generate.tasks.find_derivative');
        if (level === 1) {
            const n = g.int(2, 5);
            const m = g.int(1, n - 1);
            const a = g.nz(-6, 6);
            const b = g.nz(-9, 9);
            const c = g.int(-9, 9);
            const pw = (k) => (k === 0 ? '' : k === 1 ? 'x' : `x^${k}`);
            return {
                op: 'diff',
                task: sum([
                    [a, pw(n)],
                    [b, pw(m)],
                    [c, ''],
                ]),
                answer: {
                    expr: sum([
                        [a * n, pw(n - 1)],
                        [b * m, pw(m - 1)],
                    ]),
                },
                prompt,
            };
        }
        const k = g.nz(-3, 3);
        const n = g.int(level >= 3 ? 2 : 1, 4);
        const xn = (p) => (p === 0 ? '' : p === 1 ? 'x' : `x^${p}`);
        if (level === 2) {
            const kind = g.int(0, 2);
            if (kind === 0) {
                // (xⁿ e^(kx))′ = n xⁿ⁻¹ e^(kx) + k xⁿ e^(kx)
                const E_ = `e^(${kx(k)})`;
                return {
                    op: 'diff',
                    task: `${xn(n)} ${E_}`,
                    answer: {
                        expr: sum([
                            [n, `${xn(n - 1)} ${E_}`.trim()],
                            [k, `${xn(n)} ${E_}`],
                        ]),
                    },
                    prompt,
                };
            }
            if (kind === 1) {
                // (xⁿ sin kx)′ = n xⁿ⁻¹ sin kx + k xⁿ cos kx (k > 0: a school argument)
                const p = Math.abs(k);
                const S = `sin(${kx(p)})`;
                const C = `cos(${kx(p)})`;
                return {
                    op: 'diff',
                    task: `${xn(n)} ${S}`,
                    answer: {
                        expr: sum([
                            [n, `${xn(n - 1)} ${S}`.trim()],
                            [p, `${xn(n)} ${C}`],
                        ]),
                    },
                    prompt,
                };
            }
            // ((ax + b)/(cx + d))′ = (ad − bc)/(cx + d)²
            const [a, c] = [g.nz(-5, 5), g.int(1, 4)];
            let b = g.int(-6, 6);
            const d = g.nz(-6, 6);
            if (a * d - b * c === 0) b += 1;
            return { op: 'diff', task: `(${poly([a, b])})/(${poly([c, d])})`, answer: { expr: `${a * d - b * c}/(${poly([c, d])})^2` }, prompt };
        }
        const kind = g.int(0, 3);
        if (kind === 0) {
            // ((ax + b)ⁿ)′ = n·a·(ax + b)ⁿ⁻¹
            const a = g.nz(-4, 4);
            const b = g.nz(-6, 6);
            const m = n + 1;
            return { op: 'diff', task: `(${poly([a, b])})^${m}`, answer: { expr: `${m * a}(${poly([a, b])})^${m - 1}` }, prompt };
        }
        if (kind === 1) {
            // (ln(ax² + b))′ = 2ax/(ax² + b), a, b > 0
            const a = g.int(1, 5);
            const b = g.int(1, 9);
            return { op: 'diff', task: `ln(${poly([a, 0, b])})`, answer: { expr: `${2 * a}x/(${poly([a, 0, b])})` }, prompt };
        }
        if (kind === 2) {
            // (√(ax + b))′ = a/(2√(ax + b)), a, b > 0
            const a = g.int(1, 6);
            const b = g.int(1, 9);
            const root = `sqrt(${poly([a, b])})`;
            return { op: 'diff', task: root, answer: { expr: a % 2 === 0 ? `${a / 2 === 1 ? 1 : a / 2}/${root}` : `${a}/(2${root})` }, prompt };
        }
        // (e^(kx²))′ = 2k·x·e^(kx²)
        return { op: 'diff', task: `e^(${kx(k, 'x^2')})`, answer: { expr: `${2 * k}x e^(${kx(k, 'x^2')})` }, prompt };
    },
};

export const TASK_KINDS = Object.freeze(Object.keys(GEN));

/** One task of a kind, reproducible by its seed; level 1–3. */
export function generateTask(kind, opts = {}) {
    const gen = GEN[kind];
    if (!gen) throw new Error(`unknown task kind ${kind}; known: ${TASK_KINDS.join(', ')}`);
    const seed = opts.seed ?? Math.floor(Math.random() * 2 ** 31);
    const level = Math.min(3, Math.max(1, opts.level ?? 1));
    const t = gen(rng(seed * 97 + level), level);
    return { family: kind, level, seed, ...t };
}

/** A reproducible batch: count tasks from consecutive seeds, duplicates skipped. */
export function generateSet(kind, opts = {}) {
    const count = opts.count ?? 10;
    const out = [];
    const seen = new Set();
    for (let s = opts.seed ?? 1; out.length < count && s < (opts.seed ?? 1) + count * 20; s++) {
        const t = generateTask(kind, { ...opts, seed: s });
        const key = t.task + JSON.stringify(t.bounds ?? t.segment ?? t.at ?? '');
        if (seen.has(key)) continue;
        seen.add(key);
        out.push(t);
    }
    return out;
}
