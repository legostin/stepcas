// The demo's engine side: how each mode calls stepcas. No DOM, so the worker and the tests share it.
// run(mode, fields, lang) always returns a plain view (strings, numbers, arrays) that crosses postMessage.
import * as E from '../src/index.js';
import { MODE } from './modes.js';

const opt = (s) => (s == null || String(s).trim() === '' ? undefined : String(s).trim());

// mode → its call of the engine, on the fields of modes.js
const SOLVE = {
    equation: (f) => E.solveEquation(f.q, opt(f.v) ?? null, { domain: f.complex ? 'complex' : 'real', interval: opt(f.interval) }),
    inequality: (f) => E.solveInequality(f.q, opt(f.v) ?? null),
    system: (f) => {
        const rels = f.q.split(/\n|;/).filter((s) => s.trim());
        const method = opt(f.method);
        const r = E.solveLinearSystem(rels, null, { method });
        // automatic: a system that is not linear goes to substitution
        return r.ok || method || r.kind === 'invalid' ? r : E.solveSystem2(rels);
    },
    parameter: (f) => {
        const want = /^\d+$/.test(f.want ?? '') ? Number(f.want) : (opt(f.want) ?? 'two-roots');
        return E.solveWithParameter(f.q, { param: opt(f.param) ?? 'a', want });
    },
    derivative: (f) => {
        const n = Number(opt(f.n) ?? 1);
        return n > 1 ? E.derivativeN(f.q, opt(f.v) ?? 'x', n) : E.derivative(f.q, opt(f.v) ?? 'x');
    },
    integral: (f) => {
        const v = opt(f.v) ?? 'x';
        return opt(f.a) && opt(f.b) ? E.integrateDefinite(f.q, v, opt(f.a), opt(f.b)) : E.integrate(f.q, v);
    },
    limit: (f) => E.limit(f.q, opt(f.v) ?? 'x', opt(f.at) ?? '0', { side: opt(f.side) }),
    extremum: (f) => {
        const v = opt(f.v) ?? 'x';
        return opt(f.a) && opt(f.b) ? E.extremeOnSegment(f.q, v, opt(f.a), opt(f.b), { kind: opt(f.kind) ?? 'max' }) : E.extremePoints(f.q, v);
    },
    taylor: (f) => E.taylorPolynomial(f.q, opt(f.v) ?? 'x', opt(f.at) ?? '0', Number(opt(f.n) ?? 4)),
    ode: (f) => E.solveOde(f.q),
    series: (f) => E.sumSeries(`sum(${f.q}, ${opt(f.k) ?? 'k'}, ${opt(f.a) ?? '1'}, ${opt(f.b) ?? 'inf'})`),
    value: (f) => E.evaluateSteps(f.q),
    algebra: (f) => ({ factor: E.factorSteps, expand: E.expandSteps, simplify: E.simplifySteps })[f.op || 'factor'](f.q),
    numbers: (f) => calc(NT[f.op || 'gcd'], f.q),
    matrices: (f) => calc(MAT[f.op || 'det'], f.q, f.b),
};

// the error position points into the main field only where the engine parses that field as it is
const NO_POSITION = new Set(['series', 'numbers', 'matrices', 'system']);

// ---------------------------------------------------------------- calculators: a value, its TeX, and the steps

const ints = (s, n) => {
    const list = String(s ?? '')
        .split(/[\s,;]+/)
        .filter(Boolean);
    if (n && list.length !== n) throw new Error(`Type ${n} number${n > 1 ? 's' : ''}, separated by commas.`);
    return list;
};

const NT = {
    gcd: {
        run: (s) => {
            const [a, b] = ints(s, 2);
            const r = E.ntGcd(a, b, { steps: true });
            return [r, `\\gcd(${a}, ${b}) = ${r.value}`];
        },
    },
    lcm: {
        run: (s) => {
            const [a, b] = ints(s, 2);
            const r = E.ntLcm(a, b, { steps: true });
            return [r, `\\operatorname{lcm}(${a}, ${b}) = ${r.value}`];
        },
    },
    factor: {
        run: (s) => {
            const [n] = ints(s, 1);
            const r = E.ntFactor(n, { steps: true });
            return [r, `${n} = ${r.tex}`];
        },
    },
    phi: {
        run: (s) => {
            const [n] = ints(s, 1);
            const r = E.ntPhi(n, { steps: true });
            return [r, `\\varphi(${n}) = ${r.value}`];
        },
    },
    prime: {
        run: (s) => {
            const [n] = ints(s, 1);
            const r = E.ntMillerRabin(n, { steps: true });
            return [r, `${n}\\ \\text{is ${r.prime ? 'prime' : 'composite'}}`];
        },
    },
    modpow: {
        run: (s) => {
            const [a, e, m] = ints(s, 3);
            const r = E.ntModPow(a, e, m, { steps: true });
            return [r, `${a}^{${e}} \\equiv ${r.value} \\pmod{${m}}`];
        },
    },
    modinv: {
        run: (s) => {
            const [a, m] = ints(s, 2);
            const r = E.ntModInv(a, m, { steps: true });
            return [r, r.value == null ? '\\text{no inverse}' : `${a}^{-1} \\equiv ${r.value} \\pmod{${m}}`];
        },
    },
    congruence: {
        run: (s) => {
            const r = E.ntSolveCongruence(...ints(s, 3), { steps: true });
            return [r, r.solvable ? r.steps.at(-1).tex : '\\text{no solutions}'];
        },
    },
    diophantine: {
        run: (s) => {
            const r = E.ntDiophantine(...ints(s, 3), { steps: true });
            return [r, r.solvable ? r.steps.at(-1).tex : '\\text{no integer solutions}'];
        },
    },
    crt: {
        run: (s) => {
            const pairs = String(s)
                .split(/[,;\n]+/)
                .filter((p) => p.trim())
                .map((p) => p.match(/^\s*(-?\d+)\s*\(?\s*mod\s*(\d+)\s*\)?\s*$/i));
            if (!pairs.length || pairs.some((p) => !p)) throw new Error('Type congruences like: 2 mod 3, 3 mod 5, 2 mod 7');
            const r = E.ntCrt(
                pairs.map((p) => p[1]),
                pairs.map((p) => p[2]),
                { steps: true },
            );
            return [r, r.solvable ? `x \\equiv ${r.x} \\pmod{${r.m}}` : '\\text{no solutions}'];
        },
    },
    base: {
        run: (s) => {
            const [x, base] = ints(s, 2);
            const r = E.ntToBase(x, base, { steps: true });
            return [r, E.eachLanguage((lang) => `${x} = ${E.inLanguage(r.tex, lang)}`)];
        },
    },
    cf: {
        run: (s) => {
            const t = String(s).trim();
            const root = t.match(/^(?:sqrt\s*\(?\s*|√\s*)(\d+)\)?$/i);
            const r = E.ntContinuedFraction(root ? { sqrt: root[1] } : t, { steps: true });
            return [r, r.tex];
        },
    },
    rsa: {
        run: (s) => {
            const r = E.ntRsaKey(...ints(s, 2), { steps: true });
            return [r, `n = ${r.n},\\quad e = ${r.e},\\quad d = ${r.d}`];
        },
    },
    divisibility: {
        run: (s) => {
            const [n, d] = ints(s, 2);
            const r = E.ntDivisibilityRule(n, d);
            return [r, `${n}\\ ${r.divides ? '\\vdots' : '\\not\\vdots'}\\ ${d}`];
        },
    },
};

const matrix = (s) => {
    const rows = String(s ?? '')
        .replace(/[[\]()]/g, ' ')
        .split(/\n|;/)
        .map((r) => r.split(/[\s,]+/).filter(Boolean))
        .filter((r) => r.length);
    if (!rows.length) throw new Error('Type the matrix row by row: 2 1; 1 3');
    if (rows.some((r) => r.length !== rows[0].length)) throw new Error('Every row needs the same number of entries.');
    return E.Matrix.from(rows);
};

const MAT = {
    det: {
        run: (s) => {
            const r = E.matDet(matrix(s), { steps: true });
            return [r, `\\det A = ${r.value.toTex()}`];
        },
    },
    inverse: {
        run: (s) => {
            const r = E.matInverse(matrix(s), { steps: true });
            return [r, r.value ? `A^{-1} = ${r.value.toTex()}` : '\\text{no inverse: } \\det A = 0'];
        },
    },
    rref: {
        run: (s) => {
            const r = E.matRref(matrix(s), { steps: true });
            return [r, `${r.matrix.toTex()},\\quad \\operatorname{rank} A = ${r.rank}`];
        },
    },
    eigen: {
        run: (s) => {
            const r = E.matEigen(matrix(s), { steps: true });
            return [r, r.values.map((v, i) => `\\lambda_{${i + 1}} = ${v.tex}`).join(',\\quad ')];
        },
    },
    diagonalize: {
        run: (s) => {
            const r = E.matDiagonalize(matrix(s), { steps: true });
            return [r, r.diagonalizable ? `P = ${r.P.toTex()},\\quad D = ${r.D.toTex()}` : '\\text{not diagonalisable over } \\mathbb{Q}'];
        },
    },
    solve: {
        run: (s, b) => {
            const r = E.matSolve(matrix(s), ints(b), { steps: true });
            return [r, r.kind === 'none' ? '\\text{no solutions}' : r.tex];
        },
    },
};

function calc(op, s, b) {
    if (!op) throw new Error('Pick what to find.');
    const [r, tex] = op.run(s, b);
    return { ok: true, kind: 'value', answer: { tex, text: null }, steps: r.steps ?? [] };
}

// ---------------------------------------------------------------- the view

const texOf = (x) => (typeof x === 'string' ? x : null);

function cleanSteps(steps) {
    return (steps ?? []).map((s) => ({
        title: texOf(s.title) ?? '',
        tex: texOf(s.tex),
        text: texOf(s.text),
        rule: texOf(s.rule),
        final: !!s.final,
        sub: s.sub?.length ? cleanSteps(s.sub) : null,
    }));
}

// what the parser read in the main field, as TeX: shows how "1/2x" or "sin x^2" were understood
function preview(mode, f, lang) {
    if (mode.fields.find((x) => x.main)?.noPreview || !opt(f.q)) return null;
    const p = E.tryParse(mode.id === 'system' ? f.q.replace(/\n+/g, ';') : f.q);
    return p.ok ? E.toTex(p.node, { lang }) : null;
}

export function run(modeId, fields, lang = 'en') {
    const mode = MODE[modeId];
    const f = { ...fields };
    const t0 = performance.now();
    let r;
    try {
        if (!mode) throw new Error(`Unknown mode ${modeId}`);
        r = E.localize(SOLVE[modeId](f), lang);
    } catch (e) {
        const reason = e?.msg ? E.localize(e.msg, lang) : String(e?.message ?? e);
        r = { ok: false, kind: e?.msg ? 'invalid' : 'error', reason, steps: [] };
    }
    const ms = performance.now() - t0;
    const view = {
        ok: !!r.ok,
        kind: r.kind ?? null,
        method: texOf(r.method) ?? texOf(r.type) ?? null,
        answerTex: r.ok ? texOf(r.answer?.tex) : null,
        answerText: r.ok ? texOf(r.answer?.text) : null,
        extras: [],
        reason: r.ok ? null : (texOf(r.reason) ?? 'No answer'),
        pos: !r.ok && !NO_POSITION.has(modeId) && Number.isInteger(r.pos) ? r.pos : null,
        len: !r.ok && Number.isInteger(r.len) ? r.len : null,
        steps: cleanSteps(r.steps),
        ms,
        read: null,
    };
    if (r.ok && r.inInterval?.length) {
        const sep = lang === 'ru' ? ';\\ ' : ',\\ ';
        view.extras.push({
            label: lang === 'ru' ? 'Корни на промежутке' : 'Roots in the interval',
            tex: r.inInterval.map((x) => E.toTex(x.node, { lang })).join(sep),
        });
    }
    try {
        if (mode) view.read = preview(mode, f, lang);
    } catch {}
    return view;
}

// ---------------------------------------------------------------- a generated task as the mode's fields

export function randomTask(modeId, seed) {
    const mode = MODE[modeId];
    if (!mode?.families?.length) return null;
    const family = mode.families[seed % mode.families.length];
    const t = E.generateTask(family, { seed, level: 1 + (seed % 3) });
    const s = (x) => (x == null ? '' : typeof x === 'string' ? x : E.toText(E.asNode(x), { lang: 'en' }));
    const f = { q: t.task };
    if (t.interval) f.interval = `[${s(t.interval[0])}; ${s(t.interval[1])}]`;
    if (t.segment) [f.a, f.b, f.kind] = [s(t.segment[0]), s(t.segment[1]), t.kind];
    if (t.bounds) [f.a, f.b] = [s(t.bounds[0]), s(t.bounds[1])];
    if (t.at != null) f.at = s(t.at);
    if (t.param) [f.param, f.want] = [t.param, String(t.want)];
    if (t.op === 'factor') f.op = 'factor';
    if (t.op === 'simplify') f.op = 'simplify';
    if (modeId === 'series') {
        const m = t.task.match(/^sum\((.*),\s*(\w+),\s*([^,]+),\s*([^,]+)\)$/);
        if (m) Object.assign(f, { q: m[1], k: m[2], a: m[3], b: m[4] });
    }
    return { fields: f, prompt: E.localize(t.prompt, 'en') };
}
