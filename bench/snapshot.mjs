// The golden record: every corpus task's status, answer and steps rendered in every language, as JSON.
// A refactoring must leave it unchanged (or change it on purpose).
//   node bench/snapshot.mjs [--out bench/out/snapshot.json]      write
//   node bench/snapshot.mjs --compare a.json b.json               list the tasks that differ
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const argv = process.argv.slice(2);

if (argv[0] === '--compare') {
    const [a, b] = [argv[1], argv[2]].map((f) => JSON.parse(fs.readFileSync(f, 'utf8')));
    const ids = [...new Set([...Object.keys(a), ...Object.keys(b)])];
    let n = 0;
    for (const id of ids) {
        const x = JSON.stringify(a[id]);
        const y = JSON.stringify(b[id]);
        if (x === y) continue;
        if (n++ < 12) {
            let i = 0;
            while (i < x?.length && x[i] === y?.[i]) i++;
            console.log(`${id}\n  before …${x?.slice(Math.max(0, i - 80), i + 120)}\n  after  …${y?.slice(Math.max(0, i - 80), i + 120)}`);
        }
    }
    console.log(`${n} of ${ids.length} tasks differ`);
    process.exit(n ? 1 : 0);
}

const { runTask, lastResult } = await import('./lib/runner.mjs');
const out = argv.includes('--out') ? argv[argv.indexOf('--out') + 1] : path.join(here, 'out', 'snapshot.json');

const tasks = [];
const walk = async (dir) => {
    for (const f of fs.readdirSync(dir).sort()) {
        const p = path.join(dir, f);
        if (fs.statSync(p).isDirectory()) await walk(p);
        else if (f.endsWith('.mjs') && !f.startsWith('_')) tasks.push(...(await import(p)).default);
    }
};
await walk(path.join(here, 'tasks'));
for (const f of fs.readdirSync(path.join(here, 'gen')).filter((x) => x.endsWith('.json'))) tasks.push(...JSON.parse(fs.readFileSync(path.join(here, 'gen', f), 'utf8')));

const LANGS = ['ru', 'en'];
// a bilingual value (a {ru, en} object, a message with language getters, or a plain string) → {ru, en}
const text = (x) => {
    if (x == null) return undefined;
    if (typeof x === 'string') return x;
    if (typeof x === 'object' && LANGS.every((l) => l in x || typeof x[l] === 'string')) return Object.fromEntries(LANGS.map((l) => [l, x[l]]));
    return String(x);
};
const stepOut = (s) => ({ title: text(s.title), tex: text(s.tex), text: text(s.text), rule: s.rule, final: s.final || undefined, sub: s.sub?.map(stepOut) });
const record = {};
for (const t of tasks) {
    let res;
    try {
        res = runTask(t);
    } catch (e) {
        res = { status: 'error', note: String(e?.message ?? e) };
    }
    const r = lastResult();
    record[t.id] = { status: res.status, got: res.got === undefined ? undefined : String(res.got), answer: r?.answer ? { tex: text(r.answer.tex), text: text(r.answer.text) } : undefined, steps: Array.isArray(r?.steps) ? r.steps.map(stepOut) : undefined };
}
// API calls outside the corpus: number theory, matrices, calculus options, parse errors — every result in full
const E = await import('../src/index.js');
const ser = (x, depth = 0) => {
    if (depth > 14) return '…';
    if (x == null || typeof x === 'number' || typeof x === 'boolean' || typeof x === 'string') return x;
    if (typeof x === 'bigint') return `${x}n`;
    if (typeof x === 'function') return undefined;
    if (x instanceof E.Q) return `q:${x.toString()}`;
    if (x instanceof E.IntervalSet) return `set:${x.toText('en')}`;
    if (x instanceof E.Matrix) return `matrix:${x.toString()}`;
    if (typeof x.type === 'string' && ['num', 'sym', 'add', 'mul', 'div', 'neg', 'pow', 'fn', 'rel', 'chain', 'list'].includes(x.type)) {
        try {
            return `node:${E.toText(x, { lang: 'en' })}`;
        } catch {
            return 'node:?';
        }
    }
    if (Array.isArray(x)) return x.map((y) => ser(y, depth + 1));
    if (LANGS.every((l) => typeof x[l] === 'string')) return Object.fromEntries(LANGS.map((l) => [l, x[l]]));
    const o = {};
    for (const k of Object.keys(x).sort()) o[k] = ser(x[k], depth + 1);
    return o;
};
const M3 = [[2, 1, -1], [-3, -1, 2], [-2, 1, 2]];
const calls = {
    ntGcd: () => E.ntGcd(84n, 36n, { steps: true }),
    ntLcm: () => E.ntLcm(84n, 36n, { steps: true }),
    ntEgcd: () => E.ntEgcd(240n, 46n, { steps: true }),
    ntDiophantine: () => E.ntDiophantine(3n, 5n, 7n, { steps: true }),
    ntMillerRabin: () => E.ntMillerRabin(561n, { steps: true }),
    ntFactor: () => E.ntFactor(360n, { steps: true }),
    ntPhi: () => E.ntPhi(36n, { steps: true }),
    ntModPow: () => E.ntModPow(3n, 200n, 13n, { steps: true }),
    ntModInv: () => E.ntModInv(3n, 11n, { steps: true }),
    ntSolveCongruence: () => E.ntSolveCongruence(4n, 6n, 10n, { steps: true }),
    ntCrt: () => E.ntCrt([2n, 3n, 2n], [3n, 5n, 7n], { steps: true }),
    ntRsaKey: () => E.ntRsaKey(61n, 53n, { steps: true }),
    ntToBase: () => E.ntToBase(255n, 2, { steps: true }),
    ntFromBase: () => E.ntFromBase('ff', 16, { steps: true }),
    ntContinuedFraction: () => E.ntContinuedFraction(E.Q.of('415/93'), { steps: true }),
    ntEgyptian: () => E.ntEgyptian(E.Q.of('4/13'), { steps: true }),
    ntDivisibilityRule: () => E.ntDivisibilityRule(1234n, 3n),
    ntDivisibilityRule11: () => E.ntDivisibilityRule(918082n, 11n),
    matDet: () => E.matDet(M3, { steps: true }),
    matInverse: () => E.matInverse(M3, { steps: true }),
    matSolve: () => E.matSolve(M3, [8, -11, -3], { steps: true }),
    matSolveCramer: () => E.matSolveCramer(M3, [8, -11, -3], { steps: true }),
    matSolveNone: () => E.matSolve([[1, 2], [2, 4]], [1, 3], { steps: true }),
    matSolveMany: () => E.matSolve([[1, 2], [2, 4]], [1, 2], { steps: true }),
    matCharPoly: () => E.matCharPoly([[2, 1], [1, 2]], { steps: true }),
    matEigen: () => E.matEigen([[4, 1], [2, 3]], { steps: true }),
    matDiagonalize: () => E.matDiagonalize([[4, 1], [2, 3]], { steps: true }),
    matNullspace: () => E.matNullspace([[1, 2, 3], [2, 4, 6]], { steps: true }),
    matGramSchmidt: () => E.matGramSchmidt([[1, 1, 0], [1, 0, 1]], { steps: true }),
    matLeastSquares: () => E.matLeastSquares([[1, 1], [1, 2], [1, 3]], [1, 2, 2], { steps: true }),
    derivativeN: () => E.derivativeN('x^3 e^x', 'x', 2, { steps: true }),
    partialDerivative: () => E.partialDerivative('x^2 y + sin(x y)', 'y', { steps: true }),
    gradientOf: () => E.gradientOf('x^2 + x y', ['x', 'y'], { steps: true }),
    tangentLine: () => E.tangentLine('x^2', 'x', 1, { steps: true }),
    limitSides: () => E.limit('abs(x)/x', 'x', 0, { steps: true }),
    integrateDefinite: () => E.integrateDefinite('1/x^2', 'x', '1', 'inf', { steps: true }),
    integrateRefused: () => E.integrate('e^(x^2)', 'x', { steps: true }),
    solveTrig: () => E.solveTrig('sin(x) = 1/2', 'x', { steps: true }),
    checkRoot: () => E.checkRoot('x^2 = 4', 'x', 2),
    solveLinearSystem: () => E.solveLinearSystem(['x + y = 3', 'x - y = 1'], ['x', 'y'], { steps: true }),
    solveSystem2: () => E.solveSystem2(['x + y = 5', 'x y = 6'], ['x', 'y'], { steps: true }),
    doubleIneq: () => E.solveInequality('-1 < 2x + 1 <= 5', 'x', { steps: true }),
    ineqParam: () => E.solveInequality('a x > 1', 'x', { steps: true }),
    eqParam: () => E.solveEquation('a x = 1', 'x', { steps: true }),
    extremePoints: () => E.extremePoints('x^3 - 3x', 'x', { steps: true }),
    odeUnsupported: () => E.solveOde("y'' = y y'"),
    seriesNumeric: () => E.sumSeries('sum(1/k^3, k, 1, inf)'),
    factorIrreducible: () => E.factorSteps('x^2 + x + 1'),
    simplifyFraction: () => E.simplifySteps('(x^3 - 1)/(x^2 - 1)'),
    generateAll: () => E.TASK_KINDS.map((k) => E.generateTask(k, { seed: 3, level: 2 })),
};
const badInputs = ['2 +', '(x + 1', 'sin', 'x ** 2', '1/', 'log_(x)', 'foo(x)', '', 'x = = 2', '3..4', 'sqrt()', '[1, 2', 'x^', '2 3 +'];
const extras = {};
for (const [name, f] of Object.entries(calls)) {
    try {
        extras[name] = ser(f());
    } catch (e) {
        extras[name] = { thrown: ser(e.msg ?? String(e.message)) };
    }
}
for (const s of badInputs) {
    try {
        E.parse(s);
        extras[`parse:${s}`] = 'ok';
    } catch (e) {
        extras[`parse:${s}`] = { thrown: ser(e.msg ?? String(e.message)), pos: e.pos, code: e.code };
    }
}
record.__extras = extras;
fs.mkdirSync(path.dirname(out), { recursive: true });
fs.writeFileSync(out, JSON.stringify(record));
console.log(`${tasks.length} tasks → ${path.relative(process.cwd(), out)}`);
