// architecture: the layers of the engine and the rules between them, checked on the import graph.
//
// A unit is a directory of src/ (numbers/theory, calculus/limit, …) or a top-level file (api.js, index.js). Units form
// layers; a module imports only from its own unit or from a lower layer. Units in one layer do not import each other.
const { test } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const SRC = path.join(__dirname, '../src');

// lowest first
const LAYERS = [
    ['i18n'], //                                    words and notation of every language
    ['core'], //                                    numbers, expressions, parse, print, simplify, polynomials, steps
    ['numbers/theory', 'numbers/numeric'], //       calculators over integers and floats
    ['linalg'], //                                  matrices over Q (and floats)
    ['algebra'], //                                 values and transformations step by step
    ['solve'], //                                   equations, inequalities, systems
    ['calculus/display'], //                        what every calculus module shares
    ['calculus/derivative'],
    ['calculus/limit'],
    ['calculus/integral', 'calculus/series'],
    ['calculus/extrema', 'calculus/ode'],
    ['problems', 'generate'], //                    composite school tasks, task generators
    ['api'], //                                     the public contract of the solvers
    ['index'], //                                   the package
];
const layerOf = new Map(LAYERS.flatMap((units, i) => units.map((u) => [u, i])));

const files = [];
const walk = (d) =>
    fs.readdirSync(d).forEach((f) => {
        const p = path.join(d, f);
        if (fs.statSync(p).isDirectory()) walk(p);
        else if (p.endsWith('.js')) files.push(p);
    });
walk(SRC);

const unitOf = (file) => {
    const parts = path.relative(SRC, file).replace(/\.js$/, '').split(path.sep);
    if (parts.length === 1) return parts[0];
    if ((parts[0] === 'numbers' || parts[0] === 'calculus') && parts.length > 2) return `${parts[0]}/${parts[1]}`;
    if (parts[0] === 'calculus') return `calculus/${parts[1]}`;
    return parts[0];
};
const unitDir = (unit) => path.join(SRC, unit);
const hasIndex = (unit) => fs.existsSync(path.join(unitDir(unit), 'index.js'));

// file → [imported file]
const imports = new Map(
    files.map((f) => {
        const text = fs.readFileSync(f, 'utf8');
        const out = [];
        for (const m of text.matchAll(/(?:\bfrom\s+|\bimport\s*\(\s*|^import\s+)['"](\.{1,2}\/[^'"]+)['"]/gm)) out.push(path.resolve(path.dirname(f), m[1]));
        return [f, out];
    }),
);
const rel = (f) => path.relative(SRC, f);

test('every unit has a layer', () => {
    const missing = [...new Set(files.map(unitOf))].filter((u) => !layerOf.has(u));
    assert.deepEqual(missing, [], 'units missing from LAYERS');
});

test('a module imports only its own unit or lower layers', () => {
    const bad = [];
    for (const [f, targets] of imports) {
        const a = unitOf(f);
        for (const t of targets) {
            const b = unitOf(t);
            if (a !== b && !(layerOf.get(b) < layerOf.get(a))) bad.push(`${rel(f)} → ${rel(t)} (${a} may not use ${b})`);
        }
    }
    assert.deepEqual(bad, []);
});

test('no import cycles, not even inside a unit', () => {
    const state = new Map();
    const cycles = [];
    const visit = (f, stack) => {
        state.set(f, 'open');
        stack.push(f);
        for (const t of imports.get(f) ?? []) {
            if (state.get(t) === 'open') cycles.push(stack.slice(stack.indexOf(t)).concat(t).map(rel).join(' → '));
            else if (!state.has(t)) visit(t, stack);
        }
        stack.pop();
        state.set(f, 'done');
    };
    for (const f of files) if (!state.has(f)) visit(f, []);
    assert.deepEqual(cycles, []);
});

test('another unit is entered through its index.js', () => {
    const bad = [];
    for (const [f, targets] of imports)
        for (const t of targets) {
            const b = unitOf(t);
            if (b === unitOf(f) || !hasIndex(b)) continue;
            if (t !== path.join(unitDir(b), 'index.js')) bad.push(`${rel(f)} → ${rel(t)}`);
        }
    assert.deepEqual(bad, []);
});

test('the package index and the api are imported only from above', () => {
    const bad = [];
    for (const [f, targets] of imports)
        for (const t of targets) {
            if (t === path.join(SRC, 'index.js')) bad.push(`${rel(f)} imports the package index`);
            if (t === path.join(SRC, 'api.js') && unitOf(f) !== 'index') bad.push(`${rel(f)} imports api.js`);
        }
    assert.deepEqual(bad, []);
});

test('a module speaks from its own catalog domain', () => {
    // msg('solve.trig.…') belongs in src/solve/; the api layer has the domain 'api'
    const bad = [];
    for (const f of files) {
        if (unitOf(f) === 'i18n') continue;
        const dir = path.relative(SRC, f).replace(/\.js$/, '').split(path.sep);
        const domain = (dir.length === 1 ? dir : dir.slice(0, -1)).join('.');
        const text = fs.readFileSync(f, 'utf8');
        for (const m of text.matchAll(/\bmsg\(\s*['`]([\w.]+?)(?:\$\{|['`])/g)) if (!`${m[1]}.`.startsWith(`${domain}.`)) bad.push(`${rel(f)}: ${m[1]}`);
    }
    assert.deepEqual(bad, []);
});

test('every module opens with its path and what it holds', () => {
    // «// solve/trig — trigonometric equations: …»; the catalogs of a language say whose messages they hold
    const bad = [];
    for (const f of files) {
        let name = path.relative(SRC, f).replace(/\.js$/, '').split(path.sep).join('/');
        if (name === 'index' || /^i18n\/[^/]+\//.test(name)) continue;
        name = name.replace(/\/index$/, '');
        const first = fs.readFileSync(f, 'utf8').split('\n', 1)[0];
        if (!first.startsWith(`// ${name} — `)) bad.push(`${rel(f)}: ${first.slice(0, 60)}`);
    }
    assert.deepEqual(bad, []);
});

test('every module loads', async () => {
    for (const f of files) await import(f);
});
