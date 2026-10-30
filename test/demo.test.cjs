// demo: every example on the demo page (demo/examples.js) solves with steps in both languages, the generated tasks
// behind «Random task» solve too, and a view is plain data that crosses postMessage.
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let run;
let randomTask;
let MODES;
let EXAMPLES;
before(async () => {
    ({ run, randomTask } = await import('../demo/run.js'));
    ({ MODES } = await import('../demo/modes.js'));
    ({ EXAMPLES } = await import('../demo/examples.js'));
});

test('every mode has examples, and every example solves with steps in English and Russian', () => {
    for (const m of MODES) {
        assert.ok(EXAMPLES[m.id]?.length >= 5, `${m.id}: at least five examples`);
        for (const ex of EXAMPLES[m.id]) {
            for (const lang of ['en', 'ru']) {
                const v = run(m.id, ex.f, lang);
                const where = `${m.id} ${JSON.stringify(ex.f)} (${lang})`;
                assert.ok(v.ok, `${where}: ${v.reason}`);
                assert.equal(typeof v.answerTex, 'string', `${where}: the answer in TeX`);
                assert.ok(v.steps.length > 0, `${where}: steps`);
            }
        }
    }
});

test('an example’s fields are fields of its mode', () => {
    for (const m of MODES) {
        const keys = new Set(m.fields.map((f) => f.key));
        for (const ex of EXAMPLES[m.id]) for (const k of Object.keys(ex.f)) assert.ok(keys.has(k), `${m.id}: unknown field ${k}`);
    }
});

test('Random task: generated tasks fill the form and solve', () => {
    for (const m of MODES.filter((x) => x.families)) {
        for (let seed = 1; seed <= 2 * m.families.length; seed++) {
            const t = randomTask(m.id, seed);
            const v = run(m.id, t.fields, 'en');
            assert.ok(v.ok, `${m.id} seed ${seed} ${JSON.stringify(t.fields)}: ${v.reason}`);
        }
    }
});

test('a view is plain data: it survives structuredClone, and failures carry a reason', () => {
    const v = run('integral', { q: 'x cos x' }, 'en');
    assert.deepEqual(structuredClone(v), v);
    const bad = run('equation', { q: '2x + = 3' }, 'en');
    assert.equal(bad.ok, false);
    assert.equal(bad.pos, 5);
    assert.equal(typeof bad.reason, 'string');
    const nt = run('numbers', { q: '1, 2, 3', op: 'gcd' }, 'en');
    assert.equal(nt.ok, false);
    assert.match(nt.reason, /Type 2 numbers/);
});
