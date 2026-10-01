// Task generators: reproducible by seed, every kind at every level, answers that the engine agrees with.
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E;
before(async () => {
    E = await import('../src/index.js');
});

test('the same seed gives the same task; different seeds vary', () => {
    for (const kind of E.TASK_KINDS) {
        const a = E.generateTask(kind, { seed: 42, level: 2 });
        const b = E.generateTask(kind, { seed: 42, level: 2 });
        assert.deepEqual(a, b, kind);
        assert.equal(a.family, kind);
        assert.ok(a.prompt.ru && a.prompt.en, kind);
        const many = new Set(E.generateSet(kind, { count: 8, seed: 1, level: 2 }).map((t) => t.task + JSON.stringify(t.bounds ?? t.segment ?? t.at ?? '')));
        assert.equal(many.size, 8, `${kind}: duplicates`);
    }
    assert.throws(() => E.generateTask('no-such-kind'));
});

test('generated equations and values are solved with the constructed answer', () => {
    const num = (s) => E.evaluate(E.parse(String(s)), {});
    for (let seed = 1; seed <= 15; seed++) {
        for (const level of [1, 2, 3]) {
            const q = E.generateTask('quadratic-eq', { seed, level });
            const r = E.solveEquation(q.task, 'x');
            if (q.answer.none) assert.equal(r.kind, 'none', q.task);
            else
                assert.deepEqual(
                    r.roots.map((z) => z.approx).sort((u, v) => u - v),
                    q.answer.roots.map(num).sort((u, v) => u - v),
                    q.task,
                );
            const v = E.generateTask('log-value', { seed, level });
            assert.ok(Math.abs(num(E.toText(E.evaluateSteps(v.task).value)) - num(v.answer.value)) < 1e-9, v.task);
            const t = E.generateTask('trig-value', { seed, level });
            assert.ok(Math.abs(E.evaluateSteps(t.task).approx - num(t.answer.value)) < 1e-9, t.task);
        }
    }
});

test('linear inequalities and derivatives: the engine agrees with the construction; ODE answers read well', () => {
    for (let seed = 1; seed <= 200; seed++) {
        for (const level of [1, 2, 3]) {
            const li = E.generateTask('linear-ineq', { seed, level });
            const r = E.solveInequality(li.task, 'x');
            assert.ok(r.ok && r.set.equals(E.parseIntervalSet(li.answer.set)), `${li.task}: ${r.set?.toText('en')} vs ${li.answer.set}`);
            const d = E.generateTask('derivative', { seed, level });
            const dr = E.derivative(d.task, 'x');
            assert.ok(dr.ok && E.equivalent(dr.result, E.parse(d.answer.expr)), `${d.task}: ${dr.ok && E.toText(dr.result)} vs ${d.answer.expr}`);
            const o = E.generateTask('ode', { seed, level });
            assert.ok(!/e\^\(-?1x\)|(^|[^\d])1e\^|e\^\(0x\)/.test(o.answer.expr), `ode answer ${o.answer.expr}`);
        }
    }
});
