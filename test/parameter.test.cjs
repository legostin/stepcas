// Equations with a parameter: the quadratic way and the graphical way.
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E;
before(async () => {
    E = await import('../src/index.js');
});
const P = (task, want) => E.solveWithParameter({ task, param: 'a', want });
const same = (r, ref) => E.intervalEquals(r.set, E.parseIntervalSet(ref), 'en');

test('quadratic in x: the leading coefficient and the discriminant', () => {
    const cases = [
        ['x^2 - 2a x + 4 = 0', 'two-roots', '(-inf; -2) U (2; +inf)'],
        ['x^2 + 4x + a = 0', 'two-roots', '(-inf; 4)'],
        ['a x^2 + 2x + 1 = 0', 'one-root', '{0} U {1}'],
        ['x^2 - (a + 1)x + a = 0', 'one-root', '{1}'],
        ['(a - 1)x^2 + 2x - 3 = 0', 'one-root', '{2/3} U {1}'],
        ['x^2 + a x + 9 = 0', 'no-roots', '(-6; 6)'],
    ];
    for (const [task, want, ref] of cases) {
        const r = P(task, want);
        assert.equal(r.method, 'quadratic', task);
        assert.ok(same(r, ref), `${task}: ${r.text}`);
        assert.ok(r.steps.at(-1).final);
    }
});

test('the graphical way: a = g(x), monotone pieces, levels', () => {
    const cases = [
        ['|x - 2| = a', 'two-roots', '(0; +inf)'],
        ['sqrt(x) = a - x', 'has-roots', '[0; +inf)'],
        ['x^3 - 3x = a', 3, '(-2; 2)'],
        ['x^3 - 3x = a', 'two-roots', '{-2} U {2}'],
        ['|x^2 - 4| = a', 4, '(0; 4)'],
        ['(x^2 + 1)/x = a', 'no-roots', '(-2; 2)'],
        ['x e^(-x) = a', 'two-roots', '(0; 1/e)'],
        ['sqrt(4 - x^2) = x + a', 'two-roots', '[2; 2sqrt(2))'],
    ];
    for (const [task, want, ref] of cases) {
        const r = P(task, want);
        assert.equal(r.method, 'graphical', task);
        assert.ok(same(r, ref), `${task}: ${r.text}`);
    }
});
