// School transformations with steps: factoring, expanding, reducing fractions.
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E;
before(async () => { E = await import('../src/index.js'); });
const T = (n) => E.toText(n, { lang: 'en' });
const titles = (r) => r.steps.map((s) => s.title.en);

test('factoring names its formula and checks itself', () => {
    const cases = [
        ['x^3 - x', 'x*(x + 1)*(x - 1)', 'Take the common factor out'],
        ['x^2 - 5x + 6', '(x - 2)*(x - 3)', 'Factor the quadratic through its roots'],
        ['2x^2 + x - 1', '(x + 1)*(2x - 1)', 'Factor the quadratic through its roots'],
        ['x^4 - 16', '(x + 2)*(x - 2)*(x^2 + 4)', 'The difference of squares'],
        ['x^3 - 8', '(x - 2)*(x^2 + 2x + 4)', 'The difference of cubes'],
        ['x^3 + 27', '(x + 3)*(x^2 - 3x + 9)', 'The sum of cubes'],
        ['4x^2 - 12x + 9', '(2x - 3)^2', 'A perfect square'],
        ['x^3 - 6x^2 + 11x - 6', '(x - 1)*(x - 2)*(x - 3)', 'Find a root and divide'],
    ];
    for (const [s, want, title] of cases) {
        const r = E.factorSteps(s);
        assert.equal(T(r.result), want, s);
        assert.ok(titles(r).includes(title), `${s}: ${titles(r)}`);
        assert.ok(r.steps.at(-1).final);
    }
});

test('expanding by the formulas, then collecting', () => {
    const a = E.expandSteps('(x + 1)^2 - (x - 1)^2');
    assert.equal(T(a.result), '4x');
    assert.match(a.steps[1].text.en, /square of a sum/);
    assert.equal(T(E.expandSteps('(2x - 3)(2x + 3) + 9').result), '4x^2');
    assert.equal(T(E.expandSteps('(x + 2)^3 - x^3').result), '6x^2 + 12x + 8');
});

test('reducing a fraction keeps the excluded values', () => {
    const r = E.simplifySteps('(x^2 - 9)/(x - 3)');
    assert.equal(T(r.result), 'x + 3');
    assert.deepEqual(r.restrictions.map(String), ['3']);
    assert.equal(T(E.simplifySteps('(2x^2 + x - 1)/(4x^2 - 1)').result), '(x + 1)/(2x + 1)');
    assert.equal(T(E.simplifySteps('(3x + 3)/(x^2 - 1)').result), '3/(x - 1)');
});
