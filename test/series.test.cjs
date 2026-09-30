// Sums of series: finite, geometric, arithmetico-geometric, telescoping, classic, divergent, numeric.
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E;
before(async () => { E = await import('../src/index.js'); });
const T = (n) => E.toText(n, { lang: 'en' });
const S = (s) => E.sumSeries(s);

test('exact sums with the method named', () => {
    const cases = [
        ['sum(k, k, 1, 100)', '5050', 'arithmetic'],
        ['sum(k^2, k, 1, 10)', '385', 'power-sums'],
        ['sum(k^3 - k, k, 2, 5)', '210', 'power-sums'],
        ['sum(2^k, k, 0, 9)', '1023', 'geometric'],
        ['sum(1/2^k, k, 0, inf)', '2', 'geometric'],
        ['sum(3^k/5^(k+1), k, 1, inf)', '3/10', 'geometric'],
        ['sum(k/2^k, k, 1, inf)', '2', 'arithmetico-geometric'],
        ['sum(k^2/3^k, k, 1, inf)', '3/2', 'arithmetico-geometric'],
        ['sum(1/(k(k + 1)), k, 1, inf)', '1', 'telescoping'],
        ['sum(1/(k(k+2)), k, 1, inf)', '3/4', 'telescoping'],
        ['sum(1/(4k^2 - 1), k, 1, inf)', '1/2', 'telescoping'],
        ['sum(1/k^2, k, 1, inf)', 'pi^2/6', 'table'],
        ['sum(5/k^2, k, 2, inf)', '5pi^2/6 - 5', 'table'],
        ['sum((-1)^(k + 1)/k, k, 1, inf)', 'ln(2)', 'table'],
        ['sum(1/k!, k, 0, inf)', 'e', 'table'],
    ];
    for (const [s, v, type] of cases) {
        const r = S(s);
        assert.equal(r.kind, 'value', s);
        assert.equal(T(r.value), v, s);
        assert.equal(r.type, type, s);
        assert.ok(r.steps.at(-1).final);
    }
});

test('divergence: the necessary condition, the harmonic series, p ≤ 1', () => {
    assert.equal(S('sum(k/(k+1), k, 1, inf)').type, 'necessary');
    assert.equal(S('sum(1/k, k, 1, inf)').type, 'harmonic');
    assert.equal(S('sum(1/sqrt(k), k, 1, inf)').type, 'p-series');
    assert.equal(S('sum(2^k, k, 0, inf)').kind, 'diverges');
});

test('numeric estimates only with a convergence argument', () => {
    const z3 = S('sum(1/k^3, k, 1, inf)');
    assert.equal(z3.kind, 'approx');
    assert.ok(Math.abs(z3.approx - 1.2020569031595942) < 1e-7);
    const lb = S('sum((-1)^k/sqrt(k), k, 1, inf)');
    assert.equal(lb.kind, 'approx');
    assert.ok(Math.abs(lb.approx + 0.60489864342163) < 1e-6);
    assert.equal(S('sum(cos(k)/k, k, 1, inf)').kind, 'unsupported');
    assert.equal(S('1/k^2').kind, 'unsupported');
});
