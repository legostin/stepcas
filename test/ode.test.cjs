// Ordinary differential equations: first order and second-order linear with constant coefficients.
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E;
before(async () => {
    E = await import('../src/index.js');
});
const T = (n) => E.toText(n, { lang: 'en' });
// the answer against a reference function at a few points
const same = (a, b) => [0.3, 0.9, 1.4].every((x) => Math.abs(E.evaluate(a, { x }) - E.evaluate(E.parse(b), { x })) < 1e-9);

test('first order: separable, linear, homogeneous, plain integration', () => {
    const cases = [
        ["y' = 2y; y(0) = 3", '3e^(2x)', 'separable'],
        ["y' = x y; y(0) = 1", 'e^(x^2/2)', 'separable'],
        ["y' = y^2; y(0) = 1", '1/(1 - x)', 'separable'],
        ["x y' = y; y(1) = 2", '2x', 'separable'],
        ["y' = e^(x - y); y(0) = 0", 'x', 'separable'],
        ["y' + y = x; y(0) = 1", 'x - 1 + 2e^(-x)', 'linear'],
        ["y' = (x + y)/x; y(1) = 0", 'x ln(x)', 'linear'],
        ["y' = (x^2 + y^2)/(x y); y(1) = 2", 'x sqrt(2ln(x) + 4)', 'homogeneous'],
        ["y' = 3x^2; y(0) = 1", 'x^3 + 1', 'integrate'],
    ];
    for (const [s, ref, type] of cases) {
        const r = E.solveOde(s);
        assert.equal(r.kind, 'solution', s);
        assert.equal(r.type, type, s);
        assert.ok(same(r.expr, ref), `${s}: ${T(r.expr)}`);
        assert.ok(r.steps.at(-1).final);
    }
    const g = E.solveOde("y' + 2x y = x");
    assert.equal(g.kind, 'general');
    assert.equal(T(g.general), 'C*e^(-x^2) + 1/2');
});

test('second order with constant coefficients: roots, right-hand sides, initial conditions', () => {
    const cases = [
        ["y'' + y = 0; y(0) = 0; y'(0) = 1", 'sin(x)'],
        ["y'' - 3y' + 2y = 0; y(0) = 0; y'(0) = 1", 'e^(2x) - e^x'],
        ["y'' - 2y' + y = 0; y(0) = 1; y'(0) = 2", '(1 + x)e^x'],
        ["y'' + 2y' + 5y = 0; y(0) = 1; y'(0) = 1", 'e^(-x)(cos(2x) + sin(2x))'],
        ["y'' + y = x; y(0) = 0; y'(0) = 0", 'x - sin(x)'],
        ["y'' + 4y = sin(x); y(0) = 0; y'(0) = 0", 'sin(x)/3 - sin(2x)/6'],
    ];
    for (const [s, ref] of cases) {
        const r = E.solveOde(s);
        assert.equal(r.kind, 'solution', s);
        assert.ok(same(r.expr, ref), `${s}: ${T(r.expr)}`);
    }
    const res = E.solveOde("y'' + y = sin(x)");
    assert.equal(res.type, 'undetermined-coefficients');
    assert.equal(T(res.general), 'C_1*cos(x) + C_2*sin(x) - x*cos(x)/2');
    assert.equal(E.solveOde("y'' + y = tan(x)").type, 'variation-of-parameters');
});

test('unsupported and malformed input is refused with a reason', () => {
    assert.equal(E.solveOde('y = x').kind, 'unsupported');
    assert.equal(E.solveOde("y'' = y y'").kind, 'unsupported');
});
