// Values of numeric expressions step by step (ЕГЭ task 7, ОГЭ, ЕНТ).
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E;
before(async () => { E = await import('../src/index.js'); });
const T = (n) => E.toText(n, { lang: 'en' });
const titles = (r) => r.steps.map((s) => s.title.en);
const texts = (r) => r.steps.map((s) => `${typeof s.tex === 'string' ? s.tex : s.tex.ru} ${s.text?.ru ?? ''}`).join('\n');

test('logarithms: sums, change of base, the basic identity, logs of powers', () => {
    const a = E.evaluateSteps('log_5(60) - log_5(12)');
    assert.equal(T(a.value), '1');
    assert.ok(titles(a).includes('Logarithms with one base added and subtracted'));
    const b = E.evaluateSteps('log_3(25)/log_3(5)');
    assert.equal(T(b.value), '2');
    assert.ok(titles(b).includes('Change of base'));
    const c = E.evaluateSteps('36^(log_6(5))');
    assert.equal(T(c.value), '25');
    assert.match(texts(c), /36 = 6\^\{2\}/);
    const d = E.evaluateSteps('5^(log_5(7) + 1)');
    assert.equal(T(d.value), '35');
    assert.equal(T(E.evaluateSteps('log_(1/4)(8)').value), '-3/2');
    assert.equal(T(E.evaluateSteps('lg(0.001)').value), '-3');
    assert.equal(T(E.evaluateSteps('log_2(sqrt(8))').value), '3/2');
    assert.equal(T(E.evaluateSteps('log_4(log_3(81))').value), '1');
    assert.equal(T(E.evaluateSteps('e^(ln(5))').value), '5');
});

test('powers and roots', () => {
    const a = E.evaluateSteps('2^(3sqrt(7) - 1) * 8^(1 - sqrt(7))');
    assert.equal(T(a.value), '4');
    assert.ok(titles(a).includes('Bring the powers to one base'));
    const b = E.evaluateSteps('(0.8)^(1/7) * 5^(2/7) * 20^(6/7)');
    assert.equal(T(b.value), '20');
    assert.ok(titles(b).includes('Factor the bases into primes'));
    assert.equal(T(E.evaluateSteps('(3^(5.3) * 5^(4.3))/15^(3.3)').value), '45');
    assert.equal(T(E.evaluateSteps('(9^(1/2) * 9^(1/3))^(6/5)').value), '9');
    assert.equal(T(E.evaluateSteps('27^(2/3) - 16^(3/4)').value), '1');
    assert.equal(T(E.evaluateSteps('sqrt(45) * sqrt(5)').value), '15');
    const c = E.evaluateSteps('(sqrt(13) - sqrt(7))(sqrt(13) + sqrt(7))');
    assert.equal(T(c.value), '6');
    assert.ok(titles(c).includes('The difference of squares'));
    const d = E.evaluateSteps('sqrt(65^2 - 56^2)');
    assert.equal(T(d.value), '33');
    assert.match(texts(d), /\(65 - 56\)\(65 \+ 56\)/);
    const e = E.evaluateSteps('sqrt(3 + 2sqrt(2)) - sqrt(2)');
    assert.equal(T(e.value), '1');
    assert.ok(titles(e).includes('A perfect square under the root'));
    assert.equal(T(E.evaluateSteps('(sqrt(6) + sqrt(3))^2 - 9').value), '6sqrt(2)');
});

test('trigonometry: reduction formulas in degrees and radians, double angle, lowering the power', () => {
    const a = E.evaluateSteps('-18sqrt(2) sin(-135°)');
    assert.equal(T(a.value), '18');
    assert.match(texts(a), /180\^\\circ - 45\^\\circ/);
    const b = E.evaluateSteps('14sin(19pi/12) cos(19pi/12)');
    assert.equal(T(b.value), '-7/2');
    assert.ok(titles(b).includes('The double-angle sine'));
    assert.equal(T(E.evaluateSteps('5sin(98°)/(sin(49°) sin(41°))').value), '10');
    assert.equal(T(E.evaluateSteps('16cos(pi/8)^2 - 8').value), '4sqrt(2)');
    assert.equal(T(E.evaluateSteps('cos(15°)^2 - sin(15°)^2').value), 'sqrt(3)/2');
    assert.equal(T(E.evaluateSteps('5tg(5pi/4)').value), '5');
    assert.equal(T(E.evaluateSteps('cos(300°)').value), '1/2');
});

test('arithmetic goes one layer at a time and the answer step closes', () => {
    const r = E.evaluateSteps('(3 * 10^2)^2 * (2 * 10^(-3))');
    assert.equal(T(r.value), '180');
    const chain = r.steps[0].tex;
    assert.ok((typeof chain === 'string' ? chain : chain.ru).split(' = ').length >= 4);
    assert.ok(r.steps.at(-1).final);
    assert.equal(T(E.evaluateSteps('6!/(2! 4!)').value), '15');
    assert.equal(T(E.evaluateSteps('(3/4 - 1/6)/(7/12)').value), '1');
});

test('an expression with no rule still gets its value', () => {
    const r = E.evaluateSteps('sqrt(2) + sqrt(3)');
    assert.equal(r.steps.length, 1);
    assert.ok(Math.abs(r.approx - (Math.SQRT2 + Math.sqrt(3))) < 1e-12);
});
