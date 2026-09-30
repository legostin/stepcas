// Greatest/least values on a segment and points of extremum.
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E;
before(async () => { E = await import('../src/index.js'); });
const T = (n) => E.toText(n, { lang: 'en' });

test('greatest and least values on a segment, exact', () => {
    const r = E.extremeOnSegment('x^3 - 3x + 4', 'x', '-2', '0', { kind: 'max' });
    assert.equal(T(r.value), '6');
    assert.equal(T(r.at), '-1');
    assert.equal(T(r.min.value), '2');
    assert.ok(r.steps.length >= 5);
    assert.ok(r.steps.at(-1).final);
    const e = E.extremeOnSegment('e^(2x) - 6e^x + 3', 'x', '1', '2', { kind: 'min' });
    assert.equal(T(e.value), '-6');
    assert.equal(T(e.at), 'ln(3)');
});

test('monotonic: the answer is at an end; a corner counts as a critical point', () => {
    const r = E.extremeOnSegment('7sin(x) - 8x + 9', 'x', '-3pi/2', '0', { kind: 'min' });
    assert.equal(T(r.value), '9');
    const c = E.extremeOnSegment('abs(x - 1) + x^2', 'x', '-1', '2', { kind: 'min' });
    assert.equal(T(c.value), '3/4');
    const k = E.extremeOnSegment('abs(x)', 'x', '-1', '2', { kind: 'min' });
    assert.equal(T(k.value), '0');
});

test('a function undefined on the segment is refused, not guessed', () => {
    assert.equal(E.extremeOnSegment('ln(x)', 'x', '-1', '2').kind, 'unsupported');
    assert.throws(() => E.extremeOnSegment('x^2', 'x', '3', '1'));
});

test('points of maximum and minimum', () => {
    const r = E.extremePoints('x^3 - 48x + 17');
    assert.deepEqual(r.max.map((c) => T(c.x)), ['-4']);
    assert.deepEqual(r.min.map((c) => T(c.x)), ['4']);
    const q = E.extremePoints('(x^2 + 196)/x');
    assert.deepEqual(q.min.map((c) => T(c.x)), ['14']);
    assert.deepEqual(q.max.map((c) => T(c.x)), ['-14']);
    assert.equal(E.extremePoints('x^3').max.length, 0);
});

test('exact guesses for numeric roots', () => {
    assert.equal(T(E.exactGuess(Math.PI / 3)), 'pi/3');
    assert.equal(T(E.exactGuess(Math.sqrt(3) / 2)), 'sqrt(3)/2');
    assert.equal(T(E.exactGuess(Math.log(3))), 'ln(3)');
    assert.equal(E.exactGuess(0.1234567891), null);
});
