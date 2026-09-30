// tests/Js/math-engine-polish2.test.cjs — regressions from the engine polish round 2:
// rational roots without the candidate explosion, the true LCD, numeric roots printed as decimals,
// substitutions keeping their term order, complex coefficients, huge trig values, systems, logs.
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E;
before(async () => {
    E = await import('../src/index.js');
});

const P = (s) => E.Poly.fromNode(E.parse(s));
const rr = (p) => p.rationalRoots().map((r) => `${r.root}^${r.mult}`);
const texOf = (x, l = 'ru') => (typeof x === 'string' ? x : x[l]);

test('rationalRoots/factor: many candidates are located numerically, the roots stay exact', () => {
    const big = P('735134400x^5 - x - 735134400');
    let t = performance.now();
    assert.deepEqual(rr(big), []);
    assert.equal(big.factor().factors.length, 1);
    assert.ok(performance.now() - t < 2000, `too slow: ${performance.now() - t} ms`); // was ~6.7 s
    // the full candidate list is still there for the steps (lazily), and quick to build
    t = performance.now();
    const c = big.rationalRoots().candidates;
    assert.equal(c.length, big.rootCandidates().length);
    assert.ok(c.length > 70000);
    assert.ok(performance.now() - t < 5000);
    // exact roots next to the huge end coefficients, with multiplicities
    const q = E.Poly.fromRoots(['1/7', '2/7', '2/7', '-3/5', 1]).mul(P('735134400x^4 + x - 735134400'));
    assert.deepEqual(rr(q), ['-3/5^1', '1/7^1', '2/7^2', '1^1']);
    const f = q.factor();
    assert.equal(f.factors.map((x) => `${x.poly}^${x.mult}`).join(' | '), 'x - 1^1 | 5x + 3^1 | 7x - 2^2 | 7x - 1^1 | 735134400x^4 + x - 735134400^1');
    // Wilkinson's polynomial: ill-conditioned numerically, still every root
    const W = E.Poly.fromRoots(Array.from({ length: 20 }, (_, i) => i + 1));
    assert.deepEqual(
        W.rationalRoots().map((r) => Number(r.root.n)),
        Array.from({ length: 20 }, (_, i) => i + 1),
    );
    // small cases unchanged
    assert.deepEqual(rr(P('2x^2 - 3x - 2')), ['-1/2^1', '2^1']);
    assert.deepEqual(P('2x^2 - 3x - 2').rationalRoots().candidates.map(String), ['-2', '-1', '-1/2', '1/2', '1', '2']);
    const s = E.solveEquation('735134400x^5 - x - 735134400 = 0');
    assert.equal(s.kind, 'roots');
    assert.equal(s.roots.length, 1);
    assert.ok(Math.abs(s.roots[0].approx - 1) < 1e-8);
});

test('combineFractions builds the least common denominator from factored denominators', () => {
    const cf = (s, o) => E.toTex(E.combineFractions(E.parse(s), o));
    assert.equal(cf('1/x + 1/(x^2-x) - 2', { cancel: false }), '\\frac{-2x^{2} + 3x}{x(x - 1)}');
    assert.equal(cf('1/x + 1/(x^2-x) - 2'), '\\frac{-2x + 3}{x - 1}');
    assert.equal(cf('1/(x-1) + 1/(x^2-1)', { cancel: false }), '\\frac{x + 2}{(x + 1)(x - 1)}');
    assert.equal(cf('1/(x^2-x) + 1/(x^3-x)', { cancel: false }), '\\frac{x + 2}{x(x + 1)(x - 1)}');
    assert.equal(cf('1/(x^2-4) - 1/(x^2+4x+4)', { cancel: false }), '\\frac{4}{(x + 2)^{2}(x - 2)}');
    // a single fraction keeps its denominator; several letters are left as they were
    assert.equal(cf('(x^2 - 4)/(x^2 - 4x + 4)'), '\\frac{x^{2} - 4}{x^{2} - 4x + 4}');
    assert.equal(cf('a/b + c/d'), '\\frac{ad + bc}{bd}');
    assert.ok(E.equivalent(E.combineFractions(E.parse('1/x + 1/(x^2-x) - 2'), { cancel: false }), E.parse('1/x + 1/(x^2-x) - 2')));
});

test('numeric roots print as decimals with ≈ in checks and answers', () => {
    const s = E.solveEquation('x^3 - 2x - 5 = 0');
    assert.equal(texOf(s.answer.tex), 'x \\approx 2{,}0946');
    assert.equal(texOf(s.check[0].tex, 'ru'), '(2{,}0946)^{3} - 2 \\cdot 2{,}0946 - 5 \\approx 0\\ \\checkmark');
    assert.equal(texOf(s.check[0].tex, 'en'), '(2.0946)^{3} - 2 \\cdot 2.0946 - 5 \\approx 0\\ \\checkmark');
    for (const c of s.check) assert.ok(!/\d{8}/.test(texOf(c.tex, 'ru')), texOf(c.tex, 'ru'));
    const e = E.solveEquation('e^x = 3 - x');
    assert.ok(!/\d{8}/.test(texOf(e.check[0].tex, 'ru')));
    assert.equal(E.toTex(e.roots[0].node), '0{,}79206');
    // a double given to checkRoot is an approximation: checked numerically
    assert.equal(E.checkRoot('x^2 = 2', 'x', Math.SQRT2).isRoot, true);
    // complex numeric roots too
    const c = E.solveEquation('x^3 - 2x - 5 = 0', 'x', { domain: 'complex' });
    assert.ok(c.check.every((x) => x.ok && !/\d{8}/.test(texOf(x.tex, 'ru'))));
});

test('a substituted expression keeps the original term order', () => {
    const sub = (s, x) => E.toTex(E.substitute(E.parse(s), { x }));
    assert.equal(sub('-x^2+4x-4', 2), '-2^{2} + 4 \\cdot 2 - 4');
    assert.equal(sub('-2x + 3', 5), '-2 \\cdot 5 + 3');
    assert.equal(E.toTex(E.substitute(E.simplify(E.parse('-x^2+4x-4')), { x: 2 })), '-2^{2} + 4 \\cdot 2 - 4');
    // simplify output of numeric sums is still reordered to start with a positive term
    assert.equal(E.toTex(E.simplify(E.parse('-ln 2 + ln 3'))), '\\ln 3 - \\ln 2');
    assert.equal(E.toTex(E.simplify(E.parse('-1 + sqrt(2)'))), '\\sqrt{2} - 1');
    assert.equal(E.toTex(E.simplify(E.parse('-2 + 3i'))), '-2 + 3i');
});

test('complex domain: complex coefficients and square roots of Gaussian rationals', () => {
    const lin = E.solveEquation('(1+i)z = 3-i', 'z', { domain: 'complex' });
    assert.equal(lin.kind, 'roots');
    assert.equal(texOf(lin.answer.tex), 'z = 1 - 2i');
    assert.ok(lin.check.every((c) => c.ok));
    const sq = E.solveEquation('z^2 = 3+4i', 'z', { domain: 'complex' });
    assert.deepEqual(
        sq.roots.map((r) => E.toTex(r.node)),
        ['-2 - i', '2 + i'],
    );
    const mixed = E.solveEquation('z^2 + (1+i)z + i = 0', 'z', { domain: 'complex' });
    assert.deepEqual(
        mixed.roots.map((r) => E.toTex(r.node)),
        ['-1', '-i'],
    );
    assert.equal(E.solveEquation('(1+i)z = 3-i', 'z').kind, 'none');
    const s = (t) => E.toTex(E.simplify(E.parse(t), { complex: true }));
    assert.equal(s('sqrt(3+4i)'), '2 + i');
    assert.equal(s('sqrt(-2i)'), '1 - i');
    assert.equal(s('sqrt(5-12i)'), '3 - 2i');
    assert.equal(s('sqrt(1+i)'), '\\sqrt{1 + i}');
});

test('trig: huge values, equal functions of different arguments, fractions', () => {
    const big = E.solveTrig('tg x = 10^10');
    assert.equal(big.kind, 'roots');
    assert.ok(/arctg/.test(texOf(big.answer.tex)));
    assert.equal(E.checkRoot('tg x = 10^10', 'x', 'arctg(10^10)').isRoot, true);
    assert.equal(E.checkRoot('tg x = 10^10', 'x', E.parse('arctg(10^10) + pi')).isRoot, true);
    assert.equal(E.checkRoot('tg x = 10^10', 'x', E.parse('pi/2')).isRoot, false);
    assert.equal(texOf(E.solveEquation('tg x = 2 - sqrt(3)').answer.tex), 'x = \\frac{\\pi}{12} + \\pi n,\\ n \\in \\mathbb{Z}');
    const t3 = E.solveEquation('tg 3x = tg x');
    assert.ok(!t3.numeric);
    assert.equal(texOf(t3.answer.tex), 'x = \\pi n,\\ n \\in \\mathbb{Z}');
    const sc = E.solveEquation('sin 3x = cos x');
    assert.ok(!sc.numeric);
    assert.equal(texOf(sc.answer.tex), 'x = \\frac{\\pi}{8} + \\frac{\\pi n}{2};\\quad x = \\frac{\\pi}{4} + \\pi n,\\ n \\in \\mathbb{Z}');
    assert.ok(E.solveEquation('sin 2x = cos x').steps.some((s) => /двойного угла/.test(s.title.ru)));
    const fr = E.solveEquation('sin x/(1-cos x) = 0');
    assert.ok(!fr.numeric);
    assert.equal(texOf(fr.answer.tex), 'x = \\pi + 2\\pi n,\\ n \\in \\mathbb{Z}');
    const h = E.solveEquation('sin(x)^2 - 3sin x cos x + 2cos(x)^2 = 0');
    const hs = h.steps.find((s) => /Однородное/.test(s.title.ru));
    assert.ok(/\$\\cos x = 0\$/.test(hs.text.ru), hs.text.ru);
    for (const r of [t3, sc, fr]) for (const s of r.steps) assert.ok(!/\\quad[a-z]/.test(texOf(s.tex ?? '', 'ru')), texOf(s.tex ?? '', 'ru'));
});

test('exponentials and logarithms: a^(log_a b), common factors, taking logarithms', () => {
    const s = (t) => E.toTex(E.simplify(E.parse(t)));
    assert.equal(s('2^(log_2 3 + log_2 5)'), '15');
    assert.equal(s('10^(lg 2 + lg 5)'), '10');
    assert.equal(s('3^(2log_3 x)'), 'x^{2}');
    assert.equal(s('e^(2 ln x + 1)'), 'ex^{2}');
    const f = E.solveEquation('x^2*2^x = 4*2^x');
    assert.ok(!f.numeric);
    assert.deepEqual(
        f.roots.map((r) => r.approx),
        [-2, 2],
    );
    const g = E.solveEquation('x^(lg x) = 100x');
    assert.ok(!g.numeric);
    assert.deepEqual(
        g.roots.map((r) => E.toTex(r.node)),
        ['\\frac{1}{10}', '100'],
    );
    assert.deepEqual(
        E.solveEquation('x^(log_2 x) = 16').roots.map((r) => E.toTex(r.node)),
        ['\\frac{1}{4}', '4'],
    );
});

test('systems: clean refusal reasons, one unknown gets an answer text', () => {
    const nl = E.solveLinearSystem(['x^2 + y = 1', 'x - y = 0']);
    assert.equal(nl.kind, 'unsupported');
    assert.ok(!/solveSystem2|\(/.test(nl.reason.ru) && !/solveSystem2/.test(nl.reason.en));
    const one = E.solveLinearSystem('2x = 4');
    assert.equal(one.kind, 'unique');
    assert.equal(texOf(one.answer.tex), 'x = 2');
    assert.deepEqual(one.answer.text, { ru: 'x = 2', en: 'x = 2' });
    const two = E.solveLinearSystem(['x + y = 3', 'x - y = 1']);
    assert.deepEqual(two.answer.text, { ru: '(2; 1)', en: '(2, 1)' });
});
