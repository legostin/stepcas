// tests/Js/math-engine-solve.test.cjs — equations, inequalities, systems and sets (solve.js)
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E;
before(async () => {
    E = await import('../src/index.js');
});
// the solvers never throw on what a person types: a refusal is {ok: false} with the error's code and message
const refused = (r, pred) => r.ok === false && pred({ ...r, msg: r.reason });

// ---------------------------------------------------------------- helpers

const TOL = 1e-7;
const near = (a, b, tol = TOL) => Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b));
const PI = Math.PI;

/** Every step: bilingual title, tex string or {ru, en}, bilingual text; balanced braces; recursively. */
function checkSteps(steps, where = '') {
    assert.ok(Array.isArray(steps) && steps.length > 0, `${where}: steps must be a non-empty array`);
    for (const s of steps) {
        // a title, tex or text is a message, a string (the same in every language) or {lang: text}: read it per language
        const [titleRu, titleEn] = [E.pickLang(s.title, 'ru'), E.pickLang(s.title, 'en')];
        assert.ok(titleRu.length && titleEn.length, `${where}: empty title`);
        const texts = [titleRu, titleEn];
        if (s.tex !== undefined) texts.push(E.pickLang(s.tex, 'ru'), E.pickLang(s.tex, 'en'));
        if (s.text !== undefined) {
            const ru = E.pickLang(s.text, 'ru');
            texts.push(ru, E.pickLang(s.text, 'en'));
            assert.ok(/[а-яё]/i.test(ru) || !/[a-z]{4}/i.test(ru.replace(/\$[^$]*\$/g, '')), `${where}: RU text looks English: ${ru}`);
        }
        for (const t of texts) {
            assert.ok(!/undefined|NaN|\[object|Infinity(?!\})/.test(t), `${where}: bad text ${t}`);
            let depth = 0;
            for (const ch of t.replace(/\\[{}]/g, '')) {
                if (ch === '{') depth++;
                if (ch === '}') depth--;
                assert.ok(depth >= 0, `${where}: braces in ${t}`);
            }
            assert.equal(depth, 0, `${where}: unbalanced braces in ${t}`);
            assert.equal((t.match(/\$/g) || []).length % 2, 0, `${where}: unbalanced $ in ${t}`);
        }
        if (s.sub) checkSteps(s.sub, where + ' > ' + titleEn);
    }
}

const val = (x) => (typeof x === 'number' ? x : E.evaluate(typeof x === 'string' ? E.parse(x) : x));

/** Real roots as numbers (ascending). */
const approxRoots = (r) => r.roots.map((x) => x.approx).sort((a, b) => a - b);

function expectRoots(eq, expected, opts = {}) {
    const r = E.solveEquation(eq, opts.v ?? 'x', opts);
    assert.equal(r.kind, 'roots', `${eq}: kind ${r.kind} ${JSON.stringify(r.reason ?? '')}`);
    const got = approxRoots(r);
    const want = expected.map(val).sort((a, b) => a - b);
    assert.equal(got.length, want.length, `${eq}: roots ${got} vs ${want}`);
    got.forEach((g, k) => assert.ok(near(g, want[k]), `${eq}: root ${g} vs ${want[k]}`));
    // every exact root node evaluates to its approximation, and the answer is exact unless we asked otherwise
    for (const x of r.roots) {
        if (!x.approxOnly) assert.ok(near(E.evaluate(x.node), x.approx), `${eq}: node/approx mismatch`);
        if (!opts.approx) assert.ok(!x.approxOnly, `${eq}: root should be exact`);
    }
    if (opts.type) assert.equal(r.type, opts.type, `${eq}: type`);
    if (opts.extraneous) {
        const ex = (r.extraneous ?? []).map((x) => x.approx).sort((a, b) => a - b);
        assert.deepEqual(
            ex.map((x) => Math.round(x * 1e6) / 1e6),
            opts.extraneous
                .map(val)
                .sort((a, b) => a - b)
                .map((x) => Math.round(x * 1e6) / 1e6),
            `${eq}: extraneous`,
        );
    }
    // substitution check: every kept root is checked and fits
    assert.ok(r.check.length >= r.roots.length, `${eq}: every root is checked`);
    checkSteps(r.steps, eq);
    assert.ok(r.steps.at(-1).final, `${eq}: the last step is the answer`);
    return r;
}

function expectKind(eq, kind, opts = {}) {
    const r = E.solveEquation(eq, opts.v ?? 'x', opts);
    assert.equal(r.kind, kind, `${eq}: kind ${r.kind}`);
    checkSteps(r.steps, eq);
    return r;
}

/** Trig: the families solve the equation (n = -4..4) and give exactly the expected roots in [0, W). */
function expectTrig(eq, expected, W = 2 * PI) {
    const r = E.solveEquation(eq);
    assert.equal(r.kind, expected.length ? 'roots' : 'none', `${eq}: kind ${r.kind} ${JSON.stringify(r.reason ?? '')}`);
    checkSteps(r.steps, eq);
    if (!expected.length) return r;
    assert.ok(r.families && r.families.length, `${eq}: families`);
    const node = E.parse(eq);
    const f = E.compile(E.simplify(E.add(node.lhs, E.neg(node.rhs))), ['x']);
    const got = [];
    for (const fam of r.families) {
        const b = E.evaluate(fam.base);
        const p = E.evaluate(fam.period);
        assert.ok(p > 0, `${eq}: period`);
        for (let n = -4; n <= 4; n++) {
            const x = b + p * n;
            const y = f(x);
            assert.ok(Math.abs(y) < 1e-8, `${eq}: f(${x}) = ${y} (family ${E.toText(fam.base)} + ${E.toText(fam.period)}n)`);
        }
        const n0 = Math.ceil((0 - b) / p - 1e-9);
        for (let n = n0; b + p * n < W - 1e-9; n++) got.push(b + p * n);
    }
    const g = [...new Set(got.map((x) => Math.round(x * 1e9) / 1e9))].sort((a, b) => a - b);
    const want = expected.map(val).sort((a, b) => a - b);
    assert.equal(g.length, want.length, `${eq}: roots in [0, W): ${g} vs ${want}`);
    g.forEach((x, k) => assert.ok(near(x, want[k], 1e-8), `${eq}: ${x} vs ${want[k]}`));
    assert.match(E.pickLang(r.answer.tex, 'ru'), /n \\in \\mathbb\{Z\}/);
    return r;
}

function expectSet(ineq, expected, opts = {}) {
    const r = E.solveInequality(ineq, opts.v ?? 'x', opts);
    assert.ok(r.set, `${ineq}: no set (${JSON.stringify(r.reason ?? '')})`);
    const want = E.parseIntervalSet(expected, 'ru');
    assert.ok(r.set.equals(want), `${ineq}: got ${E.intervalText(r.set)} want ${E.intervalText(want)}`);
    checkSteps(r.steps, ineq);
    if (opts.type) assert.equal(r.type, opts.type, `${ineq}: type`);
    return r;
}

const solVal = (s, x) => E.evaluate(s[x]);

// ---------------------------------------------------------------- linear equations

const LINEAR = [
    ['2x+3=7', [2]],
    ['5x - 3 = 2x + 9', [4]],
    ['3(x-1) = 2(x+4)', [11]],
    ['(x+1)/3 = (x-1)/2', [5]],
    ['x/2 + x/3 = 5', [6]],
    ['0.5x + 1.25 = 2', ['3/2']],
    ['7 - 2x = 3', [2]],
    ['4(2x - 1) - 3(x + 2) = 5', [3]],
    ['-x = 5', [-5]],
    ['2x = 0', [0]],
    ['(2x-1)/4 - (x+3)/6 = 1', ['21/4']],
    ['1/2x - 1/3 = 1/6', [1]],
    ['x - 1 = 2 - x', ['3/2']],
    ['10x - 7 = 3x', [1]],
    ['x^2 + 2x = x^2 - 4', [-2]],
    ['(x+1)^2 = x^2 + 5', [2]],
    ['0.2x - 0.1 = 0.3', [2]],
    ['5 = x', [5]],
    ['-3x + 9 = 0', [3]],
    ['sqrt(2) x = 2', ['sqrt(2)']],
    ['pi x = pi', [1]],
    ['3(2 - x) = 4 - (x + 2)', [2]],
];
for (const [eq, roots] of LINEAR) test(`linear: ${eq}`, () => expectRoots(eq, roots));

test('linear: identities and contradictions', () => {
    expectKind('3x + 1 = 3x + 1', 'all');
    expectKind('3x + 1 = 3x + 2', 'none');
    expectKind('x + 2(x+1) = 3(x+1) - 1', 'all');
    expectKind('2(x - 3) + 1 = x - 5 + x', 'all');
    const r = expectKind('x - x = 1', 'none');
    assert.match(r.answer.tex.ru, /корней нет/);
    const a = expectKind('2(x+1) = 2x+2', 'all');
    assert.equal(a.answer.tex, 'x \\in \\mathbb{R}');
});

test('linear: school steps — common denominator, moving terms, dividing', () => {
    const r = E.solveEquation('3(x-1)/4 + x/2 = 1');
    assert.match(r.steps[0].title.ru, /Умножаем обе части на \$4\$/);
    assert.ok(r.steps.some((s) => /Переносим слагаемые/.test(s.title.ru)));
    assert.ok(r.steps.some((s) => /Делим обе части на \$5\$/.test(s.title.ru)));
    assert.equal(r.type, 'linear');
    const z = E.solveEquation('3x + 1 = 3x + 2');
    assert.ok(z.steps.some((s) => /0 \\cdot x/.test(s.title.ru)));
});

test('linear: another variable name is picked up automatically', () => {
    const r = expectRoots('t/4 = 3', [12], { v: 't' });
    assert.equal(r.v, 't');
    const r2 = E.solveEquation('y - 2 = 5');
    assert.equal(r2.v, 'y');
    assert.equal(E.toText(r2.roots[0].node), '7');
});

// ---------------------------------------------------------------- quadratic equations

const QUADRATIC = [
    ['x^2-5x+6=0', [2, 3]],
    ['2x^2+3x-2=0', [-2, '1/2']],
    ['x^2 - 4 = 0', [-2, 2]],
    ['x^2 = 9', [-3, 3]],
    ['x^2 - 3x = 0', [0, 3]],
    ['3x^2 = 12x', [0, 4]],
    ['x^2 - 6x + 9 = 0', [3]],
    ['x^2 - 2x - 1 = 0', ['1 - sqrt(2)', '1 + sqrt(2)']],
    ['x^2 + x - 1 = 0', ['(-1 - sqrt(5))/2', '(-1 + sqrt(5))/2']],
    ['4x^2 - 4x + 1 = 0', ['1/2']],
    ['-x^2 + 5x - 6 = 0', [2, 3]],
    ['(x-1)(x+2) = 4', [-3, 2]],
    ['x(x+1) = 12', [-4, 3]],
    ['0.5x^2 - 2 = 0', [-2, 2]],
    ['x^2/2 - x/3 = 0', [0, '2/3']],
    ['2x^2 - 7x + 3 = 0', ['1/2', 3]],
    ['3x^2 + 2x - 5 = 0', ['-5/3', 1]],
    ['x^2 - 8 = 0', ['-2sqrt(2)', '2sqrt(2)']],
    ['x^2 - 2x - 2 = 0', ['1 - sqrt(3)', '1 + sqrt(3)']],
    ['9x^2 - 6x + 1 = 0', ['1/3']],
    ['x^2 + 4x = 0', [-4, 0]],
    ['(2x-1)^2 = 9', [-1, 2]],
    ['x^2 - 3x - 1 = 0', ['(3 - sqrt(13))/2', '(3 + sqrt(13))/2']],
    ['5x^2 = 0', [0]],
    ['x^2 + 10x + 21 = 0', [-7, -3]],
    ['6x^2 + 5x + 1 = 0', ['-1/2', '-1/3']],
    ['x^2 = 2pi', ['-sqrt(2pi)', 'sqrt(2pi)']],
];
for (const [eq, roots] of QUADRATIC) test(`quadratic: ${eq}`, () => expectRoots(eq, roots));

test('quadratic: no real roots, complex roots as an aside or in the complex domain', () => {
    const r = expectKind('x^2 + 2x + 5 = 0', 'none');
    assert.equal(r.complexRoots.length, 2);
    assert.deepEqual(
        r.complexRoots.map((z) => E.toTex(z.node)),
        ['-1 - 2i', '-1 + 2i'],
    );
    assert.ok(r.steps.some((s) => /D < 0/.test(s.title.ru) && /комплексных/.test(s.text?.ru ?? '')));
    expectKind('2x^2 + 8 = 0', 'none');
    expectKind('x^2 + 1 = 0', 'none');
    const c = E.solveEquation('x^2 + 2x + 5 = 0', 'x', { domain: 'complex' });
    assert.equal(c.kind, 'roots');
    assert.equal(c.roots.length, 2);
    for (const z of c.roots) {
        const w = E.evaluate(z.node, {}, { complex: true });
        const p = w.mul(w).add(w.mul(2)).add(5);
        assert.ok(Math.hypot(p.re, p.im) < 1e-9);
    }
    const i2 = E.solveEquation('x^2 = -4', 'x', { domain: 'complex' });
    assert.deepEqual(
        i2.roots.map((z) => E.toTex(z.node)),
        ['-2i', '2i'],
    );
});

test('quadratic: discriminant step, simplified surds, Vieta check, double root multiplicity', () => {
    const r = E.solveEquation('x^2-5x+6=0');
    assert.ok(r.steps.some((s) => s.tex === 'D = b^2 - 4ac = (-5)^{2} - 4 \\cdot 1 \\cdot 6 = 25 - 24 = 1'));
    assert.ok(r.steps.some((s) => /Виета/.test(s.title.ru)));
    const s = E.solveEquation('x^2 - 3x - 1 = 0');
    assert.equal(E.pickLang(s.answer.tex, 'ru'), 'x_{1} = \\frac{3 - \\sqrt{13}}{2};\\quad x_{2} = \\frac{3 + \\sqrt{13}}{2}');
    const t = E.solveEquation('x^2 - 8 = 0');
    assert.deepEqual(
        t.roots.map((x) => E.toTex(x.node)),
        ['-2\\sqrt{2}', '2\\sqrt{2}'],
    );
    const d = E.solveEquation('x^2 - 6x + 9 = 0');
    assert.equal(d.roots[0].mult, 2);
    const u = E.solveEquation('2x^2 - 12x + 8 = 0'); // D = 80 → (6 ± 2√5)/2 → 3 ± √5
    assert.deepEqual(
        u.roots.map((x) => E.toTex(x.node)),
        ['3 - \\sqrt{5}', '3 + \\sqrt{5}'],
    );
});

test('quadratic: incomplete forms are solved the short way', () => {
    const r = E.solveEquation('x^2 - 3x = 0');
    assert.match(r.steps[0].title.ru, /выносим \$x\$ за скобки/);
    assert.ok(!r.steps.some((s) => /дискриминант/i.test(s.title.ru)));
    const q = E.solveEquation('x^2 = 9');
    assert.ok(q.steps.some((s) => /Извлекаем квадратный корень/.test(s.title.ru)));
});

// ---------------------------------------------------------------- higher degree

const POLY = [
    ['x^3-6x^2+11x-6=0', [1, 2, 3]],
    ['x^3 - x = 0', [-1, 0, 1]],
    ['x^4-5x^2+4=0', [-2, -1, 1, 2]],
    ['x^4 - 13x^2 + 36 = 0', [-3, -2, 2, 3]],
    ['x^4 + x^2 - 2 = 0', [-1, 1]],
    ['x^4 - 3x^2 - 4 = 0', [-2, 2]],
    ['x^3 = 8', [2]],
    ['x^3 = -27', [-3]],
    ['x^4 = 16', [-2, 2]],
    ['x^3 - 2 = 0', ['cbrt(2)']],
    ['x^3-2x^2-4x+8=0', [-2, 2]],
    ['x^3 + x^2 - 4x - 4 = 0', [-2, -1, 2]],
    ['2x^3 - x^2 - 8x + 4 = 0', [-2, '1/2', 2]],
    ['x^3 - 3x + 2 = 0', [-2, 1]],
    ['6x^3 - 11x^2 + 6x - 1 = 0', ['1/3', '1/2', 1]],
    ['2x^4+3x^3-16x^2+3x+2=0', ['-2-sqrt(3)', '-2+sqrt(3)', '1/2', 2]],
    ['x^4 - 2x^3 - x^2 - 2x + 1 = 0', ['(3-sqrt(5))/2', '(3+sqrt(5))/2']],
    ['x^6 - 9x^3 + 8 = 0', [1, 2]],
    ['x^5 - x^3 = 0', [-1, 0, 1]],
    ['(x-1)(x-2)(x-3)(x-4) = 0', [1, 2, 3, 4]],
    ['x^4 - 5x^3 + 5x^2 + 5x - 6 = 0', [-1, 1, 2, 3]],
    ['x^4 - 4 = 0', ['-sqrt(2)', 'sqrt(2)']],
    ['x^3 - 3x^2 + 3x - 1 = 0', [1]],
    ['x^4 + 2x^3 - 3x^2 - 4x + 4 = 0', [-2, 1]],
    ['2x^3 - 3x^2 - 3x + 2 = 0', [-1, '1/2', 2]],
];
for (const [eq, roots] of POLY) test(`polynomial: ${eq}`, () => expectRoots(eq, roots));

test('polynomial: numeric leftovers are marked and explained', () => {
    const r = expectRoots('x^3 + x + 1 = 0', [-0.6823278038280193], { approx: true });
    assert.ok(r.roots[0].approxOnly);
    assert.match(E.pickLang(r.answer.tex, 'ru'), /\\approx -0\{,\}6823/);
    assert.ok(r.steps.some((s) => /Кардано/.test(s.text?.ru ?? '')));
    const q = expectRoots('x^5 - x - 1 = 0', [1.1673039782614187], { approx: true });
    assert.ok(q.steps.some((s) => /Абеля/.test(s.text?.ru ?? '')));
    const c = E.solveEquation('x^5 - x - 1 = 0', 'x', { domain: 'complex' });
    assert.equal(c.roots.length, 5);
    assert.ok(c.check.every((x) => x.ok));
});

test('polynomial: rational root theorem, Horner table and multiplicities', () => {
    const r = E.solveEquation('x^3-6x^2+11x-6=0');
    assert.ok(r.steps.some((s) => /Кандидаты: \$\\pm 1;\\ \\pm 2;\\ \\pm 3;\\ \\pm 6\$/.test(s.text?.ru ?? '')));
    const h = r.steps.find((s) => /Горнера/.test(s.title.ru));
    assert.equal(h.tex, '\\begin{array}{c|cccc} & 1 & -6 & 11 & -6 \\\\ \\hline 1 & 1 & -5 & 6 & 0 \\end{array}');
    const m = E.solveEquation('x^3 - 3x + 2 = 0');
    assert.deepEqual(
        m.roots.map((x) => [x.approx, x.mult]),
        [
            [-2, 1],
            [1, 2],
        ],
    );
    const t = E.solveEquation('x^3 - 3x^2 + 3x - 1 = 0');
    assert.equal(t.roots[0].mult, 3);
    const z = E.solveEquation('x^5 - x^3 = 0');
    assert.equal(z.roots.find((x) => x.approx === 0).mult, 3);
});

test('polynomial: substitution t = x^2, symmetric equations, grouping', () => {
    const b = E.solveEquation('x^4-5x^2+4=0');
    assert.match(b.steps[0].title.ru, /биквадратное/);
    const s = E.solveEquation('2x^4+3x^3-16x^2+3x+2=0');
    assert.match(s.steps[0].title.ru, /Симметричное/);
    const g = E.solveEquation('x^3 + x^2 - 4x - 4 = 0');
    assert.match(g.steps[0].title.ru, /Группируем/);
    const c = E.solveEquation('x^3 = 8', 'x', { domain: 'complex' });
    assert.equal(c.roots.length, 3);
    assert.deepEqual(
        c.roots.map((x) => E.toTex(x.node)),
        ['2', '-1 - i\\sqrt{3}', '-1 + i\\sqrt{3}'],
    );
});

// ---------------------------------------------------------------- rational equations

const RATIONAL = [
    ['1/(x-2)+3/(x^2-4)=0', [-5]],
    ['1/x + 1/(x+1) = 0', ['-1/2']],
    ['(x+3)/(x-1) = 2', [5]],
    ['2/(x+1) = 1', [1]],
    ['x + 1/x = 2', [1]],
    ['x/(x+2) = 3/(x+2)', [3]],
    ['(x^2 - 4)/(x + 2) = 0', [2]],
    ['6/x = x + 1', [-3, 2]],
    ['x/(x-3) - 2/(x+3) = 18/(x^2-9)', [-4]],
    ['3/(x-1) - 4x/(2x-2) = 1/2', ['7/5']],
];
for (const [eq, roots] of RATIONAL) test(`rational: ${eq}`, () => expectRoots(eq, roots));

test('rational: roots that zero a denominator are discarded with an explanation', () => {
    const r = expectKind('x/(x-1)=1/(x-1)', 'none');
    assert.ok(r.odz);
    assert.ok(r.steps.some((s) => /знаменатель равен нулю/.test(s.title.ru)));
    expectKind('(x^2-1)/(x-1) = 2', 'none');
    expectKind('1/x = 0', 'none');
    expectKind('1/(x-1) + 1/(x+1) = 2/(x^2-1)', 'none');
    const a = expectKind('x/x = 1', 'all');
    assert.ok(a.set.equals(E.parseIntervalSet('x != 0')));
    const s = E.solveEquation('x/(x-3) - 2/(x+3) = 18/(x^2-9)');
    assert.match(E.pickLang(s.odz.tex, 'ru'), /\\cup/);
    assert.ok(s.steps.some((st) => /\\frac\{x\^\{2\} \+ x - 12\}\{\(x [-+] 3\)\(x [-+] 3\)\} = 0/.test(E.pickLang(st.tex ?? '', 'ru'))));
});

// ---------------------------------------------------------------- absolute value

const ABS = [
    ['|x-1|=2', [-1, 3]],
    ['|x| = 5', [-5, 5]],
    ['|x+3| = 0', [-3]],
    ['|2x-1|=x+1', [0, 2]],
    ['|x - 2| = 2x - 7', [5]],
    ['|x| = |2x - 3|', [1, 3]],
    ['|x-1| + |x+2| = 5', [-3, 2]],
    ['||x|-1| = 2', [-3, 3]],
    ['|x^2 - 4| = 3x', [1, 4]],
    ['2|x| - 3 = 5', [-4, 4]],
    ['|x^2 - 1| = 3', [-2, 2]],
    ['|x - 3| = |x + 1|', [1]],
];
for (const [eq, roots] of ABS) test(`abs: ${eq}`, () => expectRoots(eq, roots));

test('abs: no roots, and whole intervals of roots', () => {
    const r = expectKind('|2x-1| = -3', 'none');
    assert.ok(r.steps.some((s) => /Модуль не бывает отрицательным/.test(s.title.ru)));
    const s = expectKind('|x-1| + |x+2| = 3', 'set');
    assert.ok(s.set.equals(E.parseIntervalSet('[-2; 1]')));
    const t = expectKind('|x| + x = 0', 'set');
    assert.ok(t.set.equals(E.parseIntervalSet('(-inf; 0]')));
    const u = E.solveEquation('|x - 2| = 2x - 7');
    assert.ok(u.steps.some((st) => /Отбрасываем корни/.test(st.title.ru)));
});

// ---------------------------------------------------------------- radicals

const RADICAL = [
    ['sqrt(x+2)=x', [2], [-1]],
    ['sqrt(x-3) = x - 5', [7], [4]],
    ['sqrt(2x+3) - sqrt(x+1) = 1', [-1, 3]],
    ['cbrt(x+1) = -2', [-9]],
    ['x - 3sqrt(x) + 2 = 0', [1, 4]],
    ['sqrt(x^2 - 9) = 4', [-5, 5]],
    ['sqrt(x) + sqrt(x+1) = 1', [0]],
    ['sqrt(x+5) = sqrt(2x-1)', [6]],
    ['sqrt(3x - 2) = 4', [6]],
    ['sqrt(1 - x) = x + 1', [0], [-3]],
    ['x = sqrt(2 - x)', [1], [-2]],
    ['root(x, 4) = 2', [16]],
    ['x^(3/2) = 8', [4]],
    ['sqrt(x + 7) = x + 1', [2], [-3]],
    ['x^(2/3) = 4', [8], [-8]],
    ['cbrt(x^2) = 4', [-8, 8]],
    ['cbrt(x) = -2', [-8]],
    ['sqrt(x+sqrt(x)) = 2', ['(9 - sqrt(17))/2']],
];
for (const [eq, roots, extr] of RADICAL) test(`radical: ${eq}`, () => expectRoots(eq, roots, extr ? { extraneous: extr } : {}));

test('radical: extraneous roots are explained, ОДЗ is stated', () => {
    const r = E.solveEquation('sqrt(x+2)=x');
    assert.equal(r.type, 'radical');
    assert.equal(E.pickLang(r.odz.tex, 'ru'), 'x + 2 \\ge 0 \\;\\Rightarrow\\; x \\in [-2;\\,+\\infty)');
    assert.ok(r.steps.some((s) => /Возводим обе части в квадрат/.test(s.title.ru) && /посторонние корни/.test(s.text.ru)));
    assert.ok(r.steps.some((s) => /Отбрасываем корни, при которых \$x < 0\$/.test(s.title.ru)));
    const n = expectKind('sqrt(x) = -3', 'none');
    assert.ok(n.steps.some((s) => /не бывает отрицательным/.test(s.title.ru)));
    const c = E.solveEquation('sqrt(x-3) = x - 5');
    assert.equal(
        c.check.find((x) => !x.ok),
        undefined,
    ); // 4 is dropped before the check by the g ≥ 0 condition
    assert.deepEqual(
        c.extraneous.map((x) => [x.approx, x.reason]),
        [[4, 'sign']],
    );
});

// ---------------------------------------------------------------- exponential equations

const EXPONENTIAL = [
    ['2^x=8', [3]],
    ['3^(2x-1) = 27', [2]],
    ['(1/2)^x = 8', [-3]],
    ['2^(x^2-3x) = 1/4', [1, 2]],
    ['4^x = 8', ['3/2']],
    ['2^x = 3', ['log_2(3)']],
    ['5^(x-2) = 1', [2]],
    ['4^x-3*2^x+2=0', [0, 1]],
    ['9^x - 4*3^x + 3 = 0', [0, 1]],
    ['2^x + 2^(x+1) = 12', [2]],
    ['e^(2x) - 3e^x + 2 = 0', [0, 'ln(2)']],
    ['2^x = 3^x', [0]],
    ['3^(x+1) = 9^x', [1]],
    ['25^x - 6*5^x + 5 = 0', [0, 1]],
    ['e^x = 5', ['ln(5)']],
    ['4^x + 2^x - 6 = 0', [1]],
    ['2^(2x+1) - 5*2^x + 2 = 0', [-1, 1]],
    ['3*2^x = 24', [3]],
    ['2^(x+1) = 3^x', ['ln(2)/(ln(3) - ln(2))']],
    ['0.5^x = 0.25', [2]],
    ['2^x * 3^x = 36', [2]],
    ['3^x + 3^(-x) = 10/3', [-1, 1]],
    ['e^(x^2) = e', [-1, 1]],
];
for (const [eq, roots] of EXPONENTIAL) test(`exponential: ${eq}`, () => expectRoots(eq, roots, { type: 'exponential' }));

test('exponential: no roots and the reasoning', () => {
    const r = expectKind('2^x = -4', 'none');
    assert.ok(r.steps.some((s) => /всегда положительна/.test(s.text?.ru ?? '')));
    const t = E.solveEquation('4^x-3*2^x+2=0');
    assert.match(t.steps[0].title.ru, /Замена \$t = 2\^\{x\}\$, где \$t > 0\$/);
    const u = E.solveEquation('4^x + 2^x - 6 = 0');
    assert.ok(u.steps.some((s) => /Отбрасываем \$t \\le 0\$/.test(s.title.ru)));
    const w = E.solveEquation('4^x = 8');
    assert.ok(w.steps.some((s) => /основанию \$2\$/.test(s.title.ru)));
    const l = E.solveEquation('2^x = 3');
    assert.equal(E.toTex(l.roots[0].node), '\\log_{2} 3');
});

// ---------------------------------------------------------------- logarithmic equations

const LOG = [
    ['log_2(x)+log_2(x-2)=3', [4], [-2]],
    ['lg(x)=2', [100]],
    ['ln(x)=1', ['e']],
    ['log_2(x)^2 - 3log_2(x) + 2 = 0', [2, 4]],
    ['lg(x+1) + lg(x-1) = lg(3)', [2], [-2]],
    ['log_3(x^2-4x) = log_3(2x-5)', [5], [1]],
    ['log_2(x+1) - log_2(x-1) = 1', [3]],
    ['ln(x)^2 = 1', ['1/e', 'e']],
    ['log_4(x) + log_2(x) = 3', [4]],
    ['lg(x) = -1', ['1/10']],
    ['log_2(x) = 1/2', ['sqrt(2)']],
    ['log_x(16) = 2', [4], [-4]],
    ['log_x(x+2) = 2', [2], [-1]],
    ['log_3(x - 2) = 2', [11]],
    ['log_2(x^2 - 1) = 3', [-3, 3]],
    ['log_5(x) = log_5(3x - 4)', [2]],
    ['log_2(x) = -1', ['1/2']],
    ['log_(1/2)(x) = 3', ['1/8']],
    ['lg(x)^2 - lg(x) - 2 = 0', ['1/10', 100]],
];
for (const [eq, roots, extr] of LOG)
    test(`logarithmic: ${eq}`, () => expectRoots(eq, roots, extr ? { extraneous: extr, type: 'logarithmic' } : { type: 'logarithmic' }));

test('logarithmic: ОДЗ and the combined logarithm', () => {
    const r = E.solveEquation('log_2(x)+log_2(x-2)=3');
    assert.equal(E.pickLang(r.odz.tex, 'ru'), '\\begin{cases} x > 0 \\\\ x - 2 > 0 \\end{cases} \\;\\Rightarrow\\; x \\in (2;\\,+\\infty)');
    assert.ok(r.odz.set.equals(E.parseIntervalSet('(2; +inf)')));
    assert.ok(r.steps.some((s) => /Собираем логарифмы в один/.test(s.title.ru)));
    const bad = r.check.find((c) => !c.ok);
    assert.equal(bad.reason, 'odz');
    assert.ok(r.steps.some((s) => /Посторонние корни/.test(s.text?.ru ?? '')));
    const e = E.solveEquation('log_3(x^2-4x) = log_3(2x-5)');
    assert.ok(e.steps.some((s) => /равны и их аргументы/.test(s.title.ru)));
});

// ---------------------------------------------------------------- product = 0 and mixed

const MIXED = [
    ['x*(x-1)*(x+2)=0', [-2, 0, 1]],
    ['x*ln(x) = 0', [1]],
    ['(x-3)*sqrt(x+1) = 0', [-1, 3]],
    ['sqrt(x) * (x+2) = 0', [0]],
    ['(x^2 - 1)(2^x - 4) = 0', [-1, 1, 2]],
    ['(x-1)^3 = 0', [1]],
];
for (const [eq, roots] of MIXED) test(`product: ${eq}`, () => expectRoots(eq, roots));

test('product: the lost root and ОДЗ of the other factor', () => {
    const r = E.solveEquation('x*ln(x) = 0');
    assert.equal(r.extraneous.length, 1);
    assert.equal(r.extraneous[0].approx, 0);
    assert.equal(r.extraneous[0].reason, 'odz');
    const p = E.solveEquation('(x-1)^3 = 0');
    assert.equal(p.roots[0].mult, 3);
});

// ---------------------------------------------------------------- numeric fallback and refusals

test('numeric fallback: marked ≈ with the search range', () => {
    const r = expectRoots('2^x = x + 3', [-2.862500371220299, 2.444907554610207], { approx: true });
    assert.equal(r.type, 'numeric');
    assert.deepEqual(r.range, [-10, 10]);
    assert.ok(r.steps.some((s) => /численно/.test(s.title.ru)));
    const c = expectRoots('cos x = x', [0.7390851332151607], { approx: true });
    assert.deepEqual(
        c.range.map((x) => Math.round(x * 1000) / 1000),
        [-6.283, 6.283],
    );
    expectRoots('e^x = 2 - x', [0.4428544010023885], { approx: true });
    expectRoots('x^x = 4', [2], { approx: true });
    const fl = E.solveEquation('floor(x) = 2');
    assert.equal(fl.kind, 'unsupported');
    assert.match(fl.reason.ru, /на целых промежутках/);
    const n = E.solveEquation('x = 2^x');
    assert.equal(n.kind, 'unsupported');
    assert.match(n.reason.ru, /корней не нашлось/);
});

test('refusals are honest', () => {
    const p = E.solveEquation('a x + b = 0');
    assert.equal(p.kind, 'unsupported');
    assert.match(p.reason.ru, /параметрами/);
    assert.equal(E.solveEquation('x^2 < 4').kind, 'unsupported');
    assert.equal(E.solveEquation('x + y = 1; x - y = 2').kind, 'unsupported');
    assert.ok(refused(E.solveEquation('x^2 = = 4'), (e) => e.kind === 'invalid' && e.code === 'syntax'));
    const t = E.solveTrig('x^2 = 4');
    assert.equal(t.kind, 'unsupported');
});

// ---------------------------------------------------------------- trigonometric equations

const TRIG = [
    ['sin x = 1/2', ['pi/6', '5pi/6']],
    ['sin x = 0', [0, 'pi']],
    ['sin x = 1', ['pi/2']],
    ['sin x = -1', ['3pi/2']],
    ['cos x = 1/2', ['pi/3', '5pi/3']],
    ['cos x = 0', ['pi/2', '3pi/2']],
    ['cos x = -1', ['pi']],
    ['cos x = 1', [0]],
    ['cos x = -sqrt(2)/2', ['3pi/4', '5pi/4']],
    ['tg x = 1', ['pi/4', '5pi/4']],
    ['tg x = -sqrt(3)', ['2pi/3', '5pi/3']],
    ['ctg x = 1', ['pi/4', '5pi/4']],
    ['ctg x = 0', ['pi/2', '3pi/2']],
    ['sin(2x) = 0', [0, 'pi/2', 'pi', '3pi/2']],
    ['sin(2x-pi/3)=sqrt(3)/2', ['pi/3', 'pi/2', '4pi/3', '3pi/2']],
    ['3 sin x = 1', ['arcsin(1/3)', 'pi - arcsin(1/3)']],
    ['2sin(x)^2 - sin x - 1 = 0', ['pi/2', '7pi/6', '11pi/6']],
    ['2cos(x)^2 + sin x - 1 = 0', ['pi/2', '7pi/6', '11pi/6']],
    ['sin x = cos x', ['pi/4', '5pi/4']],
    ['sin(x)^2 - 3sin x cos x + 2cos(x)^2 = 0', ['pi/4', '5pi/4', 'arctan(2)', 'arctan(2) + pi']],
    ['sin x cos x = 0', [0, 'pi/2', 'pi', '3pi/2']],
    ['sin 2x = cos x', ['pi/6', 'pi/2', '5pi/6', '3pi/2']],
    ['cos 2x + sin x = 0', ['pi/2', '7pi/6', '11pi/6']],
    ['tg x + 3ctg x = 4', ['pi/4', '5pi/4', 'arctan(3)', 'arctan(3) + pi']],
    ['sqrt(3) sin x + cos x = 1', [0, '2pi/3']],
    ['sin x + cos x = 1', [0, 'pi/2']],
    ['tg(x) cos(x) = 0', [0, 'pi']],
    ['cos(x)^2 - sin(x)^2 = 1/2', ['pi/6', '5pi/6', '7pi/6', '11pi/6']],
    ['sin(x)^2 = 1/4', ['pi/6', '5pi/6', '7pi/6', '11pi/6']],
    ['2cos(x) - 1 = 0', ['pi/3', '5pi/3']],
    ['sin x = sqrt(2)/2', ['pi/4', '3pi/4']],
    ['cos(x - pi/4) = 1', ['pi/4']],
    ['2sin(x)^2 + 3cos x - 3 = 0', [0, 'pi/3', '5pi/3']],
    ['sin(x)^2 + sin x cos x = 1', ['pi/4', 'pi/2', '5pi/4', '3pi/2']],
    ['sin(x)/cos(x) = 1', ['pi/4', '5pi/4']],
    ['sin(3x) + sin(x) = 0', [0, 'pi/2', 'pi', '3pi/2']],
    ['cos(3x) - cos(x) = 0', [0, 'pi/2', 'pi', '3pi/2']],
    ['sin(5x) = sin(3x)', ['pi/8', '3pi/8', '5pi/8', '7pi/8', '9pi/8', '11pi/8', '13pi/8', '15pi/8', 0, 'pi']],
    ['tg x = sin x', [0, 'pi']],
    ['tg(x) = 2 sin(x)', [0, 'pi/3', 'pi', '5pi/3']],
    ['1/sin(x) = 2', ['pi/6', '5pi/6']],
    ['sin(x) + sin(2x) = 0', [0, '2pi/3', 'pi', '4pi/3']],
    ['sin x = sin(pi/6)', ['pi/6', '5pi/6']],
    ['cos(2x) = -1', ['pi/2', '3pi/2']],
    ['tg(2x) = 1', ['pi/8', '5pi/8', '9pi/8', '13pi/8']],
    ['sin(x) cos(x) = 1/4', ['pi/12', '5pi/12', '13pi/12', '17pi/12']],
    ['tg x = 2 - sqrt(3)', ['pi/12', '13pi/12']],
    ['cos(x)^3 = 1/8', ['pi/3', '5pi/3']],
    ['sin(x)^4 + cos(x)^4 = 1/2', ['pi/4', '3pi/4', '5pi/4', '7pi/4']],
    ['x sin x = 0', [0, 'pi']],
];
for (const [eq, roots] of TRIG) test(`trig: ${eq}`, () => expectTrig(eq, roots));

test('trig: cos 3x = 1/3 (arccos, period 2π/3)', () => {
    const a = Math.acos(1 / 3);
    const want = [];
    for (let n = -3; n <= 3; n++)
        for (const s of [1, -1]) {
            const x = (s * a + 2 * PI * n) / 3;
            if (x >= 0 && x < 2 * PI - 1e-9) want.push(x);
        }
    expectTrig('cos(3x) = 1/3', want);
});

test('trig: sin(x/2) = -1 has period 4π', () => {
    expectTrig('sin(x/2) = -1', ['3pi'], 4 * PI);
});

test('trig: no roots when |a| > 1', () => {
    const r = expectTrig('sin x = 2', []);
    assert.ok(r.steps.some((s) => /принимает значения только от/.test(s.text?.ru ?? '')));
    expectTrig('cos x = -3/2', []);
    expectTrig('2sin(x)^2 = 3', []);
});

test('trig: arc values that are rational multiples of π are recognised', () => {
    const r = E.solveEquation('tg x = 2 - sqrt(3)');
    assert.equal(E.pickLang(r.answer.tex, 'ru'), 'x = \\frac{\\pi}{12} + \\pi n,\\ n \\in \\mathbb{Z}');
    assert.ok(r.steps.some((st) => /Здесь \$\\operatorname\{arctg\}/.test(st.text?.ru ?? '')));
    const s = E.solveEquation('sin x = (sqrt(6)-sqrt(2))/4');
    assert.equal(s.answer.tex.ru, 'x = (-1)^{n}\\frac{\\pi}{12} + \\pi n,\\ n \\in \\mathbb{Z}');
});

test('trig: RU and EN general-solution forms', () => {
    const r = E.solveEquation('sin x = 1/2');
    assert.equal(r.answer.tex.ru, 'x = (-1)^{n}\\frac{\\pi}{6} + \\pi n,\\ n \\in \\mathbb{Z}');
    assert.equal(r.answer.tex.en, 'x = \\frac{\\pi}{6} + 2\\pi n,\\quad x = \\frac{5\\pi}{6} + 2\\pi n,\\ n \\in \\mathbb{Z}');
    const n = E.solveEquation('sin x = -1/2');
    assert.equal(n.answer.tex.ru, 'x = (-1)^{n+1}\\frac{\\pi}{6} + \\pi n,\\ n \\in \\mathbb{Z}');
    const c = E.solveEquation('cos x = -sqrt(2)/2');
    assert.equal(E.pickLang(c.answer.tex, 'ru'), 'x = \\pm \\frac{3\\pi}{4} + 2\\pi n,\\ n \\in \\mathbb{Z}');
    const t = E.solveEquation('tg x = 2');
    assert.equal(t.answer.tex.ru, 'x = \\operatorname{arctg} 2 + \\pi n,\\ n \\in \\mathbb{Z}');
    assert.equal(t.answer.tex.en, 'x = \\arctan 2 + \\pi n,\\ n \\in \\mathbb{Z}');
    const s0 = E.solveEquation('sin x = 0');
    assert.equal(E.pickLang(s0.answer.tex, 'ru'), 'x = \\pi n,\\ n \\in \\mathbb{Z}');
    const sh = E.solveEquation('sin(2x-pi/3)=sqrt(3)/2');
    assert.equal(sh.answer.tex.ru, 'x = (-1)^{n}\\frac{\\pi}{6} + \\frac{\\pi}{6} + \\frac{\\pi n}{2},\\ n \\in \\mathbb{Z}');
    const a = E.solveEquation('3 sin x = 1');
    assert.equal(a.answer.tex.ru, 'x = (-1)^{n}\\arcsin\\left(\\frac{1}{3}\\right) + \\pi n,\\ n \\in \\mathbb{Z}');
});

test('trig: roots on an interval (ЕГЭ, part 2)', () => {
    const r = E.solveEquation('sin x = 1/2', 'x', { interval: '[0; 2pi]' });
    assert.deepEqual(
        r.inInterval.map((x) => E.toTex(x.node)),
        ['\\frac{\\pi}{6}', '\\frac{5\\pi}{6}'],
    );
    assert.ok(r.steps.some((s) => /Отбираем корни на промежутке/.test(s.title.ru)));
    const c = E.solveEquation('2cos(x)^2 - 1 = 0', 'x', { interval: [E.parse('-pi'), E.parse('pi')] });
    assert.deepEqual(
        c.inInterval.map((x) => E.toTex(x.node)),
        ['-\\frac{3\\pi}{4}', '-\\frac{\\pi}{4}', '\\frac{\\pi}{4}', '\\frac{3\\pi}{4}'],
    );
    const e = E.solveEquation('2sin(x)^2 + 3cos x - 3 = 0', 'x', { interval: '[pi; 5pi/2]' });
    assert.deepEqual(
        e.inInterval.map((x) => E.toTex(x.node)),
        ['\\frac{5\\pi}{3}', '2\\pi', '\\frac{7\\pi}{3}'],
    );
    const t = E.solveTrig('tg x = -1', 'x', { interval: '(0; 7)' });
    assert.deepEqual(
        t.inInterval.map((x) => E.toTex(x.node)),
        ['\\frac{3\\pi}{4}', '\\frac{7\\pi}{4}'],
    );
    const en = E.solveEquation('cos x = 0', 'x', { interval: '[0, 2pi]', lang: 'en' });
    assert.equal(en.inInterval.length, 2);
});

test('trig: families outside the ОДЗ are dropped, homogeneous and auxiliary-angle steps', () => {
    const r = E.solveEquation('tg(x) cos(x) = 0');
    assert.ok(r.steps.some((s) => /Отбрасываем серии/.test(s.title.ru)));
    const h = E.solveEquation('sin(x)^2 - 3sin x cos x + 2cos(x)^2 = 0');
    assert.ok(h.steps.some((s) => /Однородное уравнение/.test(s.title.ru)));
    const a = E.solveEquation('sqrt(3) sin x + cos x = 1');
    assert.ok(a.steps.some((s) => /вспомогательного угла/.test(s.title.ru)));
    const d = E.solveEquation('sin 2x = cos x');
    assert.ok(d.steps.some((s) => /двойного угла/.test(s.title.ru)));
    const m = E.solveEquation('sin x cos x = 0');
    assert.equal(E.pickLang(m.answer.tex, 'ru'), 'x = \\frac{\\pi n}{2},\\ n \\in \\mathbb{Z}');
});

// ---------------------------------------------------------------- inequalities

const INEQ = [
    ['2x+3 > 7', '(2; +inf)'],
    ['-3x + 1 <= 7', '[-2; +inf)'],
    ['5 - x >= 2x - 4', '(-inf; 3]'],
    ['(x+1)/2 < x/3', '(-inf; -3)'],
    ['2(x - 1) > 2x', '∅'],
    ['2(x-1) < 2x', 'R'],
    ['x^2-5x+6 < 0', '(2; 3)'],
    ['x^2-5x+6 >= 0', '(-inf; 2] U [3; +inf)'],
    ['x^2+1 > 0', 'R'],
    ['x^2+1 < 0', '∅'],
    ['x^2 - 2x + 1 <= 0', '{1}'],
    ['x^2-2x+1 > 0', 'x != 1'],
    ['x^2 - 2x + 1 >= 0', 'R'],
    ['x^2 - 2x + 1 < 0', '∅'],
    ['-x^2 + 4 >= 0', '[-2; 2]'],
    ['x^2 < 2x', '(0; 2)'],
    ['x^2 - 2 > 0', '(-inf; -sqrt(2)) U (sqrt(2); +inf)'],
    ['(x-1)^2(x+2) >= 0', '[-2; +inf)'],
    ['(x-1)^2(x+2) <= 0', '(-inf; -2] U {1}'],
    ['(x-1)^2(x+2) > 0', '(-2; 1) U (1; +inf)'],
    ['(x-1)(x-2)(x-3) > 0', '(1; 2) U (3; +inf)'],
    ['x^3 - x >= 0', '[-1; 0] U [1; +inf)'],
    ['x^3 - 4x^2 + 4x < 0', '(-inf; 0)'],
    ['x^4 - 5x^2 + 4 < 0', '(-2; -1) U (1; 2)'],
    ['(x+1)/(x-2) <= 0', '[-1; 2)'],
    ['(x+1)/(x-2) > 0', '(-inf; -1) U (2; +inf)'],
    ['1/x > 1', '(0; 1)'],
    ['(x^2-1)/(x^2-4) >= 0', '(-inf; -2) U [-1; 1] U (2; +inf)'],
    ['(x-3)/(x+1)^2 >= 0', '[3; +inf)'],
    ['(x-3)/(x+1)^2 < 0', '(-inf; -1) U (-1; 3)'],
    ['x/(x-1) >= 2', '(1; 2]'],
    ['(x-1)/(x-1) >= 0', 'x != 1'],
    ['|x-1| < 2', '(-1; 3)'],
    ['|2x+1| >= 3', '(-inf; -2] U [1; +inf)'],
    ['|x| > -1', 'R'],
    ['|x-3| <= 0', '{3}'],
    ['|x| < 0', '∅'],
    ['|x - 2| > 0', 'x != 2'],
    ['|x-1| + |x+1| <= 4', '[-2; 2]'],
    ['|x - 1| > 2x', '(-inf; 1/3)'],
    ['2^x > 8', '(3; +inf)'],
    ['0.5^x > 4', '(-inf; -2)'],
    ['4^x - 3*2^x + 2 < 0', '(0; 1)'],
    ['3^(x-1) <= 9', '(-inf; 3]'],
    ['2^x > -1', 'R'],
    ['2^x < 0', '∅'],
    ['(1/3)^x >= 1/9', '(-inf; 2]'],
    ['2^x > 3', '(log_2(3); +inf)'],
    ['log_2(x) > 3', '(8; +inf)'],
    ['log_(1/2)(x) >= -2', '(0; 4]'],
    ['lg(x+1) < lg(2x-3)', '(4; +inf)'],
    ['log_3(x-1) <= 2', '(1; 10]'],
    ['ln(x) < 0', '(0; 1)'],
    ['log_2(x^2 - 1) < 3', '(-3; -1) U (1; 3)'],
    ['sqrt(x) > 2', '(4; +inf)'],
    ['sqrt(x-1) < 3', '[1; 10)'],
    ['sqrt(x+2) >= -1', '[-2; +inf)'],
    ['cbrt(x) < 2', '(-inf; 8)'],
    ['x^(1/3) < 2', '[0; 8)'],
    ['(x^2 + 1)(x - 2) < 0', '(-inf; 2)'],
    ['x^2 > 0', 'x != 0'],
    ['(x-1)/(x+1) > 1', '(-inf; -1)'],
    ['1/(x-1) < 1/(x+1)', '(-1; 1)'],
    ['|x^2 - 4| < 3', '(-sqrt(7); -1) U (1; sqrt(7))'],
    ['x^2 - 4|x| + 3 <= 0', '[-3; -1] U [1; 3]'],
    ['-1 < 2x + 1 <= 5', '(-1; 2]'],
    ['0 <= x^2 - 1 < 3', '(-2; -1] U [1; 2)'],
    ['x != 3', 'x != 3'],
];
for (const [ineq, set] of INEQ) test(`inequality: ${ineq}`, () => expectSet(ineq, set));

test('inequality: sign chart for the method of intervals', () => {
    const r = E.solveInequality('(x-1)^2(x+2) >= 0');
    assert.deepEqual(
        r.signChart.points.map((p) => [p.x, p.kind, p.included, p.mult]),
        [
            [-2, 'zero', true, 1],
            [1, 'zero', true, 2],
        ],
    );
    assert.deepEqual(r.signChart.signs, ['-', '+', '+']);
    assert.ok(r.steps.some((s) => /чётной кратности/.test(s.text?.ru ?? '')));
    const q = E.solveInequality('(x+1)/(x-2) <= 0');
    assert.deepEqual(
        q.signChart.points.map((p) => [p.x, p.kind, p.included]),
        [
            [-1, 'zero', true],
            [2, 'pole', false],
        ],
    );
    assert.deepEqual(q.signChart.signs, ['+', '-', '+']);
    assert.ok(q.steps.some((s) => /всегда выколотые/.test(s.title.ru)));
    const s = E.solveInequality('x^2 - 2 > 0');
    assert.deepEqual(
        s.signChart.points.map((p) => p.tex),
        ['-\\sqrt{2}', '\\sqrt{2}'],
    );
    const z = E.solveInequality('x^2 + 1 > 0');
    assert.deepEqual(z.signChart, { points: [], signs: ['+'] });
});

test('inequality: irrational numeric bounds are decimals and flagged', () => {
    const r = E.solveInequality('x^3 + x + 1 > 0');
    assert.ok(r.approx);
    assert.equal(E.pickLang(r.answer.tex, 'ru'), 'x \\in (-0{,}68233;\\,+\\infty)');
    assert.equal(E.pickLang(r.answer.tex, 'en'), 'x \\in (-0.68233,\\ +\\infty)');
    assert.ok(near(r.set.parts[0].lo.x, -0.6823278038280193, 1e-9));
    assert.ok(r.signChart.points[0].approx);
    assert.match(r.steps.at(-1).text.ru, /приближённо/);
});

test('inequality: steps — flipping the sign, parabola, bases below one, ОДЗ', () => {
    const r = E.solveInequality('-3x + 1 <= 7');
    assert.ok(r.steps.some((s) => /знак неравенства меняется/.test(s.title.ru)));
    const q = E.solveInequality('x^2-5x+6 < 0');
    assert.ok(q.steps.some((s) => /Парабола/.test(s.text?.ru ?? '')));
    const e = E.solveInequality('0.5^x > 4');
    assert.ok(e.steps.some((s) => /меньше 1 — функция убывает/.test(s.title.ru)));
    const l = E.solveInequality('log_(1/2)(x) >= -2');
    assert.ok(l.steps.some((s) => /ОДЗ/.test(s.title.ru)));
    assert.equal(E.pickLang(l.answer.tex, 'ru'), 'x \\in (0;\\,4]');
    assert.equal(E.pickLang(l.answer.tex, 'en'), 'x \\in (0,\\ 4]');
    const u = E.solveInequality('sin x > 1/2');
    assert.equal(u.set, null);
    assert.match(u.reason.ru, /пока не решает/);
});

// ---------------------------------------------------------------- IntervalSet and reading answers

test('IntervalSet: operations', () => {
    const { IntervalSet } = E;
    const a = IntervalSet.below(2, true).union(IntervalSet.above(3));
    assert.equal(E.intervalTex(a), '(-\\infty;\\,2] \\cup (3;\\,+\\infty)');
    assert.equal(E.intervalTex(a, 'en'), '(-\\infty,\\ 2] \\cup (3,\\ +\\infty)');
    assert.equal(E.intervalText(a), '(-∞; 2] ∪ (3; +∞)');
    assert.equal(E.intervalText(a, 'en'), '(-∞, 2] ∪ (3, +∞)');
    assert.equal(E.intervalTex(a.complement()), '(2;\\,3]');
    assert.equal(E.intervalTex(a.intersect(IntervalSet.interval(0, 5, true, true))), '[0;\\,2] \\cup (3;\\,5]');
    assert.ok(a.contains(2) && !a.contains(3) && !a.contains(2.5) && a.contains(-100));
    assert.ok(IntervalSet.all().isAll() && IntervalSet.empty().isEmpty());
    assert.equal(E.intervalTex(IntervalSet.empty()), '\\varnothing');
    const pts = IntervalSet.all().minus(IntervalSet.points([1, 2]));
    assert.equal(E.intervalTex(pts), '(-\\infty;\\,1) \\cup (1;\\,2) \\cup (2;\\,+\\infty)');
    assert.ok(IntervalSet.points([1, 2]).isFinite());
    assert.equal(E.intervalTex(IntervalSet.points([1, 2])), '\\{1;\\,2\\}');
    // touching intervals merge, [a; a] is a point
    const m = IntervalSet.interval(0, 1, true, false).union(IntervalSet.interval(1, 2, true, true));
    assert.equal(E.intervalTex(m), '[0;\\,2]');
    assert.equal(E.intervalTex(IntervalSet.interval(0, 1, false, false).union(IntervalSet.interval(1, 2, false, false))), '(0;\\,1) \\cup (1;\\,2)');
    // irrational ends are exact
    const s = IntervalSet.interval(E.parse('-sqrt(2)'), E.parse('sqrt(2)'), true, false);
    assert.equal(E.intervalTex(s), '[-\\sqrt{2};\\,\\sqrt{2})');
    assert.ok(s.contains(1.414) && !s.contains(1.4143));
    assert.deepEqual(a.toJSON(), [
        { lo: '-inf', hi: '2', loClosed: false, hiClosed: true },
        { lo: '3', hi: '+inf', loClosed: false, hiClosed: false },
    ]);
});

const SETS = [
    ['(-∞; 2] ∪ (3; +∞)', 'ru', '(-∞; 2] ∪ (3; +∞)'],
    ['(-inf; 2] U (3; +inf)', 'ru', '(-∞; 2] ∪ (3; +∞)'],
    ['[1; 3)', 'ru', '[1; 3)'],
    ['(1,5; 3]', 'ru', '(3/2; 3]'],
    ['x < 2', 'ru', '(-∞; 2)'],
    ['-1 < x <= 3', 'ru', '(-1; 3]'],
    ['x < 2 или x > 3', 'ru', '(-∞; 2) ∪ (3; +∞)'],
    ['x ≠ 1', 'ru', '(-∞; 1) ∪ (1; +∞)'],
    ['∅', 'ru', '∅'],
    ['нет решений', 'ru', '∅'],
    ['R', 'ru', '(-∞; +∞)'],
    ['{1; 2}', 'ru', '{1; 2}'],
    ['(-∞; -2] ∪ {1}', 'ru', '(-∞; -2] ∪ {1}'],
    ['x >= sqrt(2)', 'ru', '[sqrt(2); +∞)'],
    ['(-\\infty;\\,2] \\cup (3;\\,+\\infty)', 'ru', '(-∞; 2] ∪ (3; +∞)'],
    ['x∈[0;1]', 'ru', '[0; 1]'],
    ['2 > x', 'ru', '(-∞; 2)'],
    ['x ≤ -1; x ≥ 1', 'ru', '(-∞; -1] ∪ [1; +∞)'],
    ['[1, 3)', 'en', '[1, 3)'],
    ['(-inf, 2] U (3, inf)', 'en', '(-∞, 2] ∪ (3, +∞)'],
    ['x < 2, x > 3', 'en', '(-∞, 2) ∪ (3, +∞)'],
    ['{1, 2}', 'en', '{1, 2}'],
    ['x <= -1 or x >= 1', 'en', '(-∞, -1] ∪ [1, +∞)'],
    ['(1.5, 3)', 'en', '(3/2, 3)'],
    ['no solutions', 'en', '∅'],
];
for (const [text, lang, want] of SETS) {
    test(`parseIntervalSet: ${text}`, () => assert.equal(E.intervalText(E.parseIntervalSet(text, lang), lang), want));
}

test('parseIntervalSet: errors and intervalEquals', () => {
    assert.throws(
        () => E.parseIntervalSet('(1; 2; 3)'),
        (e) => e instanceof E.MathError && e.code === 'interval',
    );
    assert.throws(
        () => E.parseIntervalSet('x < y'),
        (e) => e instanceof E.MathError,
    );
    assert.throws(
        () => E.parseIntervalSet(''),
        (e) => e instanceof E.MathError,
    );
    assert.ok(E.intervalEquals('(-∞; 2] ∪ (3; +∞)', 'x <= 2 или x > 3'));
    assert.ok(!E.intervalEquals('[1;3)', '[1;3]'));
    assert.ok(E.intervalEquals('[1, 3)', '1 <= x < 3', 'en'));
    assert.ok(!E.intervalEquals('garbage', '(1; 2)'));
    assert.ok(E.intervalEquals(E.solveInequality('x^2 < 4').set, '(-2; 2)'));
});

// ---------------------------------------------------------------- checkRoot

test('checkRoot: substitution with steps', () => {
    const a = E.checkRoot('sqrt(x+2) = x', 'x', -1);
    assert.equal(a.isRoot, false);
    assert.equal(a.why, 'mismatch');
    assert.equal(a.tex, '\\sqrt{-1 + 2} = 1 \\,\\ne\\, -1');
    checkSteps(a.steps, 'checkRoot');
    const b = E.checkRoot('x^2 = 4', 'x', 2);
    assert.ok(b.isRoot && b.exact);
    assert.equal(b.tex, '2^{2} = 4\\ \\checkmark');
    const c = E.checkRoot('x^2 > 4', 'x', 3);
    assert.ok(c.isRoot);
    const d = E.checkRoot('log_2(x) = 1', 'x', -2);
    assert.equal(d.isRoot, false);
    assert.equal(d.why, 'odz');
    const e = E.checkRoot('x^2 - 2 = 0', 'x', 'sqrt(2)');
    assert.ok(e.isRoot && e.exact);
    const f = E.checkRoot('1/x = 1', 'x', 0);
    assert.equal(f.isRoot, false);
    assert.equal(f.defined, false);
    const g = E.checkRoot('x^2 + 1 = 0', 'x', 'i', { complex: true });
    assert.ok(g.isRoot);
    const h = E.checkRoot('sin(x) = 1/2', 'x', E.parse('pi/6'));
    assert.ok(h.isRoot && h.exact);
});

// ---------------------------------------------------------------- linear systems

function expectSystem(rels, want, opts = {}) {
    const r = E.solveLinearSystem(rels, opts.vars ?? null, opts);
    assert.equal(r.kind, 'unique', `${rels}: ${r.kind}`);
    for (const [k, v] of Object.entries(want)) assert.ok(near(solVal(r.solution, k), val(v)), `${rels}: ${k}`);
    assert.ok(r.check.every((c) => c.ok));
    checkSteps(r.steps, String(rels));
    return r;
}

test('systems 2×2: substitution, addition, Cramer, Gauss give the same answer', () => {
    for (const method of ['substitution', 'addition', 'cramer', 'gauss']) {
        const r = expectSystem(['2x+3y=7', 'x-y=1'], { x: 2, y: 1 }, { method });
        assert.equal(r.method, method);
        assert.equal(r.answer.tex.ru, '\\left(x;\\ y\\right) = \\left(2;\\ 1\\right)');
        assert.equal(r.answer.tex.en, '\\left(x,\\ y\\right) = \\left(2,\\ 1\\right)');
    }
    const s = E.solveLinearSystem(['2x+3y=7', 'x-y=1']);
    assert.equal(s.method, 'substitution');
    assert.match(s.steps[0].title.ru, /Выражаем \$x\$ из второго уравнения/);
    const a = E.solveLinearSystem(['2x+3y=7', '3x-2y=4']);
    assert.equal(a.method, 'addition');
    assert.match(a.steps[0].title.ru, /умножаем на \$3\$/);
});

test('systems: more cases', () => {
    expectSystem(['2x+3y=7', '3x-2y=4'], { x: 2, y: 1 });
    expectSystem(['x/2 + y/3 = 2', 'x - y = -1'], { x: 2, y: 3 });
    expectSystem('x + y = 3; x - y = 1', { x: 2, y: 1 });
    expectSystem(['x+y+z=6', 'x-y+z=2', '2x+y-z=1'], { x: 1, y: 2, z: 3 });
    expectSystem(['x+y+z+w=10', 'x-y=-1', 'y-z=-1', 'z-w=-1'], { x: 1, y: 2, z: 3, w: 4 });
    expectSystem(['2a + b = 5', 'a - b = 1'], { a: 2, b: 1 });
    expectSystem(['x_1 + x_2 = 3', 'x_1 - x_2 = 1'], { x_1: 2, x_2: 1 });
    expectSystem(['3x - y = 1', 'x + 2y = 12'], { x: 2, y: 5 }, { method: 'cramer' });
    expectSystem(['x + 2y - z = 2', '2x - y + z = 3', 'x + y + z = 6'], { x: 1, y: 2, z: 3 }, { method: 'cramer' });
});

test('systems: no solutions and infinitely many', () => {
    const n = E.solveLinearSystem(['x+y=2', 'x+y=3']);
    assert.equal(n.kind, 'none');
    assert.match(n.answer.tex.ru, /решений нет/);
    checkSteps(n.steps, 'none');
    const g = E.solveLinearSystem(['x+2y=3', '2x+4y=7'], null, { method: 'gauss' });
    assert.equal(g.kind, 'none');
    const inf = E.solveLinearSystem(['x+y=2', '2x+2y=4']);
    assert.equal(inf.kind, 'infinite');
    assert.deepEqual(inf.params, ['y']);
    for (const y of [-2, 0, 3.5]) assert.ok(near(E.evaluate(inf.general.x, { y }) + y, 2));
    const i3 = E.solveLinearSystem(['x+y+z=1', 'x+2y+3z=2']);
    assert.equal(i3.kind, 'infinite');
    assert.equal(i3.method, 'gauss');
    for (const t of [-1, 0, 2]) {
        const env = { [i3.params[0]]: t };
        const [x, y, z] = ['x', 'y', 'z'].map((k) => E.evaluate(i3.general[k], env));
        assert.ok(near(x + y + z, 1) && near(x + 2 * y + 3 * z, 2));
    }
    checkSteps(i3.steps, 'infinite');
    assert.ok(i3.steps.some((s) => /\\begin\{gathered\}/.test(E.pickLang(s.tex ?? '', 'ru')) && /\\begin\{cases\}/.test(E.pickLang(s.tex ?? '', 'ru'))));
    const a = E.solveLinearSystem(['3x - 2y = 4', '6x - 4y = 8'], null, { method: 'addition' });
    assert.equal(a.kind, 'infinite');
    const c = E.solveLinearSystem(['x+y=2', '2x+2y=4'], null, { method: 'cramer' });
    assert.equal(c.kind, 'infinite');
    assert.ok(c.steps.some((s) => /Крамера не применимо/.test(s.title.ru)));
    const nl = E.solveLinearSystem(['x^2 + y = 1', 'x - y = 0']);
    assert.equal(nl.kind, 'unsupported');
});

test('solveSystem2: a linear and a quadratic equation by substitution', () => {
    const pairs = (r) => r.solutions.map((s) => [E.evaluate(s.x), E.evaluate(s.y)]);
    const a = E.solveSystem2(['x+y=5', 'xy=6']);
    assert.equal(a.kind, 'solutions');
    assert.deepEqual(pairs(a), [
        [2, 3],
        [3, 2],
    ]);
    checkSteps(a.steps, 'system2');
    assert.equal(a.answer.tex.ru, '\\left(2;\\ 3\\right);\\quad \\left(3;\\ 2\\right)');
    assert.deepEqual(pairs(E.solveSystem2(['y = x + 1', 'x^2 + y^2 = 25'])), [
        [-4, -3],
        [3, 4],
    ]);
    assert.deepEqual(pairs(E.solveSystem2(['x - y = 1', 'x^2 - y^2 = 5'])), [[3, 2]]);
    assert.deepEqual(pairs(E.solveSystem2(['2x - y = 0', 'x^2 + y = 3'])), [
        [-3, -6],
        [1, 2],
    ]);
    const irr = E.solveSystem2(['y = x', 'x^2 + y^2 = 4']);
    assert.deepEqual(
        irr.solutions.map((s) => E.toTex(s.x)),
        ['-\\sqrt{2}', '\\sqrt{2}'],
    );
    assert.equal(E.solveSystem2(['x + y = 1', 'x^2 + y^2 = -1']).kind, 'none');
    assert.equal(E.solveSystem2(['x^2 + y^2 = 1', 'x^2 - y = 0']).kind, 'unsupported');
    const lin = E.solveSystem2(['x + y = 3', 'x - y = 1']);
    assert.deepEqual(pairs(lin), [[2, 1]]);
});

// ---------------------------------------------------------------- shapes and exports

test('exports are unique engine names and results have the documented shape', () => {
    for (const name of [
        'solveEquation',
        'solveTrig',
        'solveInequality',
        'solveLinearSystem',
        'solveSystem2',
        'checkRoot',
        'IntervalSet',
        'intervalTex',
        'intervalText',
        'parseIntervalSet',
        'intervalEquals',
    ]) {
        assert.ok(E[name], name);
    }
    const r = E.solveEquation('x^2 - 1 = 0', 'x', { steps: false });
    assert.deepEqual(r.steps, []);
    assert.ok(['kind', 'roots', 'steps', 'check', 'answer', 'type'].every((k) => k in r));
    for (const x of r.roots) assert.ok('node' in x && typeof x.approx === 'number' && x.mult === 1);
    const i = E.solveInequality('x > 1', 'x', { steps: false });
    assert.deepEqual(i.steps, []);
    assert.ok(i.set instanceof E.IntervalSet);
    const node = E.rel('=', E.parse('x^2'), E.num(4));
    expectRoots(node, [-2, 2]);
    const expr = E.solveEquation('x^2 - 9');
    assert.equal(expr.roots.length, 2);
});

test('trig equations with shifted arguments: the reduction formulas are a step of their own', () => {
    const r = E.solveEquation('sin(x + pi/2) = 1/2');
    assert.equal(r.kind, 'roots');
    const red = r.steps.find((s) => s.rule === 'reduction');
    assert.ok(red, 'a reduction step');
    assert.equal(typeof red.tex === 'string' ? red.tex : red.tex.ru, '\\sin\\left(x + \\frac{\\pi}{2}\\right) = \\cos x');
    assert.equal(r.answer.tex.ru ?? r.answer.tex, 'x = \\pm \\frac{\\pi}{3} + 2\\pi n,\\ n \\in \\mathbb{Z}');
    const two = E.solveEquation('cos(pi/2 - x) + sin(pi - x) = 1');
    const t2 = two.steps.find((s) => s.rule === 'reduction').tex;
    assert.equal(typeof t2 === 'string' ? t2 : t2.ru, '\\cos\\left(\\frac{\\pi}{2} - x\\right) = \\sin x,\\quad \\sin(\\pi - x) = \\sin x');
    assert.ok(!E.solveEquation('sin x = 1/2').steps.some((s) => s.rule === 'reduction'));
});

test('inequalities: log sums, a polynomial in a log, the generalised method of intervals', () => {
    const I = (s) => E.solveInequality(s, 'x', { steps: true });
    const txt = (r) => r.answer.text.en;
    assert.equal(txt(I('log_2(x) + log_2(x - 2) > 3')), '(4, +∞)');
    assert.equal(txt(I('log_3(x) - log_3(x - 1) <= 1')), '[3/2, +∞)');
    const sub = I('lg(x)^2 - lg(x) - 2 <= 0');
    assert.equal(txt(sub), '[1/10, 100]');
    assert.ok(sub.steps.some((s) => /t = \\lg x/.test(s.title.ru)));
    const g = I('(x - 6)^2 < sqrt(7)(x - 6)');
    assert.equal(txt(g), '(6, 6 + sqrt(7))');
    assert.ok(g.steps.some((s) => s.title.en === 'The generalised method of intervals'));
    assert.equal(txt(I('sqrt(x) > x - 2')), '[0, 4)');
    assert.equal(txt(I('(x - 1)sqrt(x + 2) >= 0')), '{-2} ∪ [1, +∞)');
    assert.equal(txt(I('(x^2 - 1)/sqrt(x) >= 0')), '[1, +∞)');
    assert.equal(txt(I('1/ln(x) > 1')), '(1, e)');
});

test('a fraction with a non-polynomial denominator equals zero', () => {
    const r = E.solveEquation('(x^2 - 4)/ln(x) = 0', 'x', { steps: true });
    assert.equal(r.answer.text, '2');
    assert.equal(E.solveEquation('(x^2 - 1)/ln(x) = 0', 'x').kind, 'none');
    assert.equal(E.solveEquation('1/ln(x) = 1', 'x').answer.text, 'e');
});
