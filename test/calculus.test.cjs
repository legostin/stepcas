// calculus — derivatives, integrals, limits and Taylor polynomials. Every answer is checked independently:
// derivatives against central differences of f, antiderivatives by differentiating them numerically, limits against the expected values
// and the numbers near the point, definite integrals against numeric quadrature.
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E;
before(async () => {
    E = await import('../src/index.js');
});
// the solvers never throw on what a person types: a refusal is {ok: false} with the error's code and message
const refused = (r, pred) => r.ok === false && pred({ ...r, msg: r.reason });

// ---------------------------------------------------------------- helpers

/** Every step: bilingual title, tex string or {ru, en} with balanced braces, bilingual text; recursively. */
function checkSteps(steps, where = '') {
    assert.ok(Array.isArray(steps) && steps.length > 0, `${where}: steps must be a non-empty array`);
    for (const s of steps) {
        assert.equal(typeof s.title?.ru, 'string', `${where}: title.ru`);
        assert.equal(typeof s.title?.en, 'string', `${where}: title.en`);
        assert.ok(s.title.ru.length && s.title.en.length, `${where}: empty title`);
        if (s.tex !== undefined) {
            assert.ok(typeof s.tex === 'string' || (typeof s.tex.ru === 'string' && typeof s.tex.en === 'string'), `${where}: tex shape`);
            const texts = typeof s.tex === 'string' ? [s.tex] : [s.tex.ru, s.tex.en];
            for (const t of texts) {
                assert.ok(!/undefined|NaN|\[object|null/.test(t), `${where}: bad tex ${t}`);
                let depth = 0;
                for (const ch of t.replace(/\\[{}]/g, '')) {
                    if (ch === '{') depth++;
                    if (ch === '}') depth--;
                    assert.ok(depth >= 0, `${where}: braces in ${t}`);
                }
                assert.equal(depth, 0, `${where}: unbalanced braces in ${t}`);
                const lr = (t.match(/\\left/g) ?? []).length;
                const rr = (t.match(/\\right/g) ?? []).length;
                assert.equal(lr, rr, `${where}: \\left/\\right mismatch in ${t}`);
            }
        }
        if (s.text !== undefined) {
            assert.equal(typeof s.text.ru, 'string', `${where}: text.ru`);
            assert.equal(typeof s.text.en, 'string', `${where}: text.en`);
            assert.ok(!/undefined|NaN|\[object/.test(s.text.ru + s.text.en), `${where}: bad text ${s.text.ru}`);
            if (s.text.ru) assert.ok(/[а-яё]/i.test(s.text.ru) || !/[a-z]{4}/i.test(s.text.ru), `${where}: RU text looks English: ${s.text.ru}`);
        }
        if (s.sub) checkSteps(s.sub, where + ' > ' + s.title.en);
    }
}

/** Five-point central difference with a Richardson step; NaN where two step sizes disagree (near a pole). */
function numD(F, x) {
    const s = Math.max(1, Math.abs(x));
    const D = (h) => (-F(x + 2 * h) + 8 * F(x + h) - 8 * F(x - h) + F(x - 2 * h)) / (12 * h);
    const a = D(1e-3 * s);
    const b = D(5e-4 * s);
    if (!Number.isFinite(a) || !Number.isFinite(b)) return NaN;
    if (Math.abs(a - b) > 1e-6 * Math.max(1, Math.abs(b))) return NaN;
    return (16 * b - a) / 15;
}

function lcg(seed) {
    let s = seed >>> 0;
    return () => (s = (Math.imul(s, 1664525) + 1013904223) >>> 0) / 4294967296;
}

const tex = (n, lang = 'ru') => E.calcTex(n, lang);
const pick = (t, lang = 'ru') => (typeof t === 'string' ? t : t[lang]);

// ---------------------------------------------------------------- derivatives

const DERIVS = [
    // the table
    '5',
    'x',
    '3x',
    'x^2',
    'x^3',
    'x^10',
    '-x^4',
    '2x^5-3x^2+x-7',
    'x^(1/2)',
    'sqrt(x)',
    'cbrt(x)',
    'root(x,4)',
    'x^(-1)',
    '1/x',
    '1/x^2',
    '1/x^3',
    '2/sqrt(x)',
    'x^(3/2)',
    'x^(-2/3)',
    'x^pi',
    'e^x',
    'exp(x)',
    '2^x',
    '10^x',
    '(1/2)^x',
    'ln(x)',
    'log_2(x)',
    'lg(x)',
    'log_3(x)',
    'sin(x)',
    'cos(x)',
    'tg(x)',
    'ctg(x)',
    'arcsin(x)',
    'arccos(x)',
    'arctg(x)',
    'arcctg(x)',
    'sh(x)',
    'ch(x)',
    'th(x)',
    'cth(x)',
    'arsh(x)',
    'abs(x)',
    'sec(x)',
    'cosec(x)',
    // sums, products, quotients
    'x^2+sin(x)',
    'x*sin(x)',
    'x^2*cos(x)',
    'x*e^x',
    'x^2*e^x',
    'e^x*sin(x)',
    'e^x*cos(x)',
    'x*ln(x)',
    'x^2*ln(x)',
    'sqrt(x)*ln(x)',
    'x*sin(x)*cos(x)',
    'x*e^x*sin(x)',
    'sin(x)/x',
    'x/sin(x)',
    'e^x/x',
    'ln(x)/x',
    'x/ln(x)',
    '(x+1)/(x-1)',
    '(x^2+1)/(x^2-1)',
    'x/(x^2+1)',
    '(1-x)/(1+x)',
    '1/(x^2+1)',
    'sin(x)/(1+cos(x))',
    '(e^x-1)/(e^x+1)',
    'x^2/(1-x)',
    '(2x+3)/(x^2-4)',
    // the chain rule
    'sin(2x)',
    'cos(3x+1)',
    'e^(2x)',
    'e^(-x)',
    'e^(x^2)',
    'e^(-x^2/2)',
    'sin(x^2)',
    'cos(x)^2',
    'sin(x)^3',
    'sqrt(x^2+1)',
    'sqrt(1-x^2)',
    '(x^2+1)^5',
    '(2x-1)^10',
    '1/(x^2+1)^2',
    'ln(x^2+1)',
    'ln(sin(x))',
    'ln(cos(x))',
    'ln(ln(x))',
    'tg(x^2)',
    'arctg(2x)',
    'arcsin(x/2)',
    'arctg(1/x)',
    'arcsin(sqrt(x))',
    'sqrt(x+sqrt(x))',
    'e^(sin(x))',
    'sin(e^x)',
    'cos(ln(x))',
    'ln(x+sqrt(x^2+1))',
    'ln(tg(x/2))',
    '(1+x^2)^(1/3)',
    '2^(x^2)',
    '3^(sin(x))',
    'lg(x^2+1)',
    'log_2(3x+1)',
    'sin(cos(x))',
    'cos(sin(x^2))',
    'e^(e^x)',
    'ln(abs(x))',
    'abs(x^2-1)',
    'sh(2x)',
    'ch(x^2)',
    'arcctg(x^2)',
    'arccos(2x-1)',
    'sqrt(tg(x))',
    'tg(x)^3',
    'ctg(2x)^2',
    '1/sin(x)^2',
    'sin(x)^2*cos(x)^3',
    // logarithmic differentiation
    'x^x',
    'x^sin(x)',
    'sin(x)^x',
    '(1+1/x)^x',
    'x^(1/x)',
    'x^(x^2)',
    'ln(x)^x',
    'x^ln(x)',
    // nasty compositions
    'sin(x)^2+cos(x)^2',
    'e^(-x)*sin(2x)',
    'x^3*e^(-2x)*cos(x)',
    'ln((1+x)/(1-x))',
    'sqrt((1+x)/(1-x))',
    'arctg((1+x)/(1-x))',
    'x*arcsin(x)+sqrt(1-x^2)',
    'x/sqrt(1+x^2)',
    '(x^2-1)^3/(x+2)^2',
    'e^x/(1+e^x)^2',
    'ln(e^x+e^(-x))',
    'sqrt(x^2+x+1)',
    '1/sqrt(4-x^2)',
    'x^2*sqrt(1-x)',
    'cbrt(x^2-1)',
    '(sin(x)+cos(x))/(sin(x)-cos(x))',
    'arcsin(2x*sqrt(1-x^2))',
    'ln(sqrt(x^2+1)-x)',
    'e^(x)*ln(x)*sin(x)',
    'x^2*arctg(x)',
    'sin(x)*sh(x)',
    'th(x)^2',
    'ln(ch(x))',
    'arsh(x^2)',
    '(x+1)^2*(x-2)^3',
    'x*(x+1)*(x+2)*(x+3)',
    '1/(x*(x+1))',
    '(3x^2-2x+1)/x^3',
    'sqrt(x)/(1+sqrt(x))',
    'sin(3x)*cos(5x)',
    'tg(x)-x',
    'ctg(x)+x',
    'e^(2x)*(x^2-x+1)',
    'log_x(2)',
    'x^2*2^x',
    'sin(x)^(1/2)',
    'sqrt(sin(x)^2+1)',
    '1/(1+sqrt(x))^2',
    'x^4-4x^3+6x^2-4x+1',
    'a*x^2+b*x+c',
    'sin(a*x)',
    'e^(k*x)',
    'x/a+a/x',
    'ln(a*x)',
    'sign(x)*x^2',
    'x*abs(x)',
];

test(`derivatives: ${DERIVS.length} functions agree with central differences`, () => {
    assert.ok(DERIVS.length >= 150);
    const rnd = lcg(2026);
    for (const s of DERIVS) {
        const f = E.parse(s);
        const r = E.derivative(f, 'x');
        assert.ok(r.verified, `${s}: not verified`);
        const others = E.freeVars(f).filter((w) => w !== 'x');
        let ok = 0;
        for (let k = 0; k < 80 && ok < 5; k++) {
            const x = (rnd() < 0.5 ? -1 : 1) * (0.1 + 2.9 * rnd());
            const env = { x };
            for (const w of others) env[w] = 1.37;
            const F = (t) => E.evaluate(f, { ...env, x: t });
            const nd = numD(F, x);
            if (!Number.isFinite(nd) || Math.abs(nd) > 1e6) continue;
            const d = E.evaluate(r.result, env);
            assert.ok(Math.abs(d - nd) <= 1e-6 * Math.max(1, Math.abs(nd)), `${s} at x = ${x}: ${d} vs ${nd} (${tex(r.result)})`);
            ok++;
        }
        assert.ok(ok >= 3, `${s}: too few sample points`);
    }
});

const FORMS = [
    ['x^5', '5x^{4}'],
    ['sqrt(x)', '\\frac{1}{2\\sqrt{x}}'],
    ['1/x', '-\\frac{1}{x^{2}}'],
    ['1/x^2', '-\\frac{2}{x^{3}}'],
    ['cbrt(x)', '\\frac{1}{3\\sqrt[3]{x^{2}}}'],
    ['e^x', 'e^{x}'],
    ['2^x', '2^{x}\\ln 2'],
    ['ln(x)', '\\frac{1}{x}'],
    ['log_2(x)', '\\frac{1}{x\\ln 2}'],
    ['sin(x)', '\\cos x'],
    ['cos(x)', '-\\sin x'],
    ['tg(x)', '\\frac{1}{\\cos^{2} x}'],
    ['ctg(x)', '-\\frac{1}{\\sin^{2} x}'],
    ['arcsin(x)', '\\frac{1}{\\sqrt{1 - x^{2}}}'],
    ['arccos(x)', '-\\frac{1}{\\sqrt{1 - x^{2}}}'],
    ['arctg(x)', '\\frac{1}{x^{2} + 1}'],
    ['sh(x)', '\\operatorname{ch} x'],
    ['x^2*sin(x)', 'x^{2}\\cos x + 2x\\sin x'],
    ['x*e^x', 'e^{x}(x + 1)'],
    ['e^x*sin(x)', 'e^{x}(\\sin x + \\cos x)'],
    ['x*ln(x)', '\\ln x + 1'],
    ['sin(x)/x', '\\frac{x\\cos x - \\sin x}{x^{2}}'],
    ['ln(x)/x', '\\frac{1 - \\ln x}{x^{2}}'],
    ['e^x/x', '\\frac{e^{x}(x - 1)}{x^{2}}'],
    ['(x+1)/(x-1)', '-\\frac{2}{(x - 1)^{2}}'],
    ['x/(x^2+1)', '\\frac{1 - x^{2}}{(x^{2} + 1)^{2}}'],
    ['(x^2-1)/(x^2+1)', '\\frac{4x}{(x^{2} + 1)^{2}}'],
    ['sin(2x)', '2\\cos(2x)'],
    ['e^(x^2)', '2xe^{x^{2}}'],
    ['sqrt(x^2+1)', '\\frac{x}{\\sqrt{x^{2} + 1}}'],
    ['sqrt(1-x^2)', '-\\frac{x}{\\sqrt{1 - x^{2}}}'],
    ['(x^2+1)^5', '10x(x^{2} + 1)^{4}'],
    ['ln(sin(x))', '\\operatorname{ctg} x'],
    ['ln(cos(x))', '-\\operatorname{tg} x'],
    ['sin(x)^2', '2\\sin x\\cos x'],
    ['arctg(x^2)', '\\frac{2x}{x^{4} + 1}'],
    ['x^x', 'x^{x}(\\ln x + 1)'],
    ['ln(x+sqrt(x^2+1))', '\\frac{1}{\\sqrt{x^{2} + 1}}'],
    ['arctg((1+x)/(1-x))', '\\frac{1}{x^{2} + 1}'],
    ['x*sqrt(1-x^2)+arcsin(x)', '2\\sqrt{1 - x^{2}}'],
    ['x^2*e^(-x)', 'xe^{-x}(2 - x)'],
    ['3x^4-2x^3+x-5', '12x^{3} - 6x^{2} + 1'],
    ['(2x-1)^10', '20(2x - 1)^{9}'],
    ['x/sqrt(x^2+1)', '\\frac{1}{\\sqrt{(x^{2} + 1)^{3}}}'],
];

test(`derivatives: clean forms of ${FORMS.length} classic cases`, () => {
    for (const [s, want] of FORMS) {
        assert.equal(tex(E.derivative(s).result), want, s);
        assert.equal(tex(E.derivative(s, 'x', { steps: true }).result), want, `${s} (with steps)`);
    }
    assert.equal(pick(E.derivative('lg(x)').tex, 'en'), "f'(x) = \\frac{1}{x\\ln 10}");
    assert.equal(pick(E.derivative('tg(x)').tex, 'ru'), "f'(x) = \\frac{1}{\\cos^{2} x}");
    assert.equal(pick(E.derivative('tg(x^2)').tex, 'en'), "f'(x) = \\frac{2x}{\\cos^{2}(x^{2})}");
});

test('derivative steps: a tree that mirrors the expression', () => {
    const r = E.derivative('x^2*sin(3x+1)/(x+1)', 'x', { steps: true });
    checkSteps(r.steps, 'quotient');
    const [start, root, answer] = r.steps;
    assert.equal(start.rule, 'start');
    assert.equal(root.rule, 'quotient');
    assert.equal(answer.rule, 'answer');
    assert.ok(answer.final);
    const rules = [];
    const walk = (s) => {
        rules.push(s.rule);
        (s.sub ?? []).forEach(walk);
    };
    walk(root);
    assert.deepEqual([...new Set(rules)].sort(), ['chain', 'const-factor', 'power', 'product', 'quotient', 'sum'].sort());
    const chain = root.sub[0].sub.find((s) => s.rule === 'chain');
    assert.match(chain.text.ru, /Внешняя функция — синус, внутренняя — u = 3x \+ 1/);
    assert.match(chain.tex, /^\(\\sin\(3x \+ 1\)\)' = \\cos\(3x \+ 1\) \\cdot \(3x \+ 1\)' = /);
    assert.match(root.tex, /\\left\(x\^\{2\}\\sin\(3x \+ 1\)\\right\)' \\cdot \(x \+ 1\) - x\^\{2\}\\sin\(3x \+ 1\) \\cdot \(x \+ 1\)'/);
    // a product: u'v + uv'
    const p = E.derivative('x^2*e^x', 'x', { steps: true }).steps[1];
    assert.equal(p.rule, 'product');
    assert.match(p.text.ru, /По правилу произведения/);
    assert.equal(
        p.tex,
        "\\left(x^{2}e^{x}\\right)' = \\left(x^{2}\\right)' \\cdot e^{x} + x^{2} \\cdot \\left(e^{x}\\right)' = 2x \\cdot e^{x} + x^{2} \\cdot e^{x} = xe^{x}(x + 2)",
    );
    // logarithmic differentiation, rewriting as a power, partial derivatives, EN/RU notation
    const ld = E.derivative('x^x', 'x', { steps: true });
    checkSteps(ld.steps, 'x^x');
    assert.equal(ld.steps[1].rule, 'log-diff');
    const rp = E.derivative('3/x^2', 'x', { steps: true });
    assert.equal(rp.steps[1].rule, 'rewrite-power');
    assert.match(rp.steps[1].tex, /\\left\(3x\^\{-2\}\\right\)'/);
    const tg = E.derivative('tg(x^2)', 'x', { steps: true });
    assert.match(tg.steps[1].tex.ru, /\\operatorname\{tg\}/);
    assert.match(tg.steps[1].tex.en, /\\tan/);
    assert.match(tg.steps[1].text.en, /The outer function is the tangent/);
    const ab = E.derivative('abs(x^2-1)', 'x', { steps: true });
    assert.match(ab.steps[1].text.ru, /u ≠ 0/);
    const pd = E.derivative('a*x^2+b*x+c', 'x', { steps: true });
    assert.match(pd.steps[0].text.ru, /Остальные буквы \(a, b, c\) считаем постоянными/);
    for (const s of DERIVS) checkSteps(E.derivative(s, 'x', { steps: true }).steps, s);
});

test('derivative options: unsimplified result, partial, n-th, gradient, tangent', () => {
    const raw = E.derivative('x^2*sin(x)', 'x', { simplify: false }).result;
    assert.ok(E.equivalent(raw, E.parse('2x*sin(x) + x^2*cos(x)')));
    const p = E.partialDerivative('x^2*y + sin(x*y)', 'y');
    assert.equal(p.tex, '\\frac{\\partial f}{\\partial y} = x^{2} + x\\cos(xy)');
    const d3 = E.derivativeN('x^5', 'x', 3);
    assert.equal(tex(d3.result), '60x^{2}');
    assert.deepEqual(
        d3.list.map((n) => tex(n)),
        ['5x^{4}', '20x^{3}', '60x^{2}'],
    );
    assert.equal(d3.tex, "f'''(x) = 60x^{2}");
    const d4 = E.derivativeN('sin(x)', 'x', 4, { steps: true });
    assert.equal(tex(d4.result), '\\sin x');
    assert.equal(d4.tex, 'f^{(4)}(x) = \\sin x');
    checkSteps(d4.steps, 'd4');
    assert.equal(tex(E.derivativeN('x^2', 'x', 5).result), '0');
    assert.ok(E.equivalent(E.derivativeN('e^(2x)*x', 'x', 2).result, E.parse('4e^(2x)*(x+1)')));
    const g = E.gradientOf('x^2*y + y^3', ['x', 'y'], { steps: true });
    assert.equal(tex(g.components.x), '2xy');
    assert.equal(tex(g.components.y), 'x^{2} + 3y^{2}');
    assert.equal(
        g.tex.ru,
        '\\nabla f = \\left(\\frac{\\partial f}{\\partial x};\\ \\frac{\\partial f}{\\partial y}\\right) = \\left(2xy;\\ x^{2} + 3y^{2}\\right)',
    );
    checkSteps(g.steps, 'grad');
    const t = E.tangentLine('x^2', 'x', 1, { steps: true });
    assert.equal(tex(t.k), '2');
    assert.equal(tex(t.b), '-1');
    assert.equal(t.tex, 'y = 2x - 1');
    checkSteps(t.steps, 'tangent');
    assert.equal(E.tangentLine('sin(x)', 'x', 'pi').tex, 'y = \\pi - x');
    assert.equal(E.tangentLine('ln(x)', 'x', 'e').tex, 'y = \\frac{x}{e}');
    assert.equal(E.tangentLine('e^x', 'x', 0).tex, 'y = x + 1');
    assert.ok(refused(E.tangentLine('sqrt(x)', 'x', 0), (e) => e.code === 'no-derivative'));
    assert.ok(refused(E.tangentLine('ln(x)', 'x', -1), (e) => e.code === 'undefined'));
});

test('derivative: refusals and helpers', () => {
    assert.ok(refused(E.derivative('x^2 = 1'), (e) => e.code === 'not-expr'));
    assert.ok(refused(E.derivative('x!'), (e) => e.code === 'unsupported' && /Факториал/.test(e.msg.ru)));
    assert.equal(tex(E.derivative('sign(x)').result), '0');
    assert.equal(tex(E.derivative('floor(2x)').result), '0');
    assert.equal(tex(E.quickDerivative(E.parse('x^3'))), '3x^{2}');
    // display helpers
    assert.equal(tex(E.parse('ln(abs(x))')), '\\ln\\left|x\\right|');
    assert.equal(tex(E.simplify(E.parse('1 - x^2'))), '1 - x^{2}');
    assert.equal(tex(E.simplify(E.parse('x^(2/3)'))), '\\sqrt[3]{x^{2}}');
    assert.equal(tex(E.simplify(E.parse('(x^2+1)^(-3/2)'))), '\\frac{1}{\\sqrt{(x^{2} + 1)^{3}}}');
    const r = E.ratFunctionOf(E.parse('(x^2-1)/(x^2-2x+1)'), 'x');
    assert.equal(r.num.toString(), 'x + 1');
    assert.equal(r.den.toString(), 'x - 1');
    assert.equal(E.ratFunctionOf(E.parse('sin(x)/x'), 'x'), null);
    assert.equal(tex(E.niceForm(E.parse('1/2*ln(2) + 1/2*ln(3) - 1/2*ln(4)'))), '\\frac{1}{2}\\ln\\left(\\frac{3}{2}\\right)');
});

// ---------------------------------------------------------------- integrals

const INTEGRALS = [
    // table and linearity
    '7',
    'x',
    'x^2',
    'x^5',
    'x^(-3)',
    'sqrt(x)',
    'cbrt(x)',
    '1/sqrt(x)',
    'x^(2/3)',
    'x^pi',
    '1/x',
    'e^x',
    '3^x',
    '(1/2)^x',
    'sin(x)',
    'cos(x)',
    'tg(x)',
    'ctg(x)',
    '1/cos(x)^2',
    '1/sin(x)^2',
    '1/(1+x^2)',
    '1/sqrt(1-x^2)',
    'sh(x)',
    'ch(x)',
    'th(x)',
    '1/ch(x)^2',
    'abs(x)',
    '1/cos(x)',
    '1/sin(x)',
    '1/sqrt(x^2+1)',
    '1/sqrt(x^2-1)',
    '3x^2-2x+1',
    'x^4-3x^3+x',
    '2sqrt(x)-3/x',
    '5e^x+2cos(x)',
    '(x^2+1)/x',
    '(1+x)^2/x',
    '(x+1)/sqrt(x)',
    'x*(x-1)*(x+2)',
    '(2x-1)^2',
    '(x^2+1)^3',
    '(1+sqrt(x))^2',
    '(e^x+1)^2',
    'a*x^2+b',
    'x/a',
    // linear substitution
    'sin(3x)',
    'cos(2x+1)',
    'e^(5x)',
    'e^(-x)',
    'e^(1-2x)',
    '(3x+2)^4',
    '1/(2x+1)',
    '1/(1-x)',
    'sqrt(4x+1)',
    '1/sqrt(1-2x)',
    '1/cos(3x)^2',
    '1/(1+(2x)^2)',
    '2^(3x)',
    'sin(x/2)',
    'cos(pi*x)',
    '1/(3x-1)^2',
    'ch(2x)',
    // u-substitution
    'x*e^(x^2)',
    'x^2*e^(x^3)',
    'x*sin(x^2)',
    'x/(x^2+1)',
    'x/(x^2+1)^2',
    'x/sqrt(x^2+1)',
    'x*sqrt(1-x^2)',
    'x^2/(x^3+1)',
    'sin(x)*cos(x)',
    'sin(x)^4*cos(x)',
    'cos(x)^3*sin(x)',
    'ln(x)/x',
    'ln(x)^2/x',
    '1/(x*ln(x))',
    '1/(x*ln(x)^2)',
    'e^x/(1+e^x)',
    'e^x/(1+e^(2x))',
    'e^x*sin(e^x)',
    'cos(x)/(1+sin(x))',
    'sin(x)/cos(x)^3',
    'tg(x)/cos(x)^2',
    'arctg(x)/(1+x^2)',
    'arcsin(x)/sqrt(1-x^2)',
    'e^(sqrt(x))/sqrt(x)',
    'sin(sqrt(x))/sqrt(x)',
    'cos(ln(x))/x',
    'x^3*sqrt(x^2+1)',
    '(2x+3)/(x^2+3x+5)',
    'e^(tg(x))/cos(x)^2',
    '1/(1+e^x)',
    'x*(x^2+1)^5',
    'e^x*(e^x+1)^3',
    'sh(x)*ch(x)',
    // by parts
    'x*e^x',
    'x*e^(-x)',
    'x^2*e^x',
    'x^3*e^x',
    'x*e^(2x)',
    'x*sin(x)',
    'x*cos(x)',
    'x^2*sin(x)',
    'x^2*cos(3x)',
    'x*sin(2x+1)',
    'ln(x)',
    'x*ln(x)',
    'x^2*ln(x)',
    'sqrt(x)*ln(x)',
    'ln(x)/x^2',
    'ln(x)^2',
    'ln(x+1)',
    'ln(x^2+1)',
    'arctg(x)',
    'x*arctg(x)',
    'arcsin(x)',
    'arccos(x)',
    'x/cos(x)^2',
    'x*2^x',
    'x*sh(x)',
    '(x+1)*e^x',
    'lg(x)',
    'log_2(x)',
    // cyclic
    'e^x*sin(x)',
    'e^x*cos(x)',
    'e^(2x)*sin(3x)',
    'e^(-x)*cos(2x)',
    '2^x*sin(x)',
    // rational functions
    '1/(x^2-1)',
    '1/(x^2-4)',
    '1/(x*(x+1))',
    '(x+1)/(x^2-5x+6)',
    '(2x+1)/(x^2+x-2)',
    '1/(x^2+2x+5)',
    '1/(x^2+4)',
    '1/(4x^2+9)',
    '(x+3)/(x^2+2x+2)',
    'x^2/(x^2+1)',
    'x^3/(x^2+1)',
    '(x^3+1)/(x^2-1)',
    '1/(x*(x+1)^2)',
    '1/(x^2*(x-1))',
    '1/(x^3+1)',
    '1/(x^3-1)',
    '1/(x^4-1)',
    'x/(x^4-1)',
    '1/(x^2+1)^2',
    'x/(x^2+1)^3',
    '(x^2+2)/(x*(x^2+1))',
    '1/(x^2-2)',
    '(3x-1)/(x^2-x-6)',
    '1/((x-1)^2*(x+1))',
    '(x^4+1)/(x^3+x)',
    '1/(x^2+x+1)',
    '1/(2x^2-3x+1)',
    // trigonometric
    'sin(x)^2',
    'cos(x)^2',
    'sin(2x)^2',
    'sin(x)^3',
    'cos(x)^3',
    'sin(x)^5',
    'cos(x)^4',
    'sin(x)^2*cos(x)^2',
    'sin(x)^3*cos(x)^2',
    'sin(x)^2*cos(x)^3',
    'tg(x)^2',
    'ctg(x)^2',
    'tg(x)^3',
    'tg(x)^4',
    '1/cos(x)^4',
    '1/sin(x)^3',
    'sin(x)^4/cos(x)^2',
    'cos(x)^3/sin(x)^2',
    'sin(2x)*cos(3x)',
    'sin(x)*sin(3x)',
    'cos(x)*cos(2x)',
    '1/(sin(x)^2*cos(x)^2)',
    'sin(x)*cos(x)^2',
    'sin(3x)^3',
    // roots
    '1/sqrt(4-x^2)',
    '1/sqrt(9-x^2)',
    '1/sqrt(x^2+9)',
    '1/sqrt(x^2-4)',
    'sqrt(1-x^2)',
    'sqrt(4-x^2)',
    'sqrt(x^2+1)',
    'sqrt(x^2-1)',
    '1/sqrt(x^2+2x+5)',
    '1/sqrt(3-2x-x^2)',
    '(x+2)/sqrt(x^2+1)',
    '(2x+1)/sqrt(1-x^2)',
    'x*sqrt(x^2+4)',
    'sqrt(2x-x^2)',
    '1/(1+sqrt(x))',
    'x*sqrt(x+1)',
    'sqrt(x)/(1+x)',
    '1/(sqrt(x)+cbrt(x))',
    'x/sqrt(x+1)',
    '1/(x*sqrt(x+1))',
    'sqrt(x+1)/x',
    // the universal substitution
    '1/(2+cos(x))',
    '1/(1+sin(x))',
    '1/(3+5*cos(x))',
    '1/(1+sin(x)+cos(x))',
    '1/(5-3*cos(x))',
    // polynomial over a root (undetermined coefficients), trigonometric substitutions, high degrees by parts
    'x^2*sqrt(4-x^2)',
    'x^2/sqrt(1-x^2)',
    'x^2/sqrt(x^2+1)',
    'x^3/sqrt(x^2+2x+5)',
    'x^2*sqrt(x^2+1)',
    '1/(x^2*sqrt(1-x^2))',
    'sqrt(1-x^2)/x^2',
    '1/(x^2+1)^(3/2)',
    'x*arcsin(x)',
    'x^8*e^x',
    'x^5*sin(x)',
    'x^4*cos(2x)',
    'x^3*2^x',
];

test(`integrals: ${INTEGRALS.length} antiderivatives, each differentiated back numerically`, () => {
    assert.ok(INTEGRALS.length >= 150);
    const rnd = lcg(77);
    const methods = new Set();
    for (const s of INTEGRALS) {
        const f = E.parse(s);
        const r = E.integrate(f, 'x');
        assert.ok(r.result, `${s}: no antiderivative (${r.reason?.en})`);
        assert.ok(r.verified, `${s}: not verified`);
        methods.add(r.method);
        const others = E.freeVars(f).filter((w) => w !== 'x');
        let ok = 0;
        for (let k = 0; k < 120 && ok < 5; k++) {
            const x = (rnd() < 0.5 ? -1 : 1) * (0.05 + 3.95 * rnd());
            const env = { x };
            for (const w of others) env[w] = 1.37;
            const fv = E.evaluate(f, env);
            if (!Number.isFinite(fv) || Math.abs(fv) > 1e6) continue;
            const nd = numD((t) => E.evaluate(r.result, { ...env, x: t }), x);
            if (!Number.isFinite(nd)) continue;
            assert.ok(Math.abs(nd - fv) <= 1e-6 * Math.max(1, Math.abs(fv)), `${s} at x = ${x}: F' = ${nd}, f = ${fv} (F = ${tex(r.result)})`);
            ok++;
        }
        assert.ok(ok >= 3, `${s}: too few sample points`);
        assert.ok(typeof r.tex === 'string' ? r.tex.endsWith(' + C') : r.tex.ru.endsWith(' + C'), `${s}: + C`);
    }
    for (const m of [
        'table',
        'linearity',
        'linear-substitution',
        'substitution',
        'parts',
        'parts-cyclic',
        'rational',
        'trig-power',
        'trig-substitution',
        'trig-product',
        'quadratic-root',
        'radical-polynomial',
        'trig-root-substitution',
        'rationalizing',
        'universal-substitution',
        'constant',
    ]) {
        assert.ok(methods.has(m), `method ${m} is never used`);
    }
});

test('integrals: high degrees are checked exactly (floating point cannot compare them)', () => {
    const f = E.parse('x^20*e^x');
    const r = E.integrate(f, 'x');
    assert.ok(r.verified);
    const d = E.expand(E.add(E.quickDerivative(r.result, 'x'), E.neg(f)));
    assert.equal(tex(d), '0');
});

const INT_FORMS = [
    ['x^2', '\\frac{x^{3}}{3}', 'table'],
    ['1/x', '\\ln\\left|x\\right|', 'table'],
    ['tg(x)', '-\\ln\\left|\\cos x\\right|', 'table'],
    ['1/cos(x)^2', '\\operatorname{tg} x', 'table'],
    ['1/(1+x^2)', '\\operatorname{arctg} x', 'table'],
    ['1/sqrt(1-x^2)', '\\arcsin x', 'table'],
    ['sqrt(x)', '\\frac{2x\\sqrt{x}}{3}', 'table'],
    ['sin(3x)', '-\\frac{1}{3}\\cos(3x)', 'linear-substitution'],
    ['e^(2x)', '\\frac{1}{2}e^{2x}', 'linear-substitution'],
    ['(2x+1)^5', '\\frac{1}{12}(2x + 1)^{6}', 'linear-substitution'],
    ['x*e^(x^2)', '\\frac{1}{2}e^{x^{2}}', 'substitution'],
    ['x/(x^2+1)', '\\frac{1}{2}\\ln(x^{2} + 1)', 'substitution'],
    ['ln(x)/x', '\\frac{1}{2}\\ln^{2} x', 'substitution'],
    ['x*e^x', 'e^{x}(x - 1)', 'parts'],
    ['x*sin(x)', '\\sin x - x\\cos x', 'parts'],
    ['ln(x)', 'x\\ln x - x', 'parts'],
    ['arctg(x)', 'x\\operatorname{arctg} x - \\frac{1}{2}\\ln(x^{2} + 1)', 'parts'],
    ['x^2*e^x', 'e^{x}(x^{2} - 2x + 2)', 'parts'],
    ['arcsin(x)', 'x\\arcsin x + \\sqrt{1 - x^{2}}', 'parts'],
    ['e^x*sin(x)', '\\frac{1}{2}e^{x}(\\sin x - \\cos x)', 'parts-cyclic'],
    ['1/(x^2-1)', '\\frac{1}{2}\\ln\\left|x - 1\\right| - \\frac{1}{2}\\ln\\left|x + 1\\right|', 'rational'],
    ['1/(x^2+2x+5)', '\\frac{1}{2}\\operatorname{arctg}\\left(\\frac{x + 1}{2}\\right)', 'rational'],
    ['1/(x^2+4)', '\\frac{1}{2}\\operatorname{arctg}\\left(\\frac{x}{2}\\right)', 'rational'],
    ['sin(x)^2', '\\frac{x}{2} - \\frac{1}{4}\\sin(2x)', 'trig-power'],
    ['cos(x)^3', '\\sin x - \\frac{1}{3}\\sin^{3} x', 'trig-substitution'],
    ['tg(x)^2', '\\operatorname{tg} x - x', 'trig-substitution'],
    ['1/sqrt(4-x^2)', '\\arcsin\\left(\\frac{x}{2}\\right)', 'quadratic-root'],
    [
        '1/(2+cos(x))',
        '\\frac{2\\sqrt{3}}{3}\\operatorname{arctg}\\left(\\frac{\\operatorname{tg}\\left(\\frac{x}{2}\\right)}{\\sqrt{3}}\\right)',
        'universal-substitution',
    ],
    ['x^2/sqrt(1-x^2)', '\\frac{1}{2}\\arcsin x - \\frac{1}{2}x\\sqrt{1 - x^{2}}', 'radical-polynomial'],
    ['1/(x^2*sqrt(1-x^2))', '-\\frac{\\sqrt{1 - x^{2}}}{x}', 'trig-root-substitution'],
    ['x^8*e^x', 'e^{x}(x^{8} - 8x^{7} + 56x^{6} - 336x^{5} + 1680x^{4} - 6720x^{3} + 20160x^{2} - 40320x + 40320)', 'parts'],
];

test(`integrals: forms and methods of ${INT_FORMS.length} classic cases`, () => {
    for (const [s, want, method] of INT_FORMS) {
        const r = E.integrate(s, 'x');
        assert.equal(tex(r.result), want, s);
        assert.equal(r.method, method, `${s}: method`);
    }
    assert.equal(E.integrate('1/(1+x^2)').tex.en, '\\int \\frac{1}{1 + x^{2}}\\,dx = \\arctan x + C');
});

test('integral steps: every method explains itself', () => {
    for (const s of INTEGRALS) {
        const r = E.integrate(s, 'x', { steps: true });
        checkSteps(r.steps, s);
        assert.equal(r.steps[0].rule, 'start', s);
        assert.equal(r.steps.at(-1).rule, 'answer', s);
        assert.ok(
            r.steps.some((x) => x.rule === 'check'),
            `${s}: check step`,
        );
    }
    const p = E.integrate('x^2*e^x', 'x', { steps: true });
    assert.equal(p.steps[1].rule, 'parts');
    assert.match(p.steps[1].text.ru, /За u берём x²: многочлен при дифференцировании понижает степень/);
    assert.match(p.steps[1].tex, /\\left\[u = x\^\{2\},\\ dv = e\^\{x\}\\,dx;\\ du = 2x\\,dx,\\ v = e\^\{x\}\\right\]/);
    const rat = E.integrate('(x+1)/(x^2-5x+6)', 'x', { steps: true });
    const rules = rat.steps[1].sub.map((s) => s.rule);
    assert.deepEqual(rules, ['factor', 'partial-fractions', 'sum']);
    assert.equal(rat.steps[1].sub[1].tex, '\\frac{x + 1}{x^{2} - 5x + 6} = \\frac{4}{x - 3} - \\frac{3}{x - 2}');
    const lin = E.integrate('sin(3x+1)', 'x', { steps: true });
    assert.match(lin.steps[1].text.ru, /∫f\(kx \+ b\)dx = F\(kx \+ b\)\/k \+ C/);
    const us = E.integrate('x*e^(x^2)', 'x', { steps: true });
    assert.match(us.steps[1].tex, /t = x\^\{2\},\\ dt = 2x\\,dx/);
    const cyc = E.integrate('e^x*cos(x)', 'x', { steps: true });
    assert.match(cyc.steps[1].text.ru, /уравнение I = \(…\) − k·I/);
});

const REFUSE = [
    ['e^(-x^2)', /erf/],
    ['e^(x^2)', /erf/],
    ['sin(x)/x', /Si x/],
    ['cos(x)/x', /Ci x/],
    ['e^x/x', /Ei x/],
    ['1/ln(x)', /li x/],
    ['sin(x^2)', /Френеля/],
    ['cos(x^2)', /Френеля/],
    ['x^x', /xˣ/],
    ['sqrt(1+x^3)', /не берёт/],
    ['e^(e^x)', /не берёт/],
    ['sqrt(sin(x))', /не берёт/],
    ['x*tg(x)', /не берёт/],
    ['sin(x)/(x+1)', /не берёт/],
];

test('integrals: honest refusals with a reason (and a hint for known non-elementary integrals)', () => {
    for (const [s, re] of REFUSE) {
        const r = E.integrate(s, 'x', { steps: true });
        assert.equal(r.result, null, `${s} must be refused`);
        assert.equal(r.verified, false);
        assert.match(r.reason.ru, re, s);
        assert.ok(r.reason.en.length > 20);
        checkSteps(r.steps, s);
        assert.equal(r.steps.at(-1).rule, 'fail');
    }
    assert.ok(refused(E.integrate('x = 2'), (e) => e.code === 'not-expr'));
});

// ---------------------------------------------------------------- definite integrals

const DEFINITE = [
    // [f, a, b, exact value | 'diverges' | 'approx', expected numeric]
    ['x^2', '0', '1', '1/3'],
    ['sin(x)', '0', 'pi', '2'],
    ['1/x', '1', 'e', '1'],
    ['x*e^x', '0', '1', '1'],
    ['cos(x)^2', '0', 'pi', 'pi/2'],
    ['1/(1+x^2)', '0', '1', 'pi/4'],
    ['sqrt(1-x^2)', '-1', '1', 'pi/2'],
    ['abs(x)', '-1', '2', '5/2'],
    ['x^2', '2', '0', '-8/3'],
    ['tan(x)', '0', 'pi/4', 'ln(2)/2'],
    ['1/(x^2-1)', '2', '3', 'ln(3/2)/2'],
    ['x^3-2x', '-1', '1', '0'],
    ['e^(-x)', '0', 'inf', '1'],
    ['1/x^2', '1', 'inf', '1'],
    ['1/(1+x^2)', '-inf', 'inf', 'pi'],
    ['x*e^(-x^2)', '0', 'inf', '1/2'],
    ['1/sqrt(x)', '0', '1', '2'],
    ['ln(x)', '0', '1', '-1'],
    ['x*ln(x)', '0', '1', '-1/4'],
    ['1/sqrt(1-x^2)', '-1', '1', 'pi'],
    ['1/(2+cos(x))', '0', '2pi', '2pi/sqrt(3)'],
    ['1/x', '1', 'inf', 'diverges'],
    ['1/x^2', '-1', '1', 'diverges'],
    ['1/x', '-1', '1', 'diverges'],
    ['1/(x^2-1)', '0', '2', 'diverges'],
    ['1/(x*ln(x))', '2', 'inf', 'diverges'],
    ['e^x', '0', 'inf', 'diverges'],
    ['e^(-x^2)', '0', '1', 'approx', 0.746824132812427],
    ['sin(x)/x', '0', 'pi', 'approx', 1.851937051982466],
];

test(`definite integrals: ${DEFINITE.length} cases — exact, improper, divergent, numeric`, () => {
    for (const [f, a, b, want, approx] of DEFINITE) {
        const r = E.integrateDefinite(f, 'x', a, b, { steps: true });
        const where = `∫[${a}, ${b}] ${f}`;
        checkSteps(r.steps, where);
        if (want === 'diverges') {
            assert.equal(r.converges, false, `${where} must diverge`);
            assert.match(r.tex.ru, /расходится/);
            assert.match(r.tex.en, /diverges/);
            continue;
        }
        if (want === 'approx') {
            assert.equal(r.exact, false, where);
            assert.equal(r.approx, true, where);
            assert.ok(Math.abs(r.numeric - approx) < 1e-8, `${where}: ${r.numeric}`);
            assert.match(typeof r.tex === 'string' ? r.tex : r.tex.ru, /\\approx/);
            continue;
        }
        assert.equal(r.exact, true, `${where}: exact`);
        assert.equal(r.converges, true);
        const exp = E.evaluate(E.parse(want));
        assert.ok(Math.abs(E.evaluate(r.value) - exp) < 1e-9, `${where}: ${tex(r.value)} vs ${want}`);
        assert.ok(Math.abs(r.numeric - exp) < 1e-9, `${where}: numeric`);
    }
    assert.equal(tex(E.integrateDefinite('1/(x^2-1)', 'x', 2, 3).value), '\\frac{1}{2}\\ln\\left(\\frac{3}{2}\\right)');
    assert.equal(tex(E.integrateDefinite('tan(x)', 'x', 0, 'pi/4').value), '\\frac{1}{2}\\ln 2');
    assert.equal(E.integrateDefinite('e^(-x)', 'x', 0, Infinity).improper, true);
    assert.equal(E.integrateDefinite('x', 'x', 3, 3).numeric, 0);
    const und = E.integrateDefinite('sqrt(x)', 'x', -1, 1, { steps: true });
    assert.equal(und.method, 'undefined');
    assert.equal(und.value, null);
    assert.ok(refused(E.integrateDefinite('a*x', 'x', 0, 1), (e) => e.code === 'unbound'));
});

test('area between curves', () => {
    const r = E.areaBetween('x', 'x^2', 'x', null, null, { steps: true });
    assert.equal(tex(r.value), '\\frac{1}{6}');
    assert.deepEqual(
        r.points.map((p) => tex(p)),
        ['0', '1'],
    );
    checkSteps(r.steps, 'area');
    const s = E.areaBetween('sin(x)', '0', 'x', 0, '2pi');
    assert.equal(tex(s.value), '4');
    assert.equal(s.pieces.length, 2);
    const c = E.areaBetween('x^3', 'x', 'x', -1, 1);
    assert.equal(tex(c.value), '\\frac{1}{2}');
    const n = E.areaBetween('e^(-x^2)', '0', 'x', 0, 1);
    assert.equal(n.value, null);
    assert.ok(Math.abs(n.numeric - 0.746824132812427) < 1e-8);
});

// ---------------------------------------------------------------- limits

const LIMITS = [
    // [f, a, expected, side?] — expected: an exact value, 'inf', '-inf' or 'dne'
    ['x^2+3x-1', '2', '9'],
    ['(x+1)/(x-3)', '1', '-1'],
    ['sqrt(x+5)', '4', '3'],
    ['e^x+ln(x)', '1', 'e'],
    ['sin(x)+cos(x)', 'pi', '-1'],
    ['arctg(x)', '1', 'pi/4'],
    ['2^x', '3', '8'],
    ['abs(x-2)', '0', '2'],
    ['(x^2-1)/(x-1)', '1', '2'],
    ['(x^2-4)/(x-2)', '2', '4'],
    ['(x^2-5x+6)/(x^2-4)', '2', '-1/4'],
    ['(x^3-1)/(x-1)', '1', '3'],
    ['(x^3-8)/(x^2-4)', '2', '3'],
    ['(x^2+x-2)/(x^2-1)', '1', '3/2'],
    ['(x^4-1)/(x^3-1)', '1', '4/3'],
    ['(2x^2-x-1)/(x^2-1)', '1', '3/2'],
    ['(x^2-3x+2)/(x^2-4x+3)', '1', '1/2'],
    ['((1+x)^5-1)/x', '0', '5'],
    ['(x^3-x^2-x+1)/(x^3-3x+2)', '1', '2/3'],
    ['(x^2-9)/(x+3)', '-3', '-6'],
    ['(3x^2+1)/(2x^2-x)', 'inf', '3/2'],
    ['(x^3+1)/(x^2+5)', 'inf', 'inf'],
    ['(x+1)/(x^3+2)', 'inf', '0'],
    ['(5x^3-2x)/(1-x^3)', 'inf', '-5'],
    ['(x^2+1)/(x-1)', '-inf', '-inf'],
    ['(2x-3)^3/(x^3+1)', 'inf', '8'],
    ['x^3-100x^2', 'inf', 'inf'],
    ['x^3-x', '-inf', '-inf'],
    ['(1-x)^4/(x^4+x)', '-inf', '1'],
    ['1/x', 'inf', '0'],
    ['(x^2+3)/(2x^2)', '-inf', '1/2'],
    ['(2x+1)/sqrt(x^2+1)', 'inf', '2'],
    ['(2x+1)/sqrt(x^2+1)', '-inf', '-2'],
    ['sqrt(x^2+1)/x', '-inf', '-1'],
    ['(sqrt(x)+1)/(sqrt(x)-1)', 'inf', '1'],
    ['sqrt(4x^2+x)/(x+1)', 'inf', '2'],
    ['cbrt(x^3+1)/x', 'inf', '1'],
    ['(sqrt(x+4)-2)/x', '0', '1/4'],
    ['(sqrt(1+x)-sqrt(1-x))/x', '0', '1'],
    ['sqrt(x^2+x)-x', 'inf', '1/2'],
    ['sqrt(x^2+2x)-sqrt(x^2-2x)', 'inf', '2'],
    ['x-sqrt(x^2-1)', 'inf', '0'],
    ['(x-4)/(sqrt(x)-2)', '4', '4'],
    ['(sqrt(x+1)-1)/(sqrt(x+4)-2)', '0', '2'],
    ['sqrt(x+1)-sqrt(x)', 'inf', '0'],
    ['(3-sqrt(x+5))/(x-4)', '4', '-1/6'],
    ['cbrt(x+1)-cbrt(x)', 'inf', '0'],
    ['sin(x)/x', '0', '1'],
    ['sin(3x)/x', '0', '3'],
    ['sin(5x)/sin(2x)', '0', '5/2'],
    ['tg(3x)/sin(5x)', '0', '3/5'],
    ['(1-cos(x))/x^2', '0', '1/2'],
    ['(1-cos(4x))/(x*sin(x))', '0', '8'],
    ['(e^x-1)/x', '0', '1'],
    ['(e^(3x)-1)/sin(2x)', '0', '3/2'],
    ['ln(1+x)/x', '0', '1'],
    ['ln(1+3x)/tg(2x)', '0', '3/2'],
    ['(2^x-1)/x', '0', 'ln(2)'],
    ['arcsin(2x)/x', '0', '2'],
    ['arctg(x)/(3x)', '0', '1/3'],
    ['((1+x)^(1/3)-1)/x', '0', '1/3'],
    ['(sqrt(1+x)-1)/x', '0', '1/2'],
    ['ln(cos(x))/x^2', '0', '-1/2'],
    ['x*sin(1/x)', 'inf', '1'],
    ['x*ln(1+1/x)', 'inf', '1'],
    ['x*(e^(1/x)-1)', 'inf', '1'],
    ['sin(x^2)/(1-cos(x))', '0', '2'],
    ['(e^(2x)-1)/ln(1+x)', '0', '2'],
    ['sh(x)/x', '0', '1'],
    ['(1-cos(x))/sin(x)^2', '0', '1/2'],
    ['tg(x)^2/(x*sin(x))', '0', '1'],
    ['(3^x-2^x)/x', '0', 'ln(3/2)'],
    ['(1+1/x)^x', 'inf', 'e'],
    ['(1+x)^(1/x)', '0', 'e'],
    ['(1+2/x)^(3x)', 'inf', 'e^6'],
    ['(1-1/x)^x', 'inf', '1/e'],
    ['(cos x)^(1/x^2)', '0', 'e^(-1/2)'],
    ['((x+1)/(x-1))^x', 'inf', 'e^2'],
    ['(1+sin(x))^(1/x)', '0', 'e'],
    ['(1+3x)^(2/x)', '0', 'e^6'],
    ['((x^2+1)/(x^2-1))^(x^2)', 'inf', 'e^2'],
    ['(1+tg(x))^(1/sin(x))', '0', 'e'],
    ['sin(x)^tg(x)', 'pi/2', '1', 'left'],
    ['(e^x+x)^(1/x)', '0', 'e^2'],
    ['(x-sin(x))/x^3', '0', '1/6'],
    ['ln(x)/x', 'inf', '0'],
    ['x^2/e^x', 'inf', '0'],
    ['e^x/x^3', 'inf', 'inf'],
    ['ln(x)/sqrt(x)', 'inf', '0'],
    ['(e^x-1-x)/x^2', '0', '1/2'],
    ['(tg(x)-x)/x^3', '0', '1/3'],
    ['(x-arctg(x))/x^3', '0', '1/3'],
    ['ln(x)/(x-1)', '1', '1'],
    ['(e^x-e^(-x))/sin(x)', '0', '2'],
    ['x^3*e^(-x)', 'inf', '0'],
    ['1/x - 1/sin(x)', '0', '0'],
    ['1/x-1/(e^x-1)', '0', '1/2'],
    ['1/ln(1+x)-1/x', '0', '1/2'],
    ['ln(x)^2/x', 'inf', '0'],
    ['(tan(x)-sin(x))/x^3', '0', '1/2'],
    ['(x+sin(x))/x', 'inf', '1'],
    ['x/(x+sin(x))', 'inf', '1'],
    ['(x^2+sin(x))/(x^2+cos(x))', 'inf', '1'],
    ['x*ln(x)', '0', '0', 'right'],
    ['x^x', '0', '1', 'right'],
    ['x^(1/x)', 'inf', '1'],
    ['x^2*ln(x)', '0', '0', 'right'],
    ['sqrt(x)*ln(x)', '0', '0', 'right'],
    ['x*e^(-x)', 'inf', '0'],
    ['(1/x)^(tg(x))', '0', '1', 'right'],
    ['x^(sin(x))', '0', '1', 'right'],
    ['ln(sin(x))/ln(x)', '0', '1', 'right'],
    ['1/x^2', '0', 'inf'],
    ['-1/x^2', '0', '-inf'],
    ['arctg(x)', 'inf', 'pi/2'],
    ['arctg(x)', '-inf', '-pi/2'],
    ['e^(-x)', 'inf', '0'],
    ['e^x', '-inf', '0'],
    ['ln(x)', '0', '-inf', 'right'],
    ['sin(x)/x', 'inf', '0'],
    ['x-ln(x)', 'inf', 'inf'],
    ['1/(x-1)', '1', 'inf', 'right'],
    ['1/(x-1)', '1', '-inf', 'left'],
    ['e^(1/x)', '0', '0', 'left'],
    ['e^(1/x)', '0', 'inf', 'right'],
    ['arctg(1/x)', '0', 'pi/2', 'right'],
    ['arctg(1/x)', '0', '-pi/2', 'left'],
    ['tg(x)', 'pi/2', 'inf', 'left'],
    ['2^(1/x)', '0', '0', 'left'],
    ['x*sin(x)', '0', '0'],
    ['sqrt(x)', '0', '0', 'right'],
    ['x^2*sin(1/x)', '0', '0'],
    ['x*cos(1/x)', '0', '0'],
    ['1/x', '0', 'dne'],
    ['abs(x)/x', '0', 'dne'],
    ['sin(x)', 'inf', 'dne'],
    ['e^(1/x)', '0', 'dne'],
    ['floor(x)', '1', 'dne'],
    ['sign(x)', '0', 'dne'],
    ['tg(x)', 'pi/2', 'dne'],
    ['(x^2+x-2)/(x-1)^2', '1', 'dne'],
    ['arctg(1/x)', '0', 'dne'],
    ['cos(x)', 'inf', 'dne'],
    ['cos(1/x)', '0', 'dne'],
    ['(2+x)^(1/x)', '0', 'dne'],
    ['(x^3+x^2-x-1)/(x^3-3x+2)', '1', 'dne'],
    ['x/(1-cos(x))', '0', 'dne'],
    ['abs(x)/x', '0', '1', 'right'],
    ['abs(x)/x', '0', '-1', 'left'],
    ['(x^2-1)/abs(x-1)', '1', '2', 'right'],
    ['(x^2-1)/abs(x-1)', '1', '-2', 'left'],
    ['floor(x)', '2', '1', 'left'],
    ['floor(x)', '2', '2', 'right'],
];

test(`limits: ${LIMITS.length} classic problems, each checked against the numbers near the point`, () => {
    assert.ok(LIMITS.length >= 100);
    for (const [f, a, want, side] of LIMITS) {
        const r = E.limit(f, 'x', a, { side: side ?? 'both' });
        const where = `lim ${f}, x → ${a}${side ? ' ' + side : ''}`;
        if (want === 'inf' || want === '-inf' || want === 'dne') {
            assert.equal(r.value, want, `${where}: got ${typeof r.value === 'object' && r.value ? tex(r.value) : r.value}`);
        } else {
            assert.ok(r.value && typeof r.value === 'object', `${where}: got ${r.value} (≈ ${r.approx})`);
            const exp = E.evaluate(E.parse(want));
            assert.ok(Math.abs(E.evaluate(r.value) - exp) < 1e-12 * Math.max(1, Math.abs(exp)), `${where}: ${tex(r.value)} vs ${want}`);
        }
        assert.equal(r.verified, true, `${where}: numeric cross-check`);
        assert.equal(r.approx, undefined, `${where}: must be exact`);
        // the table approaches the point and, for a finite limit, its last values are near the answer
        assert.ok(r.table.length >= 6, `${where}: table`);
        if (want !== 'inf' && want !== '-inf' && want !== 'dne') {
            const exp = E.evaluate(E.parse(want));
            const near = r.table.filter((row) => Number.isFinite(row.fx)).map((row) => Math.abs(row.fx - exp));
            assert.ok(Math.min(...near) < 0.05 * Math.max(1, Math.abs(exp)), `${where}: table is far from ${want}`);
        }
    }
});

test('limit steps: the method is named, the form is identified, the table is attached', () => {
    const cases = [
        ['(x^2-1)/(x-1)', '1', 'factor-cancel', '0/0'],
        ['sin(3x)/x', '0', 'equivalents', '0/0'],
        ['(sqrt(x+4)-2)/x', '0', 'conjugate', '0/0'],
        ['(3x^2+1)/(2x^2-x)', 'inf', 'rational-infinity', null],
        ['(1+2/x)^(3x)', 'inf', 'second-remarkable', '1^inf'],
        ['(x-sin(x))/x^3', '0', 'lhopital', '0/0'],
        ['x*ln(x)', '0', 'rewrite-fraction', '0*inf'],
        ['1/x-1/(e^x-1)', '0', 'common-denominator', null],
        ['x^x', '0', 'exp-log', '0^0'],
    ];
    for (const [f, a, method, form] of cases) {
        const r = E.limit(f, 'x', a, { steps: true, side: f.startsWith('x*ln') || f === 'x^x' ? 'right' : 'both' });
        checkSteps(r.steps, f);
        assert.equal(r.method, method, f);
        const rules = r.steps.map((s) => s.rule);
        assert.equal(rules[0], 'start', f);
        assert.ok(rules.includes('table'), `${f}: table step`);
        assert.equal(rules.at(-1), 'answer', f);
        if (form) {
            const fs = r.steps.find((s) => s.rule === 'form');
            assert.ok(fs, `${f}: form step`);
            assert.match(fs.text.ru, /неопределённость/);
        }
    }
    const eq = E.limit('tg(3x)/sin(5x)', 'x', 0, { steps: true });
    const st = eq.steps.find((s) => s.rule === 'equivalents');
    assert.match(st.text.ru, /sin u ~ u/);
    assert.match(pick(st.tex), /\\sin\(5x\) \\sim 5x/);
    const lh = E.limit('ln(x)/x', 'x', 'inf', { steps: true });
    assert.match(lh.steps.find((s) => s.rule === 'lhopital').text.ru, /правилу Лопиталя/);
    const sub = E.limit('x^2+1', 'x', 2, { steps: true });
    assert.equal(sub.method, 'substitution');
    assert.equal(sub.tex, '\\lim_{x \\to 2} \\left(x^{2} + 1\\right) = 5');
    const one = E.limit('1/x', 'x', 0, { steps: true });
    assert.deepEqual(one.sides, { left: '-inf', right: 'inf' });
    assert.ok(one.steps.some((s) => s.rule === 'dne'));
    assert.equal(one.tex.ru, '\\lim_{x \\to 0} \\frac{1}{x} = \\text{не существует}');
    assert.equal(one.tex.en, '\\lim_{x \\to 0} \\frac{1}{x} = \\text{does not exist}');
    assert.equal(E.limit('1/x', 'x', 0, { side: 'right' }).tex, '\\lim_{x \\to {0}^{+}} \\frac{1}{x} = +\\infty');
});

test("limits: parameters, other variables, L'Hôpital only when it applies, numeric fallback marked ≈", () => {
    assert.equal(tex(E.limit('((x+h)^2-x^2)/h', 'h', 0).value), '2x');
    assert.equal(tex(E.limit('(sin(x+h)-sin(x))/h', 'h', 0).value), '\\cos x');
    assert.equal(tex(E.limit('(1+a/x)^x', 'x', 'inf').value), 'e^{a}');
    assert.equal(tex(E.limit('sin(a*x)/x', 'x', 0).value), 'a');
    assert.equal(tex(E.limit('(a^x-1)/x', 'x', 0).value), '\\ln a');
    assert.equal(tex(E.limit('(1+1/n)^n', 'n', 'inf').value), 'e');
    // (x + sin x)/x: the ratio of derivatives (1 + cos x)/1 has no limit — L'Hôpital must not conclude «dne»
    const r = E.limit('(x+sin(x))/x', 'x', 'inf', { steps: true });
    assert.equal(tex(r.value), '1');
    assert.notEqual(r.method, 'lhopital');
    assert.equal(E.limit('x^2/e^x', 'x', Infinity).value.type, 'num');
    assert.equal(E.limit('x^2/e^x', 'x', -Infinity).value, 'inf');
    // a limit no symbolic method handles: numeric, clearly marked
    const n = E.limit('(x^x - x)/(1 - x + ln(x))', 'x', 1, { steps: true });
    if (n.approx !== undefined) {
        assert.equal(n.value, null);
        assert.match(n.tex.ru ?? n.tex, /\\approx/);
        assert.ok(n.steps.some((s) => s.rule === 'numeric'));
    } else assert.equal(tex(n.value), '-2');
    assert.ok(refused(E.limit('x = 1', 'x', 0), (e) => e.code === 'not-expr'));
    assert.ok(refused(E.limit('x', 'x', 'y'), (e) => e.code === 'range' || e.code === 'unbound'));
});

// ---------------------------------------------------------------- Taylor polynomials

test('Taylor polynomials with exact coefficients', () => {
    const e = E.taylorPolynomial('e^x', 'x', 0, 4, { steps: true });
    assert.deepEqual(
        e.coeffs.map((c) => tex(c)),
        ['1', '1', '\\frac{1}{2}', '\\frac{1}{6}', '\\frac{1}{24}'],
    );
    checkSteps(e.steps, 'taylor e^x');
    const s = E.taylorPolynomial('sin(x)', 'x', 0, 7);
    assert.deepEqual(
        s.coeffs.map((c) => tex(c)),
        ['0', '1', '0', '-\\frac{1}{6}', '0', '\\frac{1}{120}', '0', '-\\frac{1}{5040}'],
    );
    assert.equal(s.tex, 'T_{7}(x) = x - \\frac{x^{3}}{6} + \\frac{x^{5}}{120} - \\frac{x^{7}}{5040}');
    const l = E.taylorPolynomial('ln(1+x)', 'x', 0, 4);
    assert.deepEqual(
        l.coeffs.map((c) => tex(c)),
        ['0', '1', '-\\frac{1}{2}', '\\frac{1}{3}', '-\\frac{1}{4}'],
    );
    const g = E.taylorPolynomial('1/(1-x)', 'x', 0, 5);
    assert.ok(g.coeffs.every((c) => tex(c) === '1'));
    const c = E.taylorPolynomial('cos(x)', 'x', 'pi/2', 3);
    assert.deepEqual(
        c.coeffs.map((k) => tex(k)),
        ['0', '-1', '0', '\\frac{1}{6}'],
    );
    const r = E.taylorPolynomial('sqrt(x)', 'x', 1, 2);
    assert.deepEqual(
        r.coeffs.map((k) => tex(k)),
        ['1', '\\frac{1}{2}', '-\\frac{1}{8}'],
    );
    // sin x / x at 0: the removable singularity is filled in by limits
    const sx = E.taylorPolynomial('sin(x)/x', 'x', 0, 4);
    assert.deepEqual(
        sx.coeffs.map((k) => tex(k)),
        ['1', '0', '-\\frac{1}{6}', '0', '\\frac{1}{120}'],
    );
    // the polynomial approximates the function near the point
    for (const [f, a, n] of [
        ['e^x', 0, 8],
        ['cos(x)', 0, 8],
        ['atan(x)', 0, 9],
        ['ln(x)', 1, 8],
        ['tan(x)', 0, 7],
    ]) {
        const T = E.taylorPolynomial(f, 'x', a, n);
        const x = a + 0.1;
        assert.ok(Math.abs(E.evaluate(T.poly, { x }) - E.evaluate(E.parse(f), { x })) < 1e-7, `${f}: Taylor error`);
    }
    assert.ok(refused(E.taylorPolynomial('ln(x)', 'x', 0, 3), (err) => err.code === 'undefined'));
    const b = E.taylorRemainderBound('e^x', 'x', 0, 4, 1);
    assert.ok(b.bound >= Math.E - (1 + 1 + 1 / 2 + 1 / 6 + 1 / 24) - 1e-12);
    assert.ok(b.bound < 0.03);
});

test('integrate: substitutions that were missed before', () => {
    for (const [f, want] of [
        ['1/(1+cos(x))', 'tan(x/2)'],
        ['x/(x^4+1)', 'atan(x^2)/2'],
        ['x^3/(x^8+1)', 'atan(x^4)/4'],
        ['cos(ln(x))', 'x*(sin(ln(x)) + cos(ln(x)))/2'],
        ['x*tg(x)^2', 'x*tan(x) - x^2/2 + ln(abs(cos(x)))'],
    ]) {
        const r = E.integrate(E.parse(f), 'x', { steps: true });
        assert.ok(r.result && r.verified, `${f}: ${r.reason?.en}`);
        // the answer may differ from ours by a constant
        const d = (x) => E.evaluate(r.result, { x }) - E.evaluate(E.parse(want), { x });
        assert.ok(Math.abs(d(0.3) - d(0.7)) < 1e-9, `${f}: ${E.toText(r.result)}`);
    }
    // x·ln x stays with integration by parts
    assert.equal(E.integrate(E.parse('x*ln(x)'), 'x').method, 'parts');
    // the rationalizing step shows x as a plain expression of t
    const st = E.integrate(E.parse('sqrt(x+1)/x'), 'x', { steps: true }).steps.find((s) => s.rule === 'rationalizing');
    assert.ok(!/\\frac\{[^}]*\}\{1\}/.test(typeof st.tex === 'function' ? st.tex('ru') : st.tex.ru));
    // e^(x²) is erfi, e^(−x²) is erf
    assert.match(E.integrate(E.parse('e^(x^2)'), 'x').reason.ru, /erfi/);
    assert.match(E.integrate(E.parse('e^(-x^2)'), 'x').reason.ru, /erf x/);
});

test('integrateDefinite: oscillating tails', () => {
    const r = E.integrateDefinite(E.parse('sin(x)/x'), 'x', 0, E.parse('inf'));
    assert.equal(r.converges, true);
    assert.ok(Math.abs(r.numeric - Math.PI / 2) < 1e-8);
    const s = E.integrateDefinite(E.parse('sin(x^2)'), 'x', 0, E.parse('inf'));
    assert.ok(Math.abs(s.numeric - Math.sqrt(Math.PI / 8)) < 1e-8);
    const d = E.integrateDefinite(E.parse('sin(x)'), 'x', 0, E.parse('inf'));
    assert.equal(d.converges, false);
    assert.equal(E.integrateDefinite(E.parse('e^(x^2)'), 'x', 0, E.parse('inf')).value, 'inf');
});

test('limit: a function that lives on one side of the point', () => {
    for (const [f, a, want, side] of [
        ['x*ln(x)', 0, '0', 'right'],
        ['x^x', 0, '1', 'right'],
        ['sqrt(1-x)', 1, '0', 'left'],
    ]) {
        const r = E.limit(E.parse(f), 'x', a, { steps: true });
        assert.equal(E.toText(r.value), want, f);
        assert.equal(r.domainSide, side, f);
        assert.ok(
            r.steps.some((s) => s.rule === 'domain-side'),
            f,
        );
    }
    assert.equal(E.limit(E.parse('ln(x)'), 'x', 0).value, '-inf');
    // defined on both sides: nothing changes
    assert.equal(E.limit(E.parse('1/x'), 'x', 0).value, 'dne');
    assert.equal(E.limit(E.parse('1/x'), 'x', 0).domainSide, undefined);
});

test('∫(c₂x² + c₀)/(x⁴ + px² + q) through t = x ∓ √q/x', () => {
    const d = (F, f, x) => {
        const h = 1e-5;
        const g = (t) => E.evaluate(F, { x: t });
        return Math.abs((g(x + h) - g(x - h)) / (2 * h) - E.evaluate(E.parse(f), { x }));
    };
    for (const f of ['1/(x^4 + 1)', 'x^2/(x^4 + 1)', '1/(x^4 - x^2 + 1)', '3/(2x^4 + 2)', '1/(x^4 + x^2 + 2)']) {
        const r = E.integrate(f, 'x', { steps: true });
        assert.equal(r.method, 'biquadratic', f);
        for (const x of [-2.3, -0.4, 0.7, 1.9]) assert.ok(d(r.result, f, x) < 1e-6, `${f} at ${x}`);
    }
    const def = E.integrateDefinite('1/(x^4 + 1)', 'x', '-1', '1');
    assert.ok(Math.abs(E.evaluate(def.value, {}) - 1.7339459747) < 1e-8);
});
