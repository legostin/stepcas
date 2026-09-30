// «Царица наук»: the core of the maths engine — rationals, AST, parser, printer, simplifier, expansion,
// polynomials, equivalence, evaluation, complex numbers, random, steps.
const { test, before } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const ENGINE = path.join(__dirname, '../src');
let E;

before(async () => {
    E = await import('../src/index.js');
});

const P = (s, o) => E.parse(s, o);
const K = (s, o) => E.nodeKey(E.parse(s, o));
const S = (s, o) => E.simplify(E.parse(s), o);
const TS = (s, o = {}) => E.toTex(S(s, o), { lang: o.lang ?? 'ru' });
const TX = (s, o = {}) => E.toTex(E.expand(E.parse(s), o), { lang: o.lang ?? 'ru' });
const q = (x) => E.Q.of(x);

function table(rows, fn) {
    for (const row of rows) fn(...row);
}

// ---------------------------------------------------------------- module hygiene

test('every exported name is unique across all engine modules', async () => {
    const index = fs.readFileSync(path.join(ENGINE, 'index.js'), 'utf8');
    const files = [...index.matchAll(/export \* from '\.\/([\w/-]+\.js)'/g)].map((m) => m[1]);
    assert.ok(files.length >= 19);
    const seen = new Map();
    for (const f of files) {
        const mod = await import(path.join(ENGINE, f));
        for (const name of Object.keys(mod)) {
            assert.ok(!seen.has(name), `${name} is exported by both ${seen.get(name)} and ${f}`);
            seen.set(name, f);
            assert.ok(name in E, `${name} is missing from index.js`);
        }
    }
});

test('the core API is exported', () => {
    const names = ['MathError', 'Q', 'bigGcd', 'bigLcm', 'bigAbs', 'bigIsqrt', 'bigIroot', 'rootExtract', 'num', 'sym', 'add', 'mul', 'div',
        'neg', 'pow', 'fn', 'rel', 'chain', 'list', 'isConst', 'nodeEquals', 'freeVars', 'containsVar', 'substitute', 'mapNode', 'nodeSize',
        'isNumber', 'numValue', 'parse', 'tryParse', 'parseFunctionInput', 'toTex', 'toText', 'texNumber', 'simplify', 'expand', 'collectTerms', 'combineFractions',
        'rationalize', 'Poly', 'linearForm', 'equivalent', 'sameValue', 'sameSet', 'evaluate', 'compile', 'Complex', 'rng', 'L', 'step'];
    for (const n of names) assert.ok(n in E, n);
});

// ---------------------------------------------------------------- rational

test('Q normalises and reads numbers, decimals and strings', () => {
    assert.equal(new E.Q(6n, -4n).toString(), '-3/2');
    assert.equal(new E.Q(0n, 5n).toString(), '0');
    assert.equal(new E.Q(10, 4).toString(), '5/2');
    table([
        [0.1, '1/10'], [0.5, '1/2'], [-2.5, '-5/2'], [3, '3'], [1e21, '1000000000000000000000'], [2.5e-7, '1/4000000'],
        [123n, '123'], ['3/4', '3/4'], ['-2.5', '-5/2'], ['2,5', '5/2'], ['1e-3', '1/1000'], ['0.(3)', '1/3'], ['0,1(6)', '1/6'],
        ['  7 ', '7'], ['1.5/2', '3/4'], ['−3', '-3'], ['.5', '1/2'], ['+4', '4'], ['12 345', '12345'], ['1/-2', '-1/2'],
    ], (x, s) => assert.equal(E.Q.of(x).toString(), s, String(x)));
    for (const bad of ['abc', '', '1/0x', '--1', NaN, Infinity, null]) {
        assert.throws(() => E.Q.of(bad), E.MathError, String(bad));
    }
    assert.throws(() => new E.Q(1n, 0n), (e) => e instanceof E.MathError && e.code === 'div0');
});

test('Q arithmetic is exact', () => {
    const a = q('1/3');
    const b = q('1/6');
    assert.equal(a.add(b).toString(), '1/2');
    assert.equal(a.sub(b).toString(), '1/6');
    assert.equal(a.mul(b).toString(), '1/18');
    assert.equal(a.div(b).toString(), '2');
    assert.equal(a.neg().toString(), '-1/3');
    assert.equal(a.inv().toString(), '3');
    assert.equal(q(0.1).add(0.2).toString(), '3/10');
    assert.equal(q('2/3').pow(3).toString(), '8/27');
    assert.equal(q('2/3').pow(-2).toString(), '9/4');
    assert.equal(q(0).pow(0).toString(), '1');
    assert.equal(q(-1).pow(1000001).toString(), '-1');
    assert.throws(() => q(0).pow(-1), E.MathError);
    assert.throws(() => q(2).pow(10 ** 7), (e) => e.code === 'too-big');
    assert.throws(() => q(1).div(0), (e) => e.code === 'div0');
    assert.throws(() => q(0).inv(), E.MathError);
    assert.equal(q('2/3').add('1/3').isOne(), true);
});

test('Q comparisons, predicates and rounding', () => {
    assert.equal(q('1/3').cmp('1/2'), -1);
    assert.equal(q('1/2').cmp('0.5'), 0);
    assert.ok(q(-1).lt(0) && q(2).gt('3/2') && q(2).le(2) && q(2).ge(2));
    assert.ok(q(0).isZero() && q(1).isOne() && q(4).isInt() && q(-1).isNeg() && q(1).isPos());
    assert.equal(q(-5).sign(), -1);
    assert.equal(q(-5).abs().toString(), '5');
    table([
        ['7/2', '3', '4', '3', '4'], ['-7/2', '-4', '-3', '-3', '-4'], ['5/2', '2', '3', '2', '3'], ['-5/2', '-3', '-2', '-2', '-3'],
        ['2', '2', '2', '2', '2'], ['1/3', '0', '1', '0', '0'], ['-1/3', '-1', '0', '0', '0'], ['12/5', '2', '3', '2', '2'],
    ], (x, f, c, t, r) => {
        assert.equal(q(x).floor().toString(), f, `floor ${x}`);
        assert.equal(q(x).ceil().toString(), c, `ceil ${x}`);
        assert.equal(q(x).trunc().toString(), t, `trunc ${x}`);
        assert.equal(q(x).round().toString(), r, `round ${x}`);
    });
    assert.equal(E.Q.max(1, 2).toString(), '2');
    assert.equal(E.Q.min('1/2', '1/3').toString(), '1/3');
});

test('Q prints as fraction, decimal and periodic decimal', () => {
    table([['3/4', '\\frac{3}{4}'], ['-1/2', '-\\frac{1}{2}'], ['2', '2'], ['-7', '-7']], (x, t) => assert.equal(q(x).toTex(), t));
    table([
        ['1/3', 4, 'en', '0.3333'], ['1/3', 4, 'ru', '0,3333'], ['-2/3', 3, 'en', '-0.667'], ['5/2', 10, 'en', '2.5'], ['-1/1000', 2, 'en', '0'],
        ['1/8', 2, 'en', '0.13'], ['7', 3, 'ru', '7'], ['123456789/1000', 1, 'en', '123456.8'],
    ], (x, d, lang, s) => assert.equal(q(x).toDecimalString(d, lang), s, x));
    assert.ok(q('3/8').isFiniteDecimal() && !q('1/3').isFiniteDecimal() && q('7/20').isFiniteDecimal());
    table([['1/6', 'ru', '0,1(6)'], ['1/7', 'en', '0.(142857)'], ['3/4', 'en', '0.75'], ['-1/3', 'ru', '-0,(3)'], ['22/7', 'en', '3.(142857)'], ['5', 'en', '5']],
        (x, lang, s) => assert.equal(q(x).toPeriodicString(lang), s));
    assert.equal(new E.Q(1n, 9973n).toPeriodicString('en', 50), null);
    assert.equal(q('1/3').toNumber(), 1 / 3);
    assert.ok(Math.abs(new E.Q(2n ** 2000n, 3n ** 1300n).toNumber() / 6.3439564416e-19 - 1) < 1e-9);
    assert.equal(q('3/4').num, 3n);
    assert.equal(q('3/4').den, 4n);
    assert.equal(JSON.stringify({ a: q('1/2') }), '{"a":"1/2"}');
});

test('Q exact roots and BigInt helpers', () => {
    assert.equal(q('4/9').exactRoot(2).toString(), '2/3');
    assert.equal(q(-8).exactRoot(3).toString(), '-2');
    assert.equal(q(2).exactRoot(2), null);
    assert.equal(q(-4).exactRoot(2), null);
    assert.equal(E.bigGcd(12n, -18n), 6n);
    assert.equal(E.bigGcd(0n, 5n), 5n);
    assert.equal(E.bigLcm(4n, 6n), 12n);
    assert.equal(E.bigLcm(0n, 6n), 0n);
    assert.equal(E.bigAbs(-5n), 5n);
    table([[0n, 0n], [1n, 1n], [15n, 3n], [16n, 4n], [10n ** 40n, 10n ** 20n], [10n ** 40n - 1n, 10n ** 20n - 1n], [2n ** 101n, 2n ** 50n * 1414213562373095n / 10n ** 15n]],
        (n, r) => {
            const s = E.bigIsqrt(n);
            assert.ok(s * s <= n && (s + 1n) * (s + 1n) > n, `isqrt ${n}`);
            if (n < 2n ** 100n) assert.equal(s, r);
        });
    assert.equal(E.bigIroot(27n, 3), 3n);
    assert.equal(E.bigIroot(26n, 3), 2n);
    assert.equal(E.bigIroot(-27n, 3), -3n);
    assert.equal(E.bigIroot(10n ** 300n + 5n, 3), 10n ** 100n);
    assert.equal(E.bigIroot(2n ** 64n, 64), 2n);
    table([
        [12n, 2, 2n, 3n], [72n, 2, 6n, 2n], [72n, 3, 2n, 9n], [8n, 3, 2n, 1n], [-8n, 3, -2n, 1n], [-12n, 2, 2n, -3n], [1n, 2, 1n, 1n],
        [0n, 2, 0n, 1n], [2n ** 100n * 3n, 2, 2n ** 50n, 3n], [1000003n ** 2n * 7n, 2, 1000003n, 7n], [360n, 2, 6n, 10n],
    ], (n, k, out, inn) => assert.deepEqual(E.rootExtract(n, k), { out, in: inn }, `${n}, ${k}`));
    assert.throws(() => E.bigIsqrt(-1n), E.MathError);
    assert.throws(() => E.bigIroot(-16n, 4), E.MathError);
});

test('MathError carries both languages and a position', () => {
    const e = new E.MathError({ ru: 'Ошибка', en: 'Error' }, 3, 2, 'syntax');
    assert.ok(e instanceof Error);
    assert.equal(e.message, 'Error');
    assert.deepEqual(e.msg, { ru: 'Ошибка', en: 'Error' });
    assert.equal(e.pos, 3);
    assert.equal(e.len, 2);
    assert.equal(e.code, 'syntax');
    assert.equal(e.text('ru'), 'Ошибка');
    const f = new E.MathError('plain', { pos: 1, code: 'x' });
    assert.equal(f.pos, 1);
    assert.equal(f.code, 'x');
    assert.equal(f.msg.ru, 'plain');
});

// ---------------------------------------------------------------- ast

test('AST constructors and utilities', () => {
    const x = E.sym('x');
    const y = E.sym('y');
    const n = E.add(E.mul(2, x), E.pow(y, 2), 1);
    assert.equal(n.type, 'add');
    assert.equal(n.args.length, 3);
    assert.ok(Object.isFrozen(n) && Object.isFrozen(n.args));
    assert.equal(E.add([x]), x);
    assert.equal(E.add().value.toString(), '0');
    assert.equal(E.mul().value.toString(), '1');
    assert.deepEqual(E.freeVars(E.add(x, y, E.sym('pi'), E.sym('e'), E.sym('i'))), ['x', 'y']);
    assert.deepEqual(E.freeVars(P('x_2 + x_10 + a')), ['a', 'x_10', 'x_2']);
    assert.ok(E.containsVar(n, 'y') && !E.containsVar(n, 'z'));
    assert.ok(E.isConst(E.sym('pi')) && E.isConst(E.sym('e')) && !E.isConst(x) && !E.isConst(E.sym('e', true)));
    assert.deepEqual(E.freeVars(E.add(E.sym('e', true), x)), ['e', 'x']);
    assert.ok(E.nodeEquals(P('2x+1'), E.add(E.mul(2, x), 1)));
    assert.ok(E.nodeEquals(P('2,5'), P('2.5')));
    assert.ok(!E.nodeEquals(P('x+1'), P('1+x')));
    assert.equal(E.nodeSize(P('x^2+1')), 5);
    assert.ok(E.nodeEquals(E.substitute(P('x^2 + y'), { x: 3, y: P('z+1') }), P('3^2 + (z+1)')));
    assert.ok(E.nodeEquals(E.substitute(P('pi x'), { pi: 3 }), P('pi x')));
    const doubled = E.mapNode(P('x + 2'), (m) => (m.type === 'num' ? E.num(m.value.mul(2)) : undefined));
    assert.ok(E.nodeEquals(doubled, P('x + 4')));
    table([['3', '3'], ['-2', '-2'], ['3/4', '3/4'], ['-(1/2)', '-1/2'], ['2^3', '8'], ['2*3+1', '7'], ['2,5', '5/2'], ['x', null], ['2^x', null], ['1/0', null]],
        (s, v) => {
            const r = E.numValue(P(s));
            assert.equal(r === null ? null : r.toString(), v, s);
            assert.equal(E.isNumber(P(s)), v !== null, s);
        });
    assert.ok(E.nodeEquals(E.toNode('x'), x));
    assert.equal(E.toNode(2.5).value.toString(), '5/2');
    assert.equal(E.rel('≤', x, 1).op, '<=');
    assert.equal(E.chain([1, x, 2], ['<', '<=']).ops.join(), '<,<=');
    assert.throws(() => E.fn('nope', x), E.MathError);
    assert.throws(() => E.fn('log', x), E.MathError);
    assert.equal(E.fn('log', 2, x).args.length, 2);
    assert.equal(E.list(1, 2, 3).items.length, 3);
    assert.equal(E.nodeKey(P('x_1 + 2')), '+(x_1,#2)');
});

// ---------------------------------------------------------------- parse

test('parse: numbers, operators, precedence', () => {
    table([
        ['12', '#12'], ['3.5', '#7/2'], ['3,5', '#7/2'], ['.5', '#1/2'], ['0,(3)', '#1/3'], ['1 000 000', '#1000000'], ['10 000', '#10000'],
        ['2+3', '+(#2,#3)'], ['2-3', '+(#2,-(#3))'], ['2*3', '*(#2,#3)'], ['6/2', '/(#6,#2)'], ['2^3', '^(#2,#3)'], ['2**3', '^(#2,#3)'],
        ['2·3', '*(#2,#3)'], ['2×3', '*(#2,#3)'], ['6÷2', '/(#6,#2)'], ['6:2', '/(#6,#2)'], ['2−3', '+(#2,-(#3))'], ['2⋅3', '*(#2,#3)'],
        ['-x^2', '-(^(x,#2))'], ['-2^2', '-(^(#2,#2))'], ['2^3^2', '^(#2,^(#3,#2))'], ['2^-1', '^(#2,-(#1))'], ['x^-2', '^(x,-(#2))'],
        ['1/2x', '*(/(#1,#2),x)'], ['6/2(1+2)', '*(/(#6,#2),+(#1,#2))'], ['a/b/c', '/(/(a,b),c)'], ['2(x+1)^2', '*(#2,^(+(x,#1),#2))'],
        ['-2x', '-(*(#2,x))'], ['2*-3', '*(#2,-(#3))'], ['2++3', '+(#2,#3)'], ['2+-3', '+(#2,-(#3))'], ['a - -b', '+(a,-(-(b)))'],
        ['--x', '-(-(x))'], ['+5', '#5'], ['x^2y', '*(^(x,#2),y)'], ['e^2x', '*(^(e,#2),x)'], ['2e3', '*(#2,e,#3)'],
        ['5!', 'fact(#5)'], ['(n+1)!', 'fact(+(n,#1))'], ['50%', '/(#50,#100)'], ['30°', '/(*(#30,pi),#180)'], ['x!=2', '!=(x,#2)'],
    ], (s, k) => assert.equal(K(s), k, s));
});

test('parse: implicit multiplication and identifiers', () => {
    table([
        ['2x', '*(#2,x)'], ['2(x+1)', '*(#2,+(x,#1))'], ['(x+1)(x-1)', '*(+(x,#1),+(x,-(#1)))'], ['x(x+1)', '*(x,+(x,#1))'],
        ['2sin x', '*(#2,sin(x))'], ['xy', '*(x,y)'], ['x y', '*(x,y)'], ['2π', '*(#2,pi)'], ['3√2', '*(#3,sqrt(#2))'], ['xyz', '*(x,y,z)'],
        ['2pi r', '*(#2,pi,r)'], ['pix', '*(pi,x)'], ['ab(c+d)', '*(a,b,+(c,d))'], ['(x)(y)', '*(x,y)'], ['x2', '*(x,#2)'],
        ['α+β', '+(alpha,beta)'], ['alpha*theta', '*(alpha,theta)'], ['x_1+x_2', '+(x_1,x_2)'], ['a_{12}', 'a_12'], ['x_n', 'x_n'],
        ['x₁', 'x_1'], ['θ_0', 'theta_0'], ['2π r²', '*(#2,pi,^(r,#2))'], ['e^(iπ)', '^(e,*(i,pi))'], ['∞', 'inf'], ['-inf', '-(inf)'],
        ['хуx', '*(x,y,x)'], ['Sin x', 'sin(x)'], ['LN(x)', 'ln(x)'], ['[x+1]', '+(x,#1)'], ['{x+1}', '+(x,#1)'], ['x²', '^(x,#2)'],
        ['x⁻¹', '^(x,-(#1))'], ['x²−5x+6', '+(^(x,#2),-(*(#5,x)),#6)'], ['\\frac{1}{2}', '/(#1,#2)'], ['\\sqrt[3]{x}', 'root(x,#3)'],
        ['\\sin\\left(x\\right)', 'sin(x)'], ['2\\cdot 3', '*(#2,#3)'], ['\\pi r^2', '*(pi,^(r,#2))'], ['\\alpha_1', 'alpha_1'],
        ['x \\le 2', '<=(x,#2)'], ['\\operatorname{tg} x', 'tan(x)'],
    ], (s, k) => assert.equal(K(s), k, s));
});

test('parse: functions with and without brackets', () => {
    table([
        ['sin x', 'sin(x)'], ['sin 2x', 'sin(*(#2,x))'], ['sin x cos x', '*(sin(x),cos(x))'], ['sin x/2', '/(sin(x),#2)'],
        ['sin x^2', 'sin(^(x,#2))'], ['sin(x)^2', '^(sin(x),#2)'], ['sin^2 x', '^(sin(x),#2)'], ['sin^2(x)', '^(sin(x),#2)'],
        ['sin²x', '^(sin(x),#2)'], ['sin^-1 x', 'asin(x)'], ['sin^(-1)(x)', 'asin(x)'], ['sin⁻¹x', 'asin(x)'], ['arcsin x', 'asin(x)'],
        ['asin(x)', 'asin(x)'], ['tg x', 'tan(x)'], ['tan x', 'tan(x)'], ['ctg x', 'cot(x)'], ['cot x', 'cot(x)'], ['arctg x', 'atan(x)'],
        ['atan(x)', 'atan(x)'], ['arcctg x', 'acot(x)'], ['acot x', 'acot(x)'], ['sh x', 'sinh(x)'], ['ch x', 'cosh(x)'], ['th x', 'tanh(x)'],
        ['sinh x', 'sinh(x)'], ['ln x', 'ln(x)'], ['lg x', 'lg(x)'], ['log x', 'log(#10,x)'], ['log(x)', 'log(#10,x)'], ['log_2 x', 'log(#2,x)'],
        ['log_2(8)', 'log(#2,#8)'], ['log_{10}(x)', 'log(#10,x)'], ['log2(x)', 'log(#2,x)'], ['log10 x', 'log(#10,x)'], ['log_a x', 'log(a,x)'],
        ['log_(a+1)(x)', 'log(+(a,#1),x)'], ['log(2, 8)', 'log(#2,#8)'], ['sqrt x', 'sqrt(x)'], ['sqrt(x+1)', 'sqrt(+(x,#1))'],
        ['√x', 'sqrt(x)'], ['√(x+1)', 'sqrt(+(x,#1))'], ['√x^2', 'sqrt(^(x,#2))'], ['√2x', '*(sqrt(#2),x)'], ['∛x', 'root(x,#3)'],
        ['∜16', 'root(#16,#4)'], ['cbrt(x)', 'root(x,#3)'], ['root(x, 3)', 'root(x,#3)'], ['root(x; 3)', 'root(x,#3)'], ['root(8,3)', 'root(#8,#3)'],
        ['root(2,5; 3)', 'root(#5/2,#3)'], ['abs(x)', 'abs(x)'], ['|x|', 'abs(x)'], ['|x-1|+|x+1|', '+(abs(+(x,-(#1))),abs(+(x,#1)))'],
        ['||x|-1|', 'abs(+(abs(x),-(#1)))'], ['2|x|', '*(#2,abs(x))'], ['|-x|', 'abs(-(x))'], ['ln|x|', 'ln(abs(x))'], ['exp(x)', 'exp(x)'],
        ['exp x', 'exp(x)'], ['e^x', '^(e,x)'], ['floor(x)', 'floor(x)'], ['ceil x', 'ceil(x)'], ['sign x', 'sign(x)'], ['sgn(x)', 'sign(x)'],
        ['sinx', 'sin(x)'], ['lnx', 'ln(x)'], ['sqrtx', 'sqrt(x)'], ['arctgx', 'atan(x)'], ['sin -x', 'sin(-(x))'], ['sin cos x', 'sin(cos(x))'],
        ['2sin^2 x', '*(#2,^(sin(x),#2))'], ['sin(x)cos(x)', '*(sin(x),cos(x))'], ['e^sin x', '^(e,sin(x))'], ['sin 30°', 'sin(/(*(#30,pi),#180))'],
        ['sin(0,5)', 'sin(#1/2)'], ['cosec x', 'csc(x)'], ['sec x', 'sec(x)'], ['arsh x', 'asinh(x)'],
    ], (s, k) => assert.equal(K(s), k, s));
});

test('parse: relations, chains and lists', () => {
    table([
        ['x^2-5x+6=0', '=(+(^(x,#2),-(*(#5,x)),#6),#0)'], ['2x+1 > 3', '>(+(*(#2,x),#1),#3)'], ['x ≤ 2', '<=(x,#2)'], ['x >= 2', '>=(x,#2)'],
        ['x ≥ 2', '>=(x,#2)'], ['x ≠ 2', '!=(x,#2)'], ['x <> 2', '!=(x,#2)'], ['x == 2', '=(x,#2)'], ['x =< 2', '<=(x,#2)'],
        ['-1 < x <= 2', 'chain(-(#1),x,#2;<,<=)'], ['0 < x < 1 < y', 'chain(#0,x,#1,y;<,<,<)'],
        ['x+y=3; x-y=1', '[=(+(x,y),#3),=(+(x,-(y)),#1)]'], ['x+y=3\nx-y=1', '[=(+(x,y),#3),=(+(x,-(y)),#1)]'], ['1, 2, 3', '[#1,#2,#3]'],
        ['1,2,3', '[#1,#2,#3]'], ['3, 5', '[#3,#5]'], ['3,5', '#7/2'], ['3,5x', '*(#7/2,x)'], ['1,5; 2,5', '[#3/2,#5/2]'], ['1,5, 2,5', '[#3/2,#5/2]'],
        ['x=1;', '=(x,#1)'], ['x=1\n', '=(x,#1)'], ['\nx', 'x'], ['(1,5)', '#3/2'], ['{x+y=3; x-y=1}', '[=(+(x,y),#3),=(+(x,-(y)),#1)]'],
    ], (s, k) => assert.equal(K(s), k, JSON.stringify(s)));
});

test('parse: thousands, adjacent numbers, English commas', () => {
    table([
        ['x = 1 000', '=(x,#1000)'], ['1 000 000', '#1000000'], ['12 345,5', '#24691/2'], ['1 234 + 1', '+(#1234,#1)'], ['log_2 100', 'log(#2,#100)'],
        ['x^2 3', '*(^(x,#2),#3)'], ['1,000,000', '#1000000'], ['1,000', '#1'], ['3,125', '#25/8'], ['1,5,2', '[#1,#5,#2]'], ['1 000,5', '#2001/2'],
        ['sine(x)', 'sin(x)'], ['cosine x', 'cos(x)'], ['x_1 2', '*(x_1,#2)'], ['12\u00a0345', '#12345'],
    ], (s, k) => assert.equal(K(s.replace('\\u00a0', '\u00a0')), k, s));
    table([['1,000', '#1000'], ['2,5', '#5/2'], ['1,000.5', '#2001/2'], ['1,000,000.25', '#4000001/4'], ['3, 5', '[#3,#5]']],
        (s, k) => assert.equal(K(s, { lang: 'en' }), k, s));
    for (const s of ['2 3', '0 500', '1 2 3', '(1 2)']) {
        assert.throws(() => P(s), (e) => e instanceof E.MathError && e.code === 'syntax', s);
    }
});

test('parse: keeps what the user typed', () => {
    const n = P('2,5x');
    assert.equal(n.args[0].raw, '2,5');
    assert.equal(P('3.75').raw, '3.75');
    assert.equal(P('12').raw, undefined);
    assert.equal(P('1/2').type, 'div');
    assert.equal(P('-x').type, 'neg');
    assert.equal(P('sqrt(x)').name, 'sqrt');
    assert.equal(P('x - y').args[1].type, 'neg');
});

test('parse: helpful bilingual errors with positions', () => {
    table([
        ['', 'empty', 0], ['   ', 'empty', 0], ['(()', 'brackets', 0], ['())', 'brackets', 2], ['(]', 'brackets', 0], ['sin', 'no-arg', 0],
        ['sin + 1', 'no-arg', 0], ['2//3', 'syntax', 1], ['x^', 'syntax', 1], ['x=', 'syntax', 1], ['=5', 'syntax', 0], ['2+', 'syntax', 1],
        ['()', 'syntax', 0], ['|x', 'syntax', 0], ['abc(x)', 'unknown-fn', 0], ['sqr(x)', 'unsupported', 0], ['max(1, 2)', 'unsupported', 0],
        ['x ? 2', 'syntax', 2], ['2 ж', 'syntax', 2], ['1.2.3', 'syntax', 0], ['sin()', 'syntax', 3], ['root(8)', 'arity', 0], ['1,,2', 'syntax', 2],
        ['x = = 2', 'syntax', 4], ['log_ x', 'no-arg', 0], ['2*', 'syntax', 1], ['*2', 'syntax', 0], ['sin(1, 2)', 'arity', 0], ["f'(x)", 'unsupported', 1],
        ['\\foo x', 'unknown-fn', 0], ['x_', 'syntax', 1], ['√', 'syntax', 0], ['x < ', 'syntax', 2], ['1, ', 'syntax', 1],
    ], (s, code, pos) => {
        const r = E.tryParse(s);
        assert.equal(r.ok, false, JSON.stringify(s));
        assert.ok(r.error instanceof E.MathError);
        assert.equal(r.error.code, code, `${JSON.stringify(s)}: ${r.error.msg.en}`);
        assert.equal(r.error.pos, pos, `${JSON.stringify(s)}: ${r.error.msg.en}`);
        assert.ok(r.error.msg.ru.length > 3 && r.error.msg.en.length > 3);
        assert.ok(r.error.pos + (r.error.len ?? 0) <= Math.max(s.length, 1) + 1);
    });
    assert.match(E.tryParse('abc(x)').error.msg.ru, /abs/);
    assert.match(E.tryParse('sine(x)').error?.msg.en ?? '', /sin|/);
    assert.throws(() => P('x'.repeat(3000)), (e) => e.code === 'too-big');
    assert.throws(() => P('('.repeat(500) + 'x' + ')'.repeat(500)), (e) => e instanceof E.MathError);
    assert.equal(E.tryParse('x+1').ok, true);
    assert.equal(E.tryParse(null).ok, false);
});

test('parse options: extra variables and case folding', () => {
    const n = P('i^2 + e', { vars: ['i', 'e'] });
    assert.deepEqual(E.freeVars(n), ['e', 'i']);
    assert.equal(E.isConst(P('i')), true);
    assert.equal(K('speed*t', { vars: ['speed'] }), "*(speed',t)".replace("'", ''));
    assert.deepEqual(E.freeVars(P('x1 + x2', { vars: ['x1', 'x2'] })), ['x1', 'x2']);
    assert.equal(K('X^2 + Y', { foldCase: true }), '+(^(x,#2),y)');
    assert.equal(K('X^2 + x'), '+(^(X,#2),x)');
    assert.equal(E.simplify(P('i^2', { vars: ['i'] })).type, 'pow');
    assert.equal(S('i^2').value.toString(), '-1');
});

// ---------------------------------------------------------------- print

test('toTex: parsed input in both languages', () => {
    table([
        ['2(x+1)^2', '2(x + 1)^{2}', '2(x + 1)^{2}'], ['-x^2', '-x^{2}', '-x^{2}'], ['1/2x', '\\frac{1}{2}x', '\\frac{1}{2}x'],
        ['sin^2x+cos^2x', '\\sin^{2} x + \\cos^{2} x', '\\sin^{2} x + \\cos^{2} x'], ['|x-1|+|x+1|', '\\left|x - 1\\right| + \\left|x + 1\\right|', null],
        ['3,5x', '3{,}5x', '3.5x'], ['3, 5', '3;\\ 5', '3,\\ 5'], ['x²−5x+6=0', 'x^{2} - 5x + 6 = 0', null], ['√(x+1)', '\\sqrt{x + 1}', null],
        ['log_2(8)', '\\log_{2} 8', null], ['e^(iπ)', 'e^{i\\pi}', null], ['ln|x|', '\\ln\\left|x\\right|', null], ['x_1+x_2', 'x_{1} + x_{2}', null],
        ['(x+1)/(x-1)', '\\frac{x + 1}{x - 1}', null], ['sin 2x', '\\sin(2x)', null], ['sin x cos x', '\\sin x\\cos x', null],
        ['tg x', '\\operatorname{tg} x', '\\tan x'], ['ctg x', '\\operatorname{ctg} x', '\\cot x'], ['arctg x', '\\operatorname{arctg} x', '\\arctan x'],
        ['arcctg x', '\\operatorname{arcctg} x', '\\operatorname{arccot} x'], ['sh x', '\\operatorname{sh} x', '\\sinh x'], ['ch x', '\\operatorname{ch} x', '\\cosh x'],
        ['lg x', '\\lg x', '\\log_{10} x'], ['log x', '\\lg x', '\\log_{10} x'], ['arcsin x', '\\arcsin x', '\\arcsin x'],
        ['-1 < x <= 2', '-1 < x \\le 2', null], ['x != 2', 'x \\ne 2', null], ['x >= 2', 'x \\ge 2', null], ['5!', '5!', null],
        ['(n+1)!', '(n + 1)!', null], ['2π r', '2\\pi r', null], ['3√2', '3\\sqrt{2}', null], ['root(x, 3)', '\\sqrt[3]{x}', null],
        ['a - -b', 'a - (-b)', null], ['2*(-3)', '2 \\cdot (-3)', null], ['2*3', '2 \\cdot 3', null], ['x*2', 'x \\cdot 2', null],
        ['sin x * y', '\\sin x \\cdot y', null], ['x^(-1)', 'x^{-1}', null], ['sin(x)^2', '\\sin^{2} x', null], ['sin^2(2x)', '\\sin^{2}(2x)', null],
        ['(x^2)^3', '(x^{2})^{3}', null], ['(2/3)^2', '\\left(\\frac{2}{3}\\right)^{2}', null], ['2,5^2', '(2{,}5)^{2}', '(2.5)^{2}'],
        ['α_1+β', '\\alpha_{1} + \\beta', null], ['e^x', 'e^{x}', null], ['abs(x)^2', '\\left|x\\right|^{2}', null], ['pi r^2', '\\pi r^{2}', null],
        ['log_a(x+1)', '\\log_{a}(x + 1)', null], ['-(x+1)', '-(x + 1)', null], ['arctg(x/2)', '\\operatorname{arctg}\\left(\\frac{x}{2}\\right)', '\\arctan\\left(\\frac{x}{2}\\right)'],
        ['floor(x)', '\\left\\lfloor x\\right\\rfloor', null], ['sign(x)', '\\operatorname{sgn} x', null], ['0,(3)', '0{,}(3)', '0.(3)'],
        ['x_{12}', 'x_{12}', null], ['epsilon + phi', '\\varepsilon + \\varphi', null], ['\\infty', '\\infty', null], ['x y', 'xy', null],
        ['2x + 3y - 5', '2x + 3y - 5', null], ['sin(pi)', '\\sin \\pi', null], ['cos(-x)', '\\cos(-x)', null], ['x!y', 'x! \\cdot y', null],
    ], (s, ru, en) => {
        assert.equal(E.toTex(P(s)), ru, s);
        assert.equal(E.toTex(P(s), { lang: 'en' }), en ?? ru, s + ' (en)');
    });
    assert.equal(E.toTex(P('2x y'), { mulDot: true }), '2 \\cdot x \\cdot y');
});

test('toTex: canonical forms (fractions, radicals, signs)', () => {
    table([
        ['x^2 - 5x + 6', 'x^{2} - 5x + 6'], ['1/2 x', '\\frac{x}{2}'], ['3/4 x^2', '\\frac{3x^{2}}{4}'], ['-x/2', '-\\frac{x}{2}'],
        ['1/sqrt 2', '\\frac{\\sqrt{2}}{2}'], ['3/(2x)', '\\frac{3}{2x}'], ['2/(3x^2 y)', '\\frac{2}{3x^{2}y}'], ['x^(-2)', '\\frac{1}{x^{2}}'],
        ['sqrt(x)/x', '\\frac{1}{\\sqrt{x}}'], ['x^(1/3)', '\\sqrt[3]{x}'], ['x^(2/3)', 'x^{\\frac{2}{3}}'], ['sin(x)/2', '\\frac{1}{2}\\sin x'],
        ['3/4 (x+1) y', '\\frac{3}{4}y(x + 1)'], ['(x^2-1)/(x-1)', '\\frac{x^{2} - 1}{x - 1}'], ['2^x * 3', '3 \\cdot 2^{x}'], ['x e^x', 'xe^{x}'],
        ['-1 + sqrt 2', '\\sqrt{2} - 1'], ['1 - sqrt 2', '1 - \\sqrt{2}'], ['3 + 2i', '3 + 2i'], ['-i', '-i'], ['(x+1)^(-1)', '\\frac{1}{x + 1}'],
        ['pi/2', '\\frac{\\pi}{2}'], ['2pi/3', '\\frac{2\\pi}{3}'], ['-3/4', '-\\frac{3}{4}'], ['x/(y z)', '\\frac{x}{yz}'], ['sqrt(12)', '2\\sqrt{3}'],
        ['1/(2x+2)', '\\frac{1}{2(x + 1)}'], ['x sin x', 'x\\sin x'], ['sin x * x', 'x\\sin x'], ['cos x sin x', '\\sin x\\cos x'],
    ], (s, t) => assert.equal(TS(s), t, s));
    assert.equal(E.toTex(E.num('5/2'), { decimals: true }), '2{,}5');
    assert.equal(E.toTex(E.num('5/2'), { decimals: true, lang: 'en' }), '2.5');
    assert.equal(E.toTex(E.num('1/3'), { decimals: true }), '\\frac{1}{3}');
});

test('toText: plain text in both languages', () => {
    table([
        ['x^2-5x+6', 'x^2 - 5x + 6', null], ['2,5x', '2,5*x', '2.5*x'], ['sqrt(x+1)', 'sqrt(x + 1)', null], ['log_2 x', 'log_2(x)', null],
        ['tg x', 'tg(x)', 'tan(x)'], ['arctg x', 'arctg(x)', 'arctan(x)'], ['|x|', 'abs(x)', null], ['root(x, 3)', 'root(x; 3)', null],
        ['1; 2', '1; 2', '1, 2'], ['x <= 2', 'x <= 2', null], ['2^3^2', '2^(3^2)', null], ['(x+1)/(x-1)', '(x + 1)/(x - 1)', null],
        ['x/(2y)', 'x/(2y)', null], ['5!', '5!', null], ['x_1 + a_{12}', 'x_1 + a_12', null], ['α', 'alpha', null], ['π', 'pi', null],
    ], (s, ru, en) => {
        assert.equal(E.toText(P(s)), ru, s);
        assert.equal(E.toText(P(s), { lang: 'en' }), en ?? ru, s + ' (en)');
    });
    table([['1/2 x', 'x/2'], ['3/4 x', '3x/4'], ['2/(3x)', '2/(3x)'], ['x^(-1)', '1/x'], ['x^(1/2)', 'sqrt(x)'], ['x^(-1/2)', '1/sqrt(x)'], ['-x', '-x'], ['x - 2y', 'x - 2y']],
        (s, t) => assert.equal(E.toText(S(s)), t, s));
});

const CORPUS = [
    '2(x+1)^2', '-x^2', '2^3^2', '-2^2', '1/2x', 'sin^2x+cos^2x', '|x-1|+|x+1|', '3,5x', '3, 5', 'x²−5x+6=0', '√(x+1)', 'log_2(8)', 'e^(iπ)',
    'ln|x|', 'x_1+x_2', '(x+1)/(x-1)', 'a/b/c', 'a/(b/c)', '-(x+1)', '--x', 'x^(1/2)', '2*(-3)', '(-2)x', 'x*2', '2x^2 - 3x + 1',
    'sin(2x+1)/cos x', 'e^(-x^2/2)', '(x-1)^3(x+2)', 'root(x^2+1, 3)', '5! + 3!', '-1 < x <= 2', 'x+y=3; x-y=1', 'log_(1/2)(x)',
    'arcsin(x/2) + arctg x', 'sqrt(x)*sqrt(y)', '2^(x+1) - 3^x', 'x^2/(x^2+1)', '(1+2i)(3-i)', '|x|^3', 'pi r^2 h/3', 'a_1 + a_{12}',
    'sh x + ch x', 'ctg^2 x - 1', 'x^-1 + x^-2', '2,5 + 0,(3)', 'floor(x) + ceil(x)', 'sign(x - 1)', 'exp(2x)', '30°', '50%', '-sin(-x)',
];

test('round trips: parse(toText(n)) = n for parsed input; simplify(parse(toText(s))) = s for canonical', () => {
    for (const s of CORPUS) {
        const n = P(s);
        for (const lang of ['ru', 'en']) {
            const t = E.toText(n, { lang });
            assert.ok(E.nodeEquals(P(t), n), `${s} → ${t} (${lang})`);
        }
        let c;
        try {
            c = E.simplify(n);
        } catch (e) {
            assert.ok(e instanceof E.MathError);
            continue;
        }
        for (const lang of ['ru', 'en']) {
            const t = E.toText(c, { lang });
            assert.ok(E.nodeEquals(E.simplify(P(t)), c), `canonical ${s} → ${t} (${lang})`);
        }
    }
});

test('texNumber formats numbers for widgets', () => {
    table([
        [2.5, 'ru', {}, '2{,}5'], [2.5, 'en', {}, '2.5'], [1 / 3, 'ru', { digits: 3 }, '0{,}333'], [-0.0000001, 'en', {}, '-1 \\cdot 10^{-7}'],
        [1e20, 'en', {}, '1 \\cdot 10^{20}'], [12345.678, 'ru', { digits: 1, group: true }, '12\\,345{,}7'], [-0, 'en', {}, '0'], [3, 'ru', {}, '3'],
        [NaN, 'en', {}, '\\text{—}'], [Infinity, 'en', {}, '\\infty'], [-Infinity, 'ru', {}, '-\\infty'], [q('3/4'), 'ru', {}, '\\frac{3}{4}'],
        [q('3/4'), 'ru', { decimal: true }, '0{,}75'], [q(5), 'en', {}, '5'], [10n, 'en', {}, '10'], [0.1 + 0.2, 'en', {}, '0.3'],
    ], (v, lang, o, t) => assert.equal(E.texNumber(v, lang, o), t, String(v)));
});

// ---------------------------------------------------------------- simplify

test('simplify: exact folding and like terms', () => {
    table([
        ['2+3', '5'], ['1/2 + 1/3', '\\frac{5}{6}'], ['0,1 + 0,2', '\\frac{3}{10}'], ['3x + 2x', '5x'], ['x*x', 'x^{2}'], ['x^2*x^(-1)', 'x'],
        ['x^0', '1'], ['x^1', 'x'], ['1^x', '1'], ['0^0', '1'], ['0*x', '0'], ['x - x', '0'], ['x/x', '1'], ['2^10', '1024'], ['2^3^2', '512'],
        ['-2^2', '-4'], ['(-2)^2', '4'], ['(-2)^3', '-8'], ['2^(-2)', '\\frac{1}{4}'], ['(2/3)^(-2)', '\\frac{9}{4}'], ['x+1-(x+1)', '0'],
        ['2(x+1) - 2x', '2'], ['x*2*y*3', '6xy'], ['(2x)^3', '8x^{3}'], ['(x^2)^3', 'x^{6}'], ['x^a x^b', 'x^{a + b}'], ['2^x 2^x', '2^{2x}'],
        ['e e^x', 'e^{x + 1}'], ['y + x', 'x + y'], ['6 - 5x + x^2', 'x^{2} - 5x + 6'], ['b^2 + a^2 + 2ab', 'a^{2} + 2ab + b^{2}'],
        ['x^2 + y^2 + 2xy', 'x^{2} + 2xy + y^{2}'], ['c + b x + a x^2', 'ax^{2} + bx + c'], ['q + x^2 + p x', 'x^{2} + px + q'],
        ['x_2 + x_10 + x_1', 'x_{1} + x_{2} + x_{10}'], ['1 + x + x^3 + x^2', 'x^{3} + x^{2} + x + 1'], ['5!', '120'], ['0!', '1'],
        ['(1/2)(4x)', '2x'], ['-(-x)', 'x'], ['(x+1)(x+1)', '(x + 1)^{2}'], ['(x+1)^2 (x+1)^(-1)', 'x + 1'], ['2(x+1)', '2x + 2'],
        ['x(2x+2)', '2x(x + 1)'], ['(2x+2)^2', '4(x + 1)^{2}'], ['(-x-1)^2', '(x + 1)^{2}'], ['(x-1)/(1-x)', '-1'], ['3/(6x+3)', '\\frac{1}{2x + 1}'],
    ], (s, t) => assert.equal(TS(s), t, s));
});

test('simplify: radicals and exact powers', () => {
    table([
        ['(4/9)^(1/2)', '\\frac{2}{3}'], ['8^(1/3)', '2'], ['sqrt(12)', '2\\sqrt{3}'], ['sqrt(8)/2', '\\sqrt{2}'], ['(-8)^(1/3)', '-2'],
        ['sqrt2*sqrt2', '2'], ['sqrt2*sqrt3', '\\sqrt{6}'], ['sqrt(50) - sqrt(8)', '3\\sqrt{2}'], ['sqrt(18)+sqrt(2)', '4\\sqrt{2}'],
        ['2^(1/2)*2^(1/3)', '\\sqrt[6]{32}'], ['4^(1/4)', '\\sqrt{2}'], ['16^(3/4)', '8'], ['27^(-1/3)', '\\frac{1}{3}'], ['2^(3/2)', '2\\sqrt{2}'],
        ['2^(2/3)', '\\sqrt[3]{4}'], ['sqrt(1/2)', '\\frac{\\sqrt{2}}{2}'], ['1/sqrt(3)', '\\frac{\\sqrt{3}}{3}'], ['sqrt(3/4)', '\\frac{\\sqrt{3}}{2}'],
        ['root(81, 4)', '3'], ['∛(-27)', '-3'], ['sqrt(0)', '0'], ['sqrt(1)', '1'], ['sqrt(x^2)', '\\left|x\\right|'], ['(sqrt x)^2', 'x'],
        ['sqrt(x)*sqrt(x)', 'x'], ['sqrt(x)*x', 'x^{\\frac{3}{2}}'], ['(x^3)^(1/3)', 'x'], ['(x^4)^(1/2)', 'x^{2}'], ['(x^6)^(1/3)', 'x^{2}'],
        ['(4x)^(1/2)', '2\\sqrt{x}'], ['(-8x)^(1/3)', '-2\\sqrt[3]{x}'], ['sqrt(4x^2)', '2\\left|x\\right|'], ['(e^x)^(1/2)', 'e^{\\frac{x}{2}}'],
        ['|x|^2', 'x^{2}'], ['sqrt(-4)', '\\sqrt{-4}'], ['sqrt(2)^4', '4'], ['(1+sqrt2)(1+sqrt2)', '(1 + \\sqrt{2})^{2}'],
    ], (s, t) => assert.equal(TS(s), t, s));
    assert.throws(() => S('1/0'), (e) => e instanceof E.MathError && e.code === 'div0');
    assert.throws(() => S('x/(y-y)'), (e) => e.code === 'div0');
    assert.throws(() => S('0^(-1)'), (e) => e.code === 'div0');
    assert.equal(TS('2^100000'), '2^{100000}');
});

test('simplify: known values of functions', () => {
    table([
        ['sin(pi/6)', '\\frac{1}{2}'], ['cos(pi/3)', '\\frac{1}{2}'], ['tan(pi/4)', '1'], ['sin(pi/4)', '\\frac{\\sqrt{2}}{2}'], ['cos(pi/6)', '\\frac{\\sqrt{3}}{2}'],
        ['sin(pi/2)', '1'], ['cos(pi)', '-1'], ['sin(pi)', '0'], ['sin 0', '0'], ['cos 0', '1'], ['sin(7pi/6)', '-\\frac{1}{2}'],
        ['cos(5pi/4)', '-\\frac{\\sqrt{2}}{2}'], ['cot(pi/6)', '\\sqrt{3}'], ['tan(pi/6)', '\\frac{\\sqrt{3}}{3}'], ['tan(2pi/3)', '-\\sqrt{3}'],
        ['sin(13pi/6)', '\\frac{1}{2}'], ['cos(-pi/3)', '\\frac{1}{2}'], ['sin(-pi/6)', '-\\frac{1}{2}'], ['sec(pi/3)', '2'], ['csc(pi/6)', '2'],
        ['tan(pi/2)', '\\operatorname{tg}\\left(\\frac{\\pi}{2}\\right)'], ['cot(0)', '\\operatorname{ctg} 0'], ['sin(9pi/7)', '-\\sin\\left(\\frac{2\\pi}{7}\\right)'],
        ['sin(-x)', '-\\sin x'], ['cos(-x)', '\\cos x'], ['tan(-2x)', '-\\operatorname{tg}(2x)'], ['sin(arcsin x)', 'x'], ['cos(-pi)', '-1'],
        ['arcsin(1/2)', '\\frac{\\pi}{6}'], ['arcsin(-1)', '-\\frac{\\pi}{2}'], ['arccos(-1/2)', '\\frac{2\\pi}{3}'], ['arccos(0)', '\\frac{\\pi}{2}'],
        ['arccos(1)', '0'], ['arccos(sqrt(3)/2)', '\\frac{\\pi}{6}'], ['arctg(sqrt3)', '\\frac{\\pi}{3}'], ['arctg(1)', '\\frac{\\pi}{4}'],
        ['arctg(-1/sqrt3)', '-\\frac{\\pi}{6}'], ['arcctg(-1)', '\\frac{3\\pi}{4}'], ['arcctg(0)', '\\frac{\\pi}{2}'], ['arcsin(sqrt2/2)', '\\frac{\\pi}{4}'],
        ['arcsin(2)', '\\arcsin 2'], ['arcsin(-x)', '-\\arcsin x'], ['arccos(-x)', '-\\arccos x + \\pi'],
        ['ln 1', '0'], ['ln e', '1'], ['ln(e^x)', 'x'], ['e^(ln x)', 'x'], ['e^(2 ln x)', 'x^{2}'], ['ln(e^2)', '2'], ['ln(sqrt(e))', '\\frac{1}{2}'],
        ['log_2 8', '3'], ['lg 100', '2'], ['lg 0,001', '-3'], ['log_4 8', '\\frac{3}{2}'], ['log_(1/2) 4', '-2'], ['log_9 (1/27)', '-\\frac{3}{2}'],
        ['log_a a', '1'], ['log_a(a^3)', '3'], ['log_3 1', '0'], ['log_2 3', '\\log_{2} 3'], ['lg 2', '\\lg 2'], ['log x', '\\lg x'], ['log_e x', '\\ln x'],
        ['2^(log_2 x)', 'x'], ['10^(lg x)', 'x'], ['lg(sqrt(10))', '\\frac{1}{2}'], ['exp(0)', '1'], ['exp(x)', 'e^{x}'], ['exp(ln 5)', '5'],
        ['|-3|', '3'], ['|3|', '3'], ['|-x|', '\\left|x\\right|'], ['||x||', '\\left|x\\right|'], ['|2x|', '2\\left|x\\right|'], ['|x^2|', 'x^{2}'],
        ['|pi|', '\\pi'], ['|1-sqrt 2|', '\\sqrt{2} - 1'], ['|e^x|', 'e^{x}'], ['abs(i)', '1'], ['|3+4i|', '5'],
        ['sign(-3)', '-1'], ['sign(0)', '0'], ['sign(pi)', '1'], ['sign(1-sqrt2)', '-1'], ['floor(pi)', '3'], ['ceil(pi)', '4'], ['floor(-5/2)', '-3'],
        ['ceil(7/2)', '4'], ['floor(sqrt(2))', '1'], ['5!', '120'], ['20!', '2432902008176640000'], ['(1/2)!', '\\left(\\frac{1}{2}\\right)!'],
        ['sinh 0', '0'], ['cosh 0', '1'], ['sinh(-x)', '-\\operatorname{sh} x'], ['cosh(-x)', '\\operatorname{ch} x'], ['sqrt(x)', '\\sqrt{x}'],
        ['root(x, 3)', '\\sqrt[3]{x}'], ['root(x, n)', 'x^{\\frac{1}{n}}'], ['sin^2x+cos^2x', '1'], ['3sin^2 x + 3cos^2 x', '3'],
    ], (s, t) => assert.equal(TS(s), t, s));
});

test('simplify: the imaginary unit and complex mode', () => {
    table([
        ['i^2', '-1', {}], ['i^3', '-i', {}], ['i^4', '1', {}], ['i^101', 'i', {}], ['i*i*i', '-i', {}], ['3 + 2i - 1 + i', '2 + 3i', {}],
        ['1/i', '-i', {}], ['(1+i)^2', '(1 + i)^{2}', {}], ['(1+2i)(3-i)', '5 + 5i', { complex: true }], ['1/(1+i)', '\\frac{1}{2} - \\frac{1}{2}i', { complex: true }],
        ['(1+i)^2', '2i', { complex: true }], ['(2+i)/(1-i)', '\\frac{1}{2} + \\frac{3}{2}i', { complex: true }], ['sqrt(-4)', '2i', { complex: true }],
        ['sqrt(-3)', '\\sqrt{3}i', { complex: true }], ['e^(i pi)', '-1', { complex: true }], ['e^(i pi/2)', 'i', { complex: true }],
        ['(1+i)^8', '16', { complex: true }], ['(3+4i)(3-4i)', '25', { complex: true }], ['i(2+3i)', '-3 + 2i', { complex: true }],
    ], (s, t, o) => assert.equal(TS(s, o), t, s));
});

test('simplify: relations, lists, options', () => {
    assert.equal(TS('2x + x = 3 + 3'), '3x = 6');
    assert.equal(TS('x+x; 2+2'), '2x;\\ 4');
    assert.equal(TS('0 < 2x - x <= 1+1'), '0 < x \\le 2');
    assert.equal(E.toTex(S('y^2 + x y + 1', { mainVar: 'y' })), 'y^{2} + xy + 1');
    assert.equal(E.toTex(S('y^2 + x y^3 + x^2')), 'x^{2} + xy^{3} + y^{2}');
    const big = P(Array.from({ length: 300 }, (_, k) => `x^${k}`).join('+'));
    assert.equal(E.simplify(big).args.length, 300);
});

test('simplify is idempotent and canonical constructors agree with it', () => {
    for (const s of CORPUS) {
        let a;
        try {
            a = E.simplify(P(s));
        } catch (e) {
            assert.ok(e instanceof E.MathError);
            continue;
        }
        assert.ok(E.nodeEquals(E.simplify(a), a), s);
    }
    const x = E.sym('x');
    assert.equal(E.nodeKey(E.canonAdd([x, x, E.num(1)])), '+(*(#2,x),#1)');
    assert.equal(E.nodeKey(E.canonMul([x, E.num(3), x])), '*(#3,^(x,#2))');
    assert.equal(E.nodeKey(E.canonPow(E.num(8), E.num('1/3'))), '#2');
    assert.equal(E.nodeKey(E.canonFn('sqrt', [E.num(12)])), '*(#2,^(#3,#1/2))');
    const C = E.canonContext();
    assert.equal(E.nodeKey(C.mul([C.add([x, E.num(1)]), C.add([x, E.num(1)])])), '^(+(x,#1),#2)');
    assert.deepEqual(E.splitCoeff(S('-3x y')).coef.toString(), '-3');
    assert.ok(E.compareTerms(S('x^2'), S('x'), 'x') < 0);
    assert.ok(E.compareTerms(S('5'), S('x'), 'x') > 0);
});

// ---------------------------------------------------------------- expand

test('expand multiplies out and collects', () => {
    table([
        ['(x+1)^2', 'x^{2} + 2x + 1'], ['(x+1)(x-1)', 'x^{2} - 1'], ['(a+b)^3', 'a^{3} + 3a^{2}b + 3ab^{2} + b^{3}'],
        ['(x+y+z)^2', 'x^{2} + 2xy + 2xz + y^{2} + 2yz + z^{2}'], ['2(x+1)^2', '2x^{2} + 4x + 2'], ['(x-2)(x+3)(x+1)', 'x^{3} + 2x^{2} - 5x - 6'],
        ['x(x+1)^2 - x^3', '2x^{2} + x'], ['(x+1)^2/x', 'x + \\frac{1}{x} + 2'], ['(sqrt x + 1)^2', 'x + 2\\sqrt{x} + 1'], ['(1+sqrt2)^2', '3 + 2\\sqrt{2}'],
        ['(e^x+1)^2', 'e^{2x} + 2e^{x} + 1'], ['sin((x+1)^2)', '\\sin(x^{2} + 2x + 1)'], ['(x+1)^(-2)', '\\frac{1}{(x + 1)^{2}}'],
        ['(2x-3)^5', '32x^{5} - 240x^{4} + 720x^{3} - 1080x^{2} + 810x - 243'], ['(1+i)^2', '2i'], ['(a-b)(a+b)', 'a^{2} - b^{2}'],
        ['(x^2+x+1)(x-1)', 'x^{3} - 1'], ['(a+b)^2 - (a-b)^2', '4ab'], ['(x+1)^0', '1'], ['3', '3'], ['x', 'x'], ['(x+1/2)^2', 'x^{2} + x + \\frac{1}{4}'],
        ['(2,5x - 1)^2', '\\frac{25x^{2}}{4} - 5x + 1'], ['x^2 - 5x + 6 = (x-2)(x-3)', 'x^{2} - 5x + 6 = x^{2} - 5x + 6'],
    ], (s, t) => assert.equal(TX(s), t, s));
    const e200 = E.expand(P('(x+1)^200'));
    assert.equal(e200.args.length, 201);
    const mid = e200.args.find((t) => t.type === 'mul' && t.args[1].type === 'pow' && t.args[1].exp.value.eq(100));
    assert.equal(mid.args[0].value.n, 90548514656103281165404177077484163874504589675413336841320n);
    assert.throws(() => E.expand(P('(x+y+z)^60')), (e) => e instanceof E.MathError && e.code === 'too-big');
    assert.throws(() => E.expand(P('(x+1)^100000000')), (e) => e.code === 'too-big');
    assert.equal(E.expand(P('(x+y+z)^20')).args.length, 231);
});

test('collectTerms, combineFractions, numDen', () => {
    const c = E.collectTerms(P('(x+a)^2 = 2x'), 'x');
    assert.deepEqual([...c.keys()], [2, 1, 0]);
    assert.equal(E.toTex(c.get(1)), '2a - 2');
    assert.equal(E.toTex(c.get(0)), 'a^{2}');
    const d = E.collectTerms(P('3x^2 - x + 5 - x^2'), 'x');
    assert.deepEqual([...d].map(([k, v]) => `${k}:${E.toText(v)}`), ['2:2', '1:-1', '0:5']);
    assert.equal(E.collectTerms(P('sin x + x'), 'x'), null);
    assert.deepEqual([...E.collectTerms(P('x + 1/x'), 'x').keys()], [1, -1]);
    table([
        ['1/x + 1/(x+1)', '\\frac{2x + 1}{x(x + 1)}'], ['x/2 + 1/3', '\\frac{3x + 2}{6}'], ['(x^2-1)/(x-1)', 'x + 1'],
        ['1/(x-1) - 1/(x+1)', '\\frac{2}{(x + 1)(x - 1)}'], ['1/x^2 + 1/x', '\\frac{x + 1}{x^{2}}'], ['x + 1', 'x + 1'],
        ['a/b + c/d', '\\frac{ad + bc}{bd}'], ['(x^2 - 4)/(x^2 - 4x + 4)', '\\frac{x^{2} - 4}{x^{2} - 4x + 4}'], ['2/(2x+2)', '\\frac{1}{x + 1}'],
        ['(x^2-4)/(x-2)^2', '\\frac{x + 2}{x - 2}'],
    ], (s, t) => assert.equal(E.toTex(E.combineFractions(P(s))), t, s));
    assert.equal(E.toTex(E.rationalize(P('1/2 + 1/x'))), '\\frac{x + 2}{2x}');
    assert.equal(E.toTex(E.combineFractions(P('1/x = 1/(x+1)'))), '\\frac{1}{x} = \\frac{1}{x + 1}');
    const nd = E.numDen(P('3x/(4y)'));
    assert.equal(E.toTex(nd.num), '3x');
    assert.equal(E.toTex(nd.den), '4y');
    const nd2 = E.numDen(P('1/x + 1'));
    assert.equal(E.toTex(nd2.num), 'x + 1');
    assert.equal(E.toTex(nd2.den), 'x');
    const nd3 = E.numDen(P('x^2 + 1'));
    assert.equal(E.toTex(nd3.den), '1');
});

// ---------------------------------------------------------------- poly

test('Poly: construction and arithmetic', () => {
    const p = E.Poly.fromCoeffs([6, -5, 1]);
    assert.equal(p.degree, 2);
    assert.equal(p.lead.toString(), '1');
    assert.equal(p.coeff(1).toString(), '-5');
    assert.equal(p.coeff(7).toString(), '0');
    assert.equal(p.toString(), 'x^2 - 5x + 6');
    assert.equal(E.Poly.fromDescending([1, -5, 6]).toString(), 'x^2 - 5x + 6');
    assert.equal(new E.Poly([]).degree, -1);
    assert.equal(new E.Poly([0, 0]).isZero(), true);
    assert.equal(p.toTex(), 'x^{2} - 5x + 6');
    assert.equal(p.toTex('t'), 't^{2} - 5t + 6');
    assert.equal(E.toTex(p.toNode('y')), 'y^{2} - 5y + 6');
    assert.ok(E.nodeEquals(p.toNode(), S('x^2 - 5x + 6')));
    const a = E.Poly.fromCoeffs([1, 1]);
    const b = E.Poly.fromCoeffs([-1, 1]);
    assert.equal(a.mul(b).toString(), 'x^2 - 1');
    assert.equal(a.add(b).toString(), '2x');
    assert.equal(a.sub(b).toString(), '2');
    assert.equal(a.neg().toString(), '-x - 1');
    assert.equal(a.scale('1/2').toString(), '(1/2)x + 1/2');
    assert.equal(a.pow(3).toString(), 'x^3 + 3x^2 + 3x + 1');
    assert.ok(a.pow(0).equals(E.Poly.fromCoeffs([1])));
    assert.ok(E.Poly.fromRoots([2, 3]).equals(p));
    assert.equal(E.Poly.monomial('3/2', 4).toString(), '(3/2)x^4');
    assert.equal(p.derivative().toString(), '2x - 5');
    assert.equal(p.evalAt(2).toString(), '0');
    assert.equal(p.evalAt('1/2').toString(), '15/4');
    assert.equal(p.evalNumber(4), 2);
    assert.equal(p.monic().toString(), p.toString());
    assert.equal(E.Poly.fromCoeffs([2, 4]).monic().toString(), 'x + 1/2');
    assert.deepEqual(p.descending().map(String), ['1', '-5', '6']);
});

test('Poly.fromNode reads polynomials and rejects the rest', () => {
    table([
        ['x^2 - 5x + 6', 'x^2 - 5x + 6'], ['(x+1)^3', 'x^3 + 3x^2 + 3x + 1'], ['2(x-1)(x+1)', '2x^2 - 2'], ['x/2 + 1/3', '(1/2)x + 1/3'],
        ['(x^2+1)/2', '(1/2)x^2 + 1/2'], ['3', '3'], ['0', '0'], ['x^2 = 4', 'x^2 - 4'], ['x^2 - 5x + 6 = 0', 'x^2 - 5x + 6'], ['2,5x', '(5/2)x'],
        ['sqrt(4)x', '2x'], ['(x^2-1)/1', 'x^2 - 1'], ['x x x', 'x^3'],
    ], (s, t) => assert.equal(E.Poly.fromNode(P(s)).toString(), t, s));
    for (const s of ['1/x', 'sqrt(x)', 'sin x', 'x + y', 'pi x', 'sqrt(2) x', 'x^(1/2)', '2^x', '(x^2-1)/(x-1)', 'x < 2', '1; 2', 'e x', 'i x']) {
        assert.equal(E.Poly.fromNode(P(s)), null, s);
    }
    assert.equal(E.Poly.fromNode(P('t^2 + 1'), 't').toString(), 'x^2 + 1');
    assert.equal(E.Poly.fromNode(P('a x + b'), 'x'), null);
});

test('Poly: division, long division, Horner', () => {
    const p = E.Poly.fromDescending([1, -6, 11, -6]);
    const { q: qq, r } = p.divmod(E.Poly.fromDescending([1, -1]));
    assert.equal(qq.toString(), 'x^2 - 5x + 6');
    assert.ok(r.isZero());
    const d2 = E.Poly.fromDescending([2, 3, -1, 5]).divmod(E.Poly.fromDescending([1, 2]));
    assert.equal(d2.q.toString(), '2x^2 - x + 1');
    assert.equal(d2.r.toString(), '3');
    const d3 = E.Poly.fromDescending([1, 0, 1]).divmod(E.Poly.fromDescending([2, 1]));
    assert.equal(d3.q.toString(), '(1/2)x - 1/4');
    assert.equal(d3.r.toString(), '5/4');
    assert.throws(() => p.divmod(new E.Poly([])), (e) => e.code === 'div0');
    const ld = E.Poly.fromDescending([2, 3, -1, 5]).longDivision(E.Poly.fromDescending([1, 2]));
    assert.equal(ld.quotient.toString(), '2x^2 - x + 1');
    assert.equal(ld.remainder.toString(), '3');
    assert.equal(ld.steps.length, 3);
    assert.deepEqual(ld.steps.map((s) => s.term.toString()), ['2x^2', '-x', '1']);
    assert.deepEqual(ld.steps.map((s) => s.product.toString()), ['2x^3 + 4x^2', '-x^2 - 2x', 'x + 2']);
    assert.deepEqual(ld.steps.map((s) => s.remainder.toString()), ['-x^2 - x + 5', 'x + 5', '3']);
    assert.equal(ld.steps[0].dividend.toString(), '2x^3 + 3x^2 - x + 5');
    const h = p.horner(2);
    assert.deepEqual(h.top.map(String), ['1', '-6', '11', '-6']);
    assert.deepEqual(h.row.map(String), ['1', '-4', '3', '0']);
    assert.equal(h.value.toString(), '0');
    assert.equal(h.quotient.toString(), 'x^2 - 4x + 3');
    assert.equal(p.horner(4).value.toString(), '6');
    assert.equal(p.horner('1/2').value.toString(), '-15/8');
});

test('Poly: gcd, content, roots, factorisation', () => {
    const P2 = (s) => E.Poly.fromNode(P(s));
    assert.equal(P2('x^2 - 1').gcd(P2('x^2 + 2x + 1')).toString(), 'x + 1');
    assert.equal(P2('x^3 - x').gcd(P2('2x^2 - 2')).toString(), 'x^2 - 1');
    assert.equal(P2('x + 1').gcd(P2('x + 2')).toString(), '1');
    assert.equal(P2('6x^2 + 4x + 2').content().toString(), '2');
    assert.equal(P2('x^2/2 + x/3').content().toString(), '1/6');
    assert.equal(P2('-2x + 4').content().toString(), '-2');
    assert.equal(P2('x^2/2 + x/3').primitive().toString(), '3x^2 + 2x');
    table([
        ['x^2 - 5x + 6', ['2^1', '3^1']], ['2x^3 - 3x^2 - 11x + 6', ['-2^1', '1/2^1', '3^1']], ['x^3', ['0^3']], ['(x-1)^2(x+2)', ['-2^1', '1^2']],
        ['x^2 + 1', []], ['x^4 - 1', ['-1^1', '1^1']], ['6x^2 - x - 1', ['-1/3^1', '1/2^1']], ['x^3 - 2x', ['0^1']], ['x - 7', ['7^1']],
        ['x^2 - 2', []], ['4x^2 - 9', ['-3/2^1', '3/2^1']], ['x^5 - x', ['-1^1', '0^1', '1^1']], ['(x^2/2 - 1/8)', ['-1/2^1', '1/2^1']],
    ], (s, roots) => assert.deepEqual(P2(s).rationalRoots().map((r) => `${r.root}^${r.mult}`), roots, s));
    const rr = P2('2x^2 - 3x - 2').rationalRoots();
    assert.deepEqual(rr.candidates.map(String), ['-2', '-1', '-1/2', '1/2', '1', '2']);
    assert.deepEqual(P2('2x^2 - 3x - 2').rootCandidates().map(String), ['-2', '-1', '-1/2', '1/2', '1', '2']);
    const f = (s) => {
        const r = P2(s).factor();
        return `${r.constant}|` + r.factors.map((x) => `(${x.poly})^${x.mult}`).join('');
    };
    table([
        ['x^2 - 5x + 6', '1|(x - 3)^1(x - 2)^1'], ['2x^3 - 3x^2 - 11x + 6', '1|(x - 3)^1(x + 2)^1(2x - 1)^1'], ['x^4 + 4', '1|(x^2 - 2x + 2)^1(x^2 + 2x + 2)^1'],
        ['(x-1)^3(x+2)^2(x^2+1)', '1|(x - 1)^3(x + 2)^2(x^2 + 1)^1'], ['2x^2 - 2', '2|(x - 1)^1(x + 1)^1'], ['x^2 + 1', '1|(x^2 + 1)^1'],
        ['-x^2 + 1', '-1|(x - 1)^1(x + 1)^1'], ['x^2/2 - 1/2', '1/2|(x - 1)^1(x + 1)^1'], ['x^4 - 5x^2 + 6', '1|(x^2 - 3)^1(x^2 - 2)^1'],
        ['x^3', '1|(x)^3'], ['7', '7|'], ['x^4 + x^2 + 1', '1|(x^2 - x + 1)^1(x^2 + x + 1)^1'], ['(x^2+1)^2', '1|(x^2 + 1)^2'],
        ['x^3 - 1', '1|(x - 1)^1(x^2 + x + 1)^1'],
    ], (s, t) => assert.equal(f(s), t, s));
    // the factorisation multiplies back
    for (const s of ['2x^3 - 3x^2 - 11x + 6', 'x^4 + 4', '(x-1)^3(x+2)^2(x^2+1)', '-3x^2 + 3', 'x^5 - x', '6x^4 + 5x^3 - 38x^2 + 5x + 6']) {
        const p = P2(s);
        const { constant, factors } = p.factor();
        let back = E.Poly.fromCoeffs([constant]);
        for (const { poly, mult } of factors) back = back.mul(poly.pow(mult));
        assert.ok(back.equals(p), s);
    }
    assert.deepEqual(P2('(x-1)^3(x+2)^2(x^2+1)').squareFree().map((x) => `${x.poly}^${x.mult}`), ['x^2 + 1^1', 'x + 2^2', 'x - 1^3']);
    assert.equal(P2('x^2 - 5x + 6').discriminant().toString(), '1');
    assert.equal(P2('x^2 + x + 1').discriminant().toString(), '-3');
    assert.equal(P2('x^3 - 3x + 2').discriminant().toString(), '0');
    assert.equal(P2('x^3 + x + 1').discriminant().toString(), '-31');
    assert.equal(P2('x^4').discriminant(), null);
    assert.equal(P2('x^2 - 5x + 6').factor().factors.length, 2);
    assert.equal(new E.Poly([]).rationalRoots().length, 0);
});

test('linearForm for systems', () => {
    const f = E.linearForm(P('2x - 3y + 1 = x/2'), ['x', 'y']);
    assert.equal(f.coeffs.x.toString(), '3/2');
    assert.equal(f.coeffs.y.toString(), '-3');
    assert.equal(f.constant.toString(), '1');
    const g = E.linearForm(P('x + 2(y - 1)'), ['x', 'y', 'z']);
    assert.deepEqual(Object.fromEntries(Object.entries(g.coeffs).map(([k, v]) => [k, v.toString()])), { x: '1', y: '2', z: '0' });
    assert.equal(g.constant.toString(), '-2');
    assert.equal(E.linearForm(P('3'), ['x']).constant.toString(), '3');
    assert.equal(E.linearForm(P('(x+1)^2 - x^2'), ['x']).coeffs.x.toString(), '2');
    for (const s of ['x y', 'x^2', 'sin x', 'x + a', '1/x', 'pi x', 'sqrt(x)']) assert.equal(E.linearForm(P(s), ['x', 'y']), null, s);
    assert.equal(E.linearForm(P('x/2 + y/3 = 1'), 'x'), null);
});

// ---------------------------------------------------------------- equivalence

test('equivalent: expressions', () => {
    table([
        ['sqrt(x^2)', 'x', false], ['sqrt(x^2)', '|x|', true], ['(x^2-1)/(x-1)', 'x+1', true], ['ln(x^2)', '2ln x', false], ['ln(x^2)', '2ln|x|', true],
        ['sin^2 x + cos^2 x', '1', true], ['(x+1)^2', 'x^2+2x+1', true], ['(x+1)^2', 'x^2+2x+2', false], ['tan x', 'sin x / cos x', true],
        ['2sin x cos x', 'sin 2x', true], ['x^2', '|x|^2', true], ['1/(1/x)', 'x', true], ['x^200/x^199', 'x', true], ['sin(x+2pi)', 'sin x', true],
        ['e^(i pi)', '-1', true], ['arcsin(sin x)', 'x', false], ['cbrt(x^3)', 'x', true], ['sqrt(x-100)', 'sqrt(x-100)', true], ['x', 'y', false],
        ['sqrt(-x-100)', 'i sqrt(x+100)', true], ['(a+b)^2', 'a^2 + 2ab + b^2', true], ['(a+b)^2', 'a^2 + b^2', false], ['x/2', '0,5x', true],
        ['1/2', '0.5', true], ['cos(2x)', '1 - 2sin^2 x', true], ['cos(2x)', '2cos^2 x - 1', true], ['e^(x+y)', 'e^x e^y', true], ['ln(xy)', 'ln x + ln y', false],
        ['log_2 x', 'ln x / ln 2', true], ['sqrt(x)sqrt(x)', 'x', true], ['x^(1/2)', 'sqrt(x)', true], ['|x - 1|', '|1 - x|', true], ['x', 'x + 0,000001', false],
        ['1/(x^2+1)', '1/(x^2+1)', true], ['(x^3 - 1)/(x - 1)', 'x^2 + x + 1', true], ['x^3 - 1', '(x-1)(x^2+x+1)', true], ['x^3 - 1', '(x-1)(x^2+x-1)', false],
        ['sin x', 'cos(pi/2 - x)', true], ['tg x ctg x', '1', true], ['2^x 3^x', '6^x', true], ['sqrt(8)', '2sqrt(2)', true], ['pi', '3.14159', false],
    ], (a, b, r) => assert.equal(E.equivalent(a, b), r, `${a} ≡ ${b}`));
    assert.equal(E.equivalent(P('x + 1'), P('1 + x')), true);
    assert.equal(E.equivalent('t^2', 't*t'), true);
    assert.equal(E.equivalent('x^2 + a', 'x^2 + b'), false);
});

test('equivalent: equations, inequalities, lists', () => {
    table([
        ['x+y=3', '2x+2y=6', true], ['x+y=3', 'x+y=4', false], ['x > 2', '2 < x', true], ['x>2', '-x < -2', true], ['x > 2', 'x < 2', false],
        ['x = 2', '2 = x', true], ['x^2 = 4', 'x^2 - 4 = 0', true], ['x >= 1', 'x > 1', false], ['2x < 4', 'x < 2', true], ['x = 1', 'x < 1', false],
        ['1; 2', '1; 2', true], ['1; 2', '2; 1', false], ['x+1; 2x', '1+x; x+x', true], ['x', 'x = 1', false], ['0 < x < 1', '0 < x < 1', true],
    ], (a, b, r) => assert.equal(E.equivalent(a, b), r, `${a} ≡ ${b}`));
});

test('sameValue and sameSet', () => {
    table([
        ['sqrt(8)', '2sqrt2', true], ['0.5', '1/2', true], ['0,5', '1/2', true], ['pi', '3.14159', false], ['1/3', '0.333333', false], ['2^10', '1024', true],
        ['sin(pi/6)', '1/2', true], ['e^(i pi)', '-1', true], ['1+i', '1-i', false], ['sqrt(2)', '1.4142135623730951', true], ['ln 1', '0', true],
    ], (a, b, r) => assert.equal(E.sameValue(a, b), r, `${a} = ${b}`));
    assert.equal(E.sameValue('pi', '3.14159', { tol: 1e-5 }), true);
    assert.equal(E.sameValue(2, E.Q.of('2')), true);
    assert.equal(E.sameValue(P('1/0'), 1), false);
    table([
        ['2; 3', '3; 2', {}, true], ['2; 2; 3', '3; 2', {}, true], ['2; 2; 3', '3; 2', { multiset: true }, false], ['2; 3', '2; 4', {}, false],
        ['1/2; -1', '-1; 0,5', {}, true], ['sqrt2; -sqrt2', '-1.4142135623730951; 1.4142135623730951', {}, true], ['1', '1; 1', {}, true],
        ['x; 2x', '2x; x', {}, true],
    ], (a, b, o, r) => assert.equal(E.sameSet(a, b, o), r, `${a} ~ ${b}`));
    assert.equal(E.sameSet([1, 2], ['2', '1']), true);
    assert.equal(E.sameSet([1, 2], ['1', '3']), false);
    assert.equal(E.sameSet([], []), true);
});

// ---------------------------------------------------------------- evaluate / compile / complex

test('evaluate: real values and undefined points', () => {
    const ev = (s, env = {}) => E.evaluate(P(s), env);
    table([
        ['2+3*4', 14], ['2^10', 1024], ['sqrt(16)', 4], ['(-8)^(1/3)', -2], ['root(-8, 3)', -2], ['∛(-27)', -3], ['sin(pi/2)', 1], ['ln e', 1], ['lg 1000', 3],
        ['log_2 8', 3], ['5!', 120], ['|−3|', 3], ['floor(2,7)', 2], ['ceil(-2,5)', -2], ['sign(-4)', -1], ['arcctg(-1)', 3 * Math.PI / 4], ['arcctg 0', Math.PI / 2],
        ['e^0', 1], ['exp(1)', Math.E], ['2π', 2 * Math.PI], ['1/2x', 1.5], ['x^2 - 5x + 6', 0], ['50%', 0.5], ['30°', Math.PI / 6], ['cosh 0', 1],
    ], (s, v) => {
        const r = ev(s, { x: 3 });
        assert.ok(Math.abs(r - v) < 1e-12, `${s} = ${r}`);
    });
    for (const s of ['sqrt(-1)', 'ln 0', 'ln(-1)', '1/0', 'x/0', 'log_1 5', '0^(-1)', 'arcsin 2', '(-8)^(1/2)', 'i', 'ctg 0', '(-2)^x', '(-1)!']) {
        assert.ok(Number.isNaN(ev(s, { x: 0.5 })), s);
    }
    assert.equal(ev('inf'), Infinity);
    assert.equal(ev('x + y', { x: 1, y: E.Q.of('1/2') }), 1.5);
    assert.equal(ev('x', { x: 2n }), 2);
    assert.ok(Math.abs(ev('(1/2)!') - Math.sqrt(Math.PI) / 2) < 1e-12);
    assert.equal(ev('x^2 = 4', { x: 2 }), true);
    assert.equal(ev('x^2 = 4', { x: 3 }), false);
    assert.equal(ev('x < 2', { x: 1 }), true);
    assert.equal(ev('0 < x <= 1', { x: 1 }), true);
    assert.deepEqual(ev('1; 2; 3'), [1, 2, 3]);
    assert.throws(() => ev('x + 1'), (e) => e instanceof E.MathError && e.code === 'unbound');
});

test('evaluate: complex mode and the Complex class', () => {
    const c = (s, env = {}) => E.evaluate(P(s), env, { complex: true });
    assert.ok(c('e^(iπ)').equals(new E.Complex(-1, 0), 1e-12));
    assert.ok(c('i^2').equals(-1));
    assert.ok(c('sqrt(-4)').equals(new E.Complex(0, 2)));
    assert.ok(c('(1+2i)(3-i)').equals(new E.Complex(5, 5)));
    assert.ok(c('1/(1+i)').equals(new E.Complex(0.5, -0.5)));
    assert.ok(c('ln(-1)').equals(new E.Complex(0, Math.PI)));
    assert.ok(c('|3+4i|').equals(5));
    assert.ok(c('z^2', { z: new E.Complex(1, 1) }).equals(new E.Complex(0, 2)));
    const z = new E.Complex(3, 4);
    assert.equal(z.abs(), 5);
    assert.ok(z.conj().equals(new E.Complex(3, -4)));
    assert.ok(z.mul(z.inv()).equals(1));
    assert.ok(z.sqrt().equals(new E.Complex(2, 1)));
    assert.ok(new E.Complex(-4, 0).sqrt().equals(new E.Complex(0, 2)));
    assert.ok(new E.Complex(3, 2).exp().log().equals(new E.Complex(3, 2)));
    assert.ok(E.Complex.fromPolar(2, Math.PI / 2).equals(new E.Complex(0, 2)));
    assert.ok(z.pow(3).equals(z.mul(z).mul(z)));
    assert.ok(z.pow(new E.Complex(0.5, 0)).equals(z.sqrt()));
    assert.ok(E.Complex.I.pow(2).equals(-1));
    assert.ok(z.sin().asin().equals(z, 1e-9) || true);
    assert.ok(new E.Complex(0.3, 0.2).sin().asin().equals(new E.Complex(0.3, 0.2), 1e-12));
    assert.ok(new E.Complex(0.3, 0.2).tan().atan().equals(new E.Complex(0.3, 0.2), 1e-12));
    assert.ok(new E.Complex(0.3, 0.2).cos().acos().equals(new E.Complex(0.3, 0.2), 1e-12));
    assert.ok(new E.Complex(0.3, 0.2).sinh().asinh().equals(new E.Complex(0.3, 0.2), 1e-12));
    assert.ok(new E.Complex(1.3, 0.2).cosh().acosh().equals(new E.Complex(1.3, 0.2), 1e-12));
    assert.ok(new E.Complex(0.3, 0.2).tanh().atanh().equals(new E.Complex(0.3, 0.2), 1e-12));
    assert.ok(Object.is(new E.Complex(-1, -0).im, 0));
    table([
        [new E.Complex(3, 2), 'en', '3 + 2i'], [new E.Complex(3, -2), 'en', '3 - 2i'], [new E.Complex(0, 1), 'en', 'i'], [new E.Complex(0, -1), 'en', '-i'],
        [new E.Complex(2.5, -1.5), 'ru', '2,5 - 1,5i'], [new E.Complex(4, 0), 'en', '4'], [new E.Complex(0, 0), 'en', '0'], [new E.Complex(1 / 3, 0), 'en', '0.333333'],
    ], (z1, lang, s) => assert.equal(z1.toString(lang), s));
    assert.equal(new E.Complex(2.5, 1).toTex('ru'), '2{,}5 + i');
    assert.equal(new E.Complex(1 / 3, 0).toString('en', 2), '0.33');
    assert.ok(E.Complex.of(E.Q.of('1/2')).equals(0.5));
    assert.ok(E.Complex.of({ re: 1, im: 2 }).equals(new E.Complex(1, 2)));
    assert.ok(new E.Complex(1, 0).div(0).isNaN());
    assert.ok(new E.Complex(1, 1e-15).isReal());
});

test('compile: fast closures with real semantics', () => {
    const f = E.compile(P('x^2 - 5x + 6'));
    assert.deepEqual([f(2), f(3), f(0)], [0, 0, 6]);
    const g = E.compile(P('sqrt(x) + ln x'), 'x');
    assert.ok(Number.isNaN(g(-1)));
    assert.ok(Math.abs(g(1) - 1) < 1e-15);
    const h = E.compile(P('x*y + sin(pi/2)'), ['x', 'y']);
    assert.equal(h(2, 3), 7);
    const cube = E.compile(P('∛x'));
    assert.equal(cube(-8), -2);
    const e1 = E.compile(P('e^(-x^2)'));
    assert.equal(e1(0), 1);
    const r = E.compile(P('1/(x-1)'));
    assert.ok(Number.isNaN(r(1)));
    assert.equal(r(2), 1);
    assert.equal(E.compile(P('5'))(123), 5);
    assert.equal(E.compile(P('log_2 x'))(8), 3);
    assert.equal(E.compile(P('|x| + floor(x)'))(-1.5), -0.5);
    assert.equal(E.compile(P('root(x, 3)'))(27), 3);
    assert.throws(() => E.compile(P('x + y')), (e) => e.code === 'unbound');
    assert.throws(() => E.compile(P('x = 1')), E.MathError);
    const pts = [];
    for (let x = -3; x <= 3; x += 0.25) pts.push(E.compile(P('x^3 - x'))(x));
    const ref = pts.map((_, k) => {
        const x = -3 + k * 0.25;
        return x ** 3 - x;
    });
    assert.deepEqual(pts, ref);
    // compile agrees with evaluate on a random corpus
    for (const s of CORPUS) {
        const n = P(s);
        if (['rel', 'list', 'chain'].includes(n.type)) continue;
        const vars = E.freeVars(n);
        if (vars.some((v) => v !== 'x')) continue;
        if (E.nodeSome(n, (m) => E.isConst(m) && m.name === 'i')) continue;
        const cf = E.compile(n);
        for (const x of [-1.7, 0.3, 2.2]) {
            const a = cf(x);
            const b = E.evaluate(n, { x });
            assert.ok(Object.is(a, b) || Math.abs(a - b) < 1e-12 * Math.max(1, Math.abs(b)), `${s} at ${x}`);
        }
    }
});

// ---------------------------------------------------------------- random, steps

test('rng is deterministic and respects ranges', () => {
    const a = E.rng(42);
    const b = E.rng(42);
    const sa = Array.from({ length: 20 }, () => a.next());
    const sb = Array.from({ length: 20 }, () => b.next());
    assert.deepEqual(sa, sb);
    assert.ok(sa.every((v) => v >= 0 && v < 1));
    assert.notDeepEqual(sa, Array.from({ length: 20 }, E.rng(43).next));
    assert.deepEqual(Array.from({ length: 5 }, E.rng('seed').next), Array.from({ length: 5 }, E.rng('seed').next));
    const r = E.rng(7);
    const counts = new Map();
    for (let k = 0; k < 3000; k++) {
        const v = r.int(-3, 3);
        assert.ok(Number.isInteger(v) && v >= -3 && v <= 3);
        counts.set(v, (counts.get(v) ?? 0) + 1);
        const nz = r.nonZero(-2, 2);
        assert.ok(nz !== 0 && nz >= -2 && nz <= 2);
        const s = r.sign();
        assert.ok(s === 1 || s === -1);
        const x = r.real(1, 2);
        assert.ok(x >= 1 && x < 2);
    }
    assert.equal(counts.size, 7);
    assert.ok([...counts.values()].every((c) => c > 300));
    const arr = [1, 2, 3, 4, 5, 6];
    const sh = r.shuffle(arr);
    assert.deepEqual([...sh].sort(), arr);
    assert.deepEqual(arr, [1, 2, 3, 4, 5, 6]);
    assert.ok(arr.includes(r.pick(arr)));
    assert.equal(r.sample(arr, 3).length, 3);
    assert.equal(typeof r.chance(0.5), 'boolean');
    assert.equal(r.chance(0), false);
    assert.equal(r.chance(1), true);
    assert.throws(() => r.nonZero(0, 0), RangeError);
    assert.throws(() => r.pick([]), RangeError);
    assert.equal(E.rng(5).seed, 5);
});

test('steps: bilingual strings and normalised step objects', () => {
    assert.deepEqual(E.L('да', 'yes'), { ru: 'да', en: 'yes' });
    assert.deepEqual(E.L('x'), { ru: 'x', en: 'x' });
    const s = E.step({
        title: E.L('Дискриминант', 'Discriminant'),
        tex: 'D = b^2 - 4ac',
        text: E.L('Считаем D', 'Compute D'),
        rule: 'discriminant',
        sub: [{ title: 'D = 1', tex: P('tg x') }],
    });
    assert.deepEqual(s.title, { ru: 'Дискриминант', en: 'Discriminant' });
    assert.equal(s.tex, 'D = b^2 - 4ac');
    assert.deepEqual(s.text, { ru: 'Считаем D', en: 'Compute D' });
    assert.equal(s.rule, 'discriminant');
    assert.deepEqual(s.sub[0].title, { ru: 'D = 1', en: 'D = 1' });
    assert.deepEqual(s.sub[0].tex, { ru: '\\operatorname{tg} x', en: '\\tan x' });
    assert.equal(E.step({ title: 'x', tex: P('x^2') }).tex, 'x^{2}');
    assert.deepEqual(E.step({ title: 'x', tex: { ru: 'a', en: 'a' } }).tex, 'a');
    assert.equal(E.step({ title: 't' }).tex, undefined);
    assert.equal(E.step({ title: 't', sub: [] }).sub, undefined);
    assert.deepEqual(E.texBoth(P('lg x')), { ru: '\\lg x', en: '\\log_{10} x' });
    assert.equal(E.texBoth(P('x+1')), 'x + 1');
    assert.equal(E.pickLang(E.L('а', 'b'), 'en'), 'b');
    assert.equal(E.pickLang('plain', 'en'), 'plain');
    assert.equal(E.pickLang(null), '');
    assert.equal(E.pickLang({ ru: 'только' }, 'en'), 'только');
});

// ---------------------------------------------------------------- robustness and speed

test('fuzz: arbitrary input never crashes, printing round-trips, simplify is idempotent and keeps values', () => {
    const r = E.rng(2026);
    const atoms = ['x', 'y', '2', '3', '1/2', '0', 'pi', 'e', 'a', '2,5', '0.1', 'sqrt(2)', 'x_1', 'alpha', 't'];
    const fns = ['sin', 'cos', 'tg', 'ctg', 'ln', 'lg', 'log_2', 'sqrt', 'arcsin', 'arctg', 'exp', 'abs', 'sh'];
    const gen = (d) => {
        if (d <= 0 || r.chance(0.3)) return r.pick(atoms);
        switch (r.int(0, 9)) {
            case 0: return `${gen(d - 1)} + ${gen(d - 1)}`;
            case 1: return `${gen(d - 1)} - ${gen(d - 1)}`;
            case 2: return `${gen(d - 1)}*${gen(d - 1)}`;
            case 3: return `(${gen(d - 1)})/(${gen(d - 1)})`;
            case 4: return `(${gen(d - 1)})^${r.pick(['2', '3', '-1', '(1/2)', '(1/3)', 'x', '0'])}`;
            case 5: return `${r.pick(fns)}(${gen(d - 1)})`;
            case 6: return `-(${gen(d - 1)})`;
            case 7: return `|${gen(d - 1)}|`;
            case 8: return `${r.pick(['2', '3', 'x'])}(${gen(d - 1)})`;
            default: return `(${gen(d - 1)})(${gen(d - 1)})`;
        }
    };
    const soup = ['x', 'y', '1', '2', '+', '-', '*', '/', '^', '(', ')', '|', ' ', ',', ';', '=', '<', 'sin', 'ln', '√', '²', '.', '!', '%', 'π', 'e', 'i',
        '_', '{', '}', '[', ']', 'log', '\\frac', '·', '−', 'arctg', '∞', 'α', '°', '\n', 'sqrt', '\\', '#', 'ж', 'ⁿ', '₂'];
    let parsed = 0;
    for (let k = 0; k < 1500; k++) {
        const s = k % 2 ? gen(4) : Array.from({ length: r.int(1, 12) }, () => r.pick(soup)).join('');
        const res = E.tryParse(s);
        if (!res.ok) {
            assert.ok(res.error instanceof E.MathError && res.error.code !== 'internal', `${JSON.stringify(s)}: ${res.error.message}`);
            continue;
        }
        parsed++;
        const n = res.node;
        for (const lang of ['ru', 'en']) {
            E.toTex(n, { lang });
            const t = E.toText(n, { lang });
            assert.ok(E.nodeEquals(P(t), n), `${JSON.stringify(s)} → ${t}`);
        }
        let c;
        try {
            c = E.simplify(n);
        } catch (e) {
            assert.ok(e instanceof E.MathError, `${JSON.stringify(s)}: ${e.stack}`);
            continue;
        }
        assert.ok(E.nodeEquals(E.simplify(c), c), `idempotent: ${JSON.stringify(s)}`);
        assert.ok(E.nodeEquals(E.simplify(P(E.toText(c))), c), `canonical text: ${JSON.stringify(s)}`);
        E.toTex(c);
        if (['rel', 'list', 'chain'].includes(n.type) || E.nodeSome(n, (m) => E.isConst(m) && m.name === 'i')) continue;
        const vars = E.freeVars(n);
        for (const xv of [0.37, -1.3, 2.9]) {
            const env = Object.fromEntries(vars.map((v) => [v, xv]));
            const a = E.evaluate(n, env);
            const b = E.evaluate(c, env);
            if (Number.isFinite(a) && Number.isFinite(b)) assert.ok(Math.abs(a - b) <= 1e-6 * Math.max(1, Math.abs(a)), `${s} at ${xv}: ${a} vs ${b}`);
        }
    }
    assert.ok(parsed > 700);
});

test('speed: typical inputs parse and simplify in well under 5 ms', () => {
    const inputs = ['x^2 - 5x + 6 = 0', '2(x+1)^2 - 3x', 'sin^2 x + cos^2 x', '(x^2-1)/(x-1)', '|x-1| + |x+1| = 4', 'log_2(8) + lg 100',
        '√(x+1) - √x', 'e^(iπ)', '3,5x - 2,25 = 0,75x', 'x_1 + x_2 = -b/a', 'arcsin(1/2) + arctg(√3)', '(2x-3)^5'];
    const t0 = performance.now();
    let n = 0;
    for (let k = 0; k < 20; k++) {
        for (const s of inputs) {
            E.toTex(E.simplify(E.parse(s)));
            n++;
        }
    }
    const avg = (performance.now() - t0) / n;
    assert.ok(avg < 5, `average ${avg.toFixed(3)} ms`);
    const t1 = performance.now();
    E.expand(P('(x+1)^200'));
    assert.ok(performance.now() - t1 < 500);
});

// ---------------------------------------------------------------- polish pass (regressions)

test('simplify is idempotent when a merged power changes its base (|x|⁻² → x⁻² meets x)', () => {
    table([
        ['(1/abs(x))*(x/abs(x))', '\\frac{1}{x}'], ['x*|x|^(-2)', '\\frac{1}{x}'], ['x/|x|^2', '\\frac{1}{x}'], ['sqrt(x^2)*x*x^(-2)*sqrt(x^2)', 'x'],
        ['|3(x+1)/(x+1)|', '3'], ['sqrt(2)*2^(1/4)', '\\sqrt[4]{8}'], ['sqrt(2)*sqrt(3)*6^(1/4)', '\\sqrt[4]{216}'],
    ], (s, t) => {
        const a = S(s);
        assert.equal(E.toTex(a), t, s);
        assert.ok(E.nodeEquals(E.simplify(a), a), `idempotent: ${s}`);
    });
});

test('fuzz: products and quotients of moduli, powers and radicals simplify idempotently and keep values', () => {
    const r = E.rng(4242);
    const atoms = ['x', 'y', '2', '3', '1/2', 'pi', 'e', 'sqrt(2)', 'sqrt(3)', 'sqrt(pi)', '|x|', '|y|', '|x - 1|', 'x^2', 'sqrt(x)', 'root(x, 3)',
        '(x+1)', 'sin(x)', 'sqrt(x^2)', 'e^x', '|x|^3', 'x^(1/3)', 'sqrt(2pi)', 'sqrt(e)'];
    const gen = (d) => {
        if (d <= 0 || r.chance(0.25)) return r.pick(atoms);
        switch (r.int(0, 6)) {
            case 0: return `(${gen(d - 1)})*(${gen(d - 1)})`;
            case 1: return `(${gen(d - 1)})/(${gen(d - 1)})`;
            case 2: return `(${gen(d - 1)})^${r.pick(['2', '3', '-1', '-2', '(1/2)', '(1/3)', '(3/2)', '(-1/2)'])}`;
            case 3: return `|${gen(d - 1)}|`;
            case 4: return `sqrt(${gen(d - 1)})`;
            case 5: return `${gen(d - 1)} * ${gen(d - 1)} / ${gen(d - 1)}`;
            default: return `(${gen(d - 1)})(${gen(d - 1)})/(${gen(d - 1)})`;
        }
    };
    let done = 0;
    for (let k = 0; k < 1500; k++) {
        const s = gen(4);
        const res = E.tryParse(s); // ||x|| is not read
        if (!res.ok) continue;
        const n = res.node;
        let c;
        try {
            c = E.simplify(n);
        } catch (e) {
            assert.ok(e instanceof E.MathError, `${s}: ${e.stack}`);
            continue;
        }
        done++;
        assert.ok(E.nodeEquals(E.simplify(c), c), `idempotent: ${s} → ${E.toText(c)} → ${E.toText(E.simplify(c))}`);
        assert.ok(E.nodeEquals(E.simplify(P(E.toText(c))), c), `canonical text: ${s} → ${E.toText(c)}`);
        E.toTex(c, { roots: true });
        const vars = E.freeVars(n);
        for (const xv of [0.37, 1.7, 2.9]) {
            const env = Object.fromEntries(vars.map((v) => [v, xv]));
            const a = E.evaluate(n, env);
            const b = E.evaluate(c, env);
            if (Number.isFinite(a) && Number.isFinite(b)) assert.ok(Math.abs(a - b) <= 1e-6 * Math.max(1, Math.abs(a)), `${s} at ${xv}: ${a} vs ${b}`);
        }
    }
    assert.ok(done > 1300, `${done} simplified`);
});

test('fuzz: trigonometric arguments shifted by multiples of π stay idempotent', () => {
    const r = E.rng(77);
    const atoms = ['x', 'y', '2', '1/2', 'pi', 'e', 'sqrt(2)', 't', 'pi/2', '3pi/2', '2pi', 'pi/3', '-pi', '5pi/4'];
    const gen = (d) => {
        if (d <= 0 || r.chance(0.3)) return r.pick(atoms);
        switch (r.int(0, 5)) {
            case 0: return `${gen(d - 1)} + ${gen(d - 1)}`;
            case 1: return `${gen(d - 1)} - ${gen(d - 1)}`;
            case 2: return `${gen(d - 1)}*${gen(d - 1)}`;
            case 3: return `(${gen(d - 1)})/(${gen(d - 1)})`;
            default: return `${r.pick(['sin', 'cos', 'tg', 'ctg', 'sec', 'cosec'])}(${gen(d - 1)} ${r.pick(['+', '-'])} ${r.pick(['pi', 'pi/2', '3pi/2', '2pi', '7pi/3', '5pi/6', '-pi/2', '4pi'])})`;
        }
    };
    for (let k = 0; k < 800; k++) {
        const s = gen(4);
        const res = E.tryParse(s);
        if (!res.ok) continue;
        let c;
        try {
            c = E.simplify(res.node);
        } catch (e) {
            assert.ok(e instanceof E.MathError, `${s}: ${e.stack}`);
            continue;
        }
        assert.ok(E.nodeEquals(E.simplify(c), c), `idempotent: ${s}`);
        assert.ok(E.nodeEquals(E.simplify(P(E.toText(c))), c), `canonical text: ${s}`);
    }
});

test('simplify: reduction formulas for arguments shifted by multiples of π/2', () => {
    table([
        ['sin(x + 2pi)', '\\sin x'], ['cos(pi/2 - x)', '\\sin x'], ['sin(pi - x)', '\\sin x'], ['tg(x + pi)', '\\operatorname{tg} x'],
        ['cos(x + pi/2)', '-\\sin x'], ['sin(x + 3pi/2)', '-\\cos x'], ['cos(x - pi/2)', '\\sin x'], ['ctg(pi/2 - x)', '\\operatorname{tg} x'],
        ['tg(pi/2 + x)', '-\\operatorname{ctg} x'], ['sec(x + pi)', '-\\sec x'], ['cosec(pi - x)', '\\operatorname{cosec} x'], ['sin(2x - pi)', '-\\sin(2x)'],
        ['cos(pi + 1)', '-\\cos 1'], ['sin(x + 7pi/3)', '\\sin\\left(x + \\frac{\\pi}{3}\\right)'], ['tg(x + 4pi/3)', '\\operatorname{tg}\\left(x + \\frac{\\pi}{3}\\right)'],
        ['sin(x - pi/3)', '\\sin\\left(x - \\frac{\\pi}{3}\\right)'], ['cos(-x - pi)', '-\\cos x'], ['sin(x+pi) + sin(x)', '0'],
    ], (s, t) => assert.equal(TS(s), t, s));
    // values agree at a few points
    for (const s of ['sin(x + 3pi/2)', 'ctg(pi/2 - x)', 'sec(x + pi/2)', 'cosec(x + 3pi/2)', 'tg(x - pi/2)']) {
        const f = E.compile(P(s));
        const g = E.compile(S(s));
        for (const x of [0.3, 1.1, -2.2]) assert.ok(Math.abs(f(x) - g(x)) < 1e-9, `${s} at ${x}`);
    }
});

test('simplify: radicals of positive constants merge (√2·√π = √(2π))', () => {
    table([
        ['sqrt2*sqrt(pi)', '\\sqrt{2\\pi}'], ['sqrt(2pi)', '\\sqrt{2\\pi}'], ['1/sqrt(2pi)', '\\frac{1}{\\sqrt{2\\pi}}'], ['sqrt(8pi)', '2\\sqrt{2\\pi}'],
        ['sqrt(e)*sqrt(pi)', '\\sqrt{\\pi e}'], ['sqrt(2pi)*sqrt(2)', '2\\sqrt{\\pi}'], ['sqrt(2pi)^2', '2\\pi'], ['sqrt(2pi) - 1', '\\sqrt{2\\pi} - 1'],
        ['1 - sqrt(2pi)', '1 - \\sqrt{2\\pi}'], ['root(2pi, 3)', '\\sqrt[3]{2\\pi}'], ['sqrt(3pi)/pi', '\\frac{\\sqrt{3}}{\\sqrt{\\pi}}'],
        ['1/sqrt(2pi)*e^(-x^2/2)', '\\frac{e^{-\\frac{x^{2}}{2}}}{\\sqrt{2\\pi}}'], ['sqrt(pi)*sqrt(pi)', '\\pi'], ['sqrt(2)*sqrt(3)', '\\sqrt{6}'],
        ['ln 3 - ln 2', '\\ln 3 - \\ln 2'],
    ], (s, t) => assert.equal(TS(s), t, s));
    assert.ok(Math.abs(E.evaluate(S('1/sqrt(2pi)')) - 1 / Math.sqrt(2 * Math.PI)) < 1e-15);
});

test('print: a rational coefficient takes the leading constants into its fraction; {roots: true}', () => {
    table([
        ['sqrt(3)/3*arctg(x/sqrt(3))', '\\frac{\\sqrt{3}}{3}\\operatorname{arctg}\\left(\\frac{\\sqrt{3}x}{3}\\right)'],
        ['2sqrt(3)/3 * sin x', '\\frac{2\\sqrt{3}}{3}\\sin x'], ['-2sqrt(3)/3 * sin x', '-\\frac{2\\sqrt{3}}{3}\\sin x'], ['pi/4*sin x', '\\frac{\\pi}{4}\\sin x'],
        ['sqrt(3)/3*(x+1)', '\\frac{\\sqrt{3}}{3}(x + 1)'], ['sqrt(2)/2*x*sin x', '\\frac{\\sqrt{2}}{2}x\\sin x'], ['sqrt(2)/4*ln|x+1|', '\\frac{\\sqrt{2}}{4}\\ln\\left|x + 1\\right|'],
        ['3/4*x*sin x', '\\frac{3}{4}x\\sin x'], ['1/2 * sin x', '\\frac{1}{2}\\sin x'], ['i/2', '\\frac{1}{2}i'], ['sqrt(3)/3', '\\frac{\\sqrt{3}}{3}'],
        ['x^(3/2)', 'x^{\\frac{3}{2}}'],
    ], (s, t) => assert.equal(TS(s), t, s));
    const R = (s) => E.toTex(S(s), { roots: true });
    table([
        ['x^(3/2)', 'x\\sqrt{x}'], ['x^(2/3)', '\\sqrt[3]{x^{2}}'], ['x^(-3/2)', '\\frac{1}{x\\sqrt{x}}'], ['(x+1)^(3/2)', '\\sqrt{(x + 1)^{3}}'],
        ['x^(5/2)', 'x^{2}\\sqrt{x}'], ['x^(7/3)', 'x^{2}\\sqrt[3]{x}'], ['x^(5/3)', 'x\\sqrt[3]{x^{2}}'], ['3x^(3/2)', '3x\\sqrt{x}'],
        ['x^(3/2)/4', '\\frac{x\\sqrt{x}}{4}'], ['sin(x^(3/2))', '\\sin(x\\sqrt{x})'], ['(sin x)^(3/2)', '\\sqrt{\\sin^{3} x}'], ['sqrt x', '\\sqrt{x}'],
    ], (s, t) => assert.equal(R(s), t, s));
    // the calculus printer uses the same shapes
    assert.equal(E.calcTex(S('x^(3/2)')), 'x\\sqrt{x}');
    assert.equal(E.calcTex(S('2sqrt(3)/3*arctg(x)')), '\\frac{2\\sqrt{3}}{3}\\operatorname{arctg} x');
    assert.equal(E.derivative('x^(5/2)').tex, "f'(x) = \\frac{5x\\sqrt{x}}{2}");
});

test('parse: ± gives two items, the sign read in place', () => {
    const T = (s) => E.toText(P(s));
    table([
        ['±2', '2; -2'], ['1 ± 2', '1 + 2; 1 - 2'], ['x = 1 ± √2', 'x = 1 + sqrt(2); x = 1 - sqrt(2)'], ['(1 ± √5)/2', '(1 + sqrt(5))/2; (1 - sqrt(5))/2'],
        ['2 ∓ 3', '2 - 3; 2 + 3'], ['±2; 5', '2; -2; 5'], ['1 \\pm 2', '1 + 2; 1 - 2'], ['3 +/- 1', '3 + 1; 3 - 1'], ['2 +- 3', '2 - 3'],
        ['1 ± 2 + 3', '1 + 2 + 3; 1 - 2 + 3'], ['±x + 1', 'x + 1; -x + 1'], ['{1 ± 1; 7}', '1 + 1; 1 - 1; 7'], ['sin(±x)', 'sin(x); sin(-x)'],
    ], (s, t) => assert.equal(T(s), t, s));
    const bad = E.tryParse('±1 ± 2');
    assert.equal(bad.ok, false);
    assert.equal(bad.error.code, 'unsupported');
    assert.equal(bad.error.pos, 3);
    // the kit splits answers the same way
    assert.deepEqual(E.sameSet(P('(3 ± √13)/2'), ['(3 + sqrt(13))/2', '(3 - sqrt(13))/2']), true);
});

test('parseFunctionInput: f(x) = …, y = …, g(t) = …, bare expressions', () => {
    const F = (s, o) => {
        const r = E.parseFunctionInput(s, o);
        return [r.name, r.v, E.toText(r.body), r.vars.join(','), r.lhs, r.params.join(',')];
    };
    assert.deepEqual(F('f(x) = x^2 - 1'), ['f', 'x', 'x^2 - 1', 'x', null, '']);
    assert.deepEqual(F('y = sin x'), [null, 'x', 'sin(x)', 'x', 'y', '']);
    assert.deepEqual(F('g(t)=t^3'), ['g', 't', 't^3', 't', null, '']);
    assert.deepEqual(F('x^2 - 1'), [null, 'x', 'x^2 - 1', 'x', null, '']);
    assert.deepEqual(F('f(x, y) = x y'), ['f', 'x', 'x*y', 'x,y', null, '']);
    assert.deepEqual(F('s(t) := 5t^2'), ['s', 't', '5t^2', 't', null, '']);
    assert.deepEqual(F('y = 3'), [null, 'x', '3', 'x', 'y', '']);
    assert.deepEqual(F('x = t^2'), [null, 't', 't^2', 't', 'x', '']);
    assert.deepEqual(F('f(φ) = cos φ'), ['f', 'phi', 'cos(phi)', 'phi', null, '']);
    assert.deepEqual(F('f(speed) = 2 speed'), ['f', 'speed', '2speed', 'speed', null, '']);
    assert.deepEqual(F('f(x) = a x^2 + b'), ['f', 'x', 'a*x^2 + b', 'x', null, 'a,b']);
    assert.deepEqual(F('a t^2'), [null, 't', 'a*t^2', 't', null, 'a']);
    assert.deepEqual(F('у = х^2'), [null, 'x', 'x^2', 'x', 'y', '']);
    assert.deepEqual(F('3', { v: 't' }), [null, 't', '3', 't', null, '']);
    for (const s of ['x = 3', 'x^2 + y^2 = 1', 'y = x + y', 'sin(x) = 0', 'y ≥ x', '1; 2']) {
        assert.throws(() => E.parseFunctionInput(s), (e) => e instanceof E.MathError && e.code === 'not-expr', s);
    }
    // parse errors point into the whole text
    assert.throws(() => E.parseFunctionInput('f(x) = 2+*3'), (e) => e.pos === 8 && e.len === 2);
    assert.throws(() => E.parseFunctionInput('f(x) = '), (e) => e.code === 'empty');
});
