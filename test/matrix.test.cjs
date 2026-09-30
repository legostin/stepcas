// tests/Js/math-engine-matrix.test.cjs — exact linear algebra (matrix.js) and the float toolkit
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E, Matrix, Q;
before(async () => {
    E = await import('../src/index.js');
    ({ Matrix, Q } = E);
});

// ---------------------------------------------------------------- helpers

const close = (a, b, tol = 1e-9, msg) => assert.ok(Math.abs(a - b) <= tol * Math.max(1, Math.abs(b)), `${msg ?? ''} expected ${b}, got ${a}`);
const mstr = (m) => m.toString();
function checkSteps(steps, where = '') {
    assert.ok(Array.isArray(steps) && steps.length > 0, `${where}: steps`);
    for (const s of steps) {
        assert.ok(s.title && typeof s.title.ru === 'string' && typeof s.title.en === 'string' && s.title.ru && s.title.en, `${where}: title`);
        if (s.tex !== undefined) {
            const texts = typeof s.tex === 'string' ? [s.tex] : [s.tex.ru, s.tex.en];
            for (const t of texts) {
                assert.equal(typeof t, 'string', `${where}: tex type`);
                assert.ok(!/undefined|NaN|\[object|null/.test(t), `${where}: bad tex ${t}`);
                let depth = 0;
                for (const ch of t.replace(/\\[{}]/g, '')) {
                    if (ch === '{') depth++;
                    if (ch === '}') depth--;
                    assert.ok(depth >= 0, `${where}: braces ${t}`);
                }
                assert.equal(depth, 0, `${where}: unbalanced ${t}`);
                const begins = (t.match(/\\begin\{/g) || []).length,
                    ends = (t.match(/\\end\{/g) || []).length;
                assert.equal(begins, ends, `${where}: begin/end ${t}`);
            }
        }
        if (s.text !== undefined) {
            assert.ok(typeof s.text.ru === 'string' && typeof s.text.en === 'string', `${where}: text`);
            assert.ok(!/undefined|NaN|\[object/.test(s.text.ru + s.text.en), `${where}: bad text ${s.text.ru}`);
            assert.ok(/[а-яё]/i.test(s.text.ru), `${where}: RU text is not Russian: ${s.text.ru}`);
        }
        if (s.sub) checkSteps(s.sub, `${where} > ${s.title.en}`);
    }
}
function rng(seed) {
    let s = seed >>> 0 || 1;
    return () => {
        s ^= s << 13;
        s >>>= 0;
        s ^= s >>> 17;
        s ^= s << 5;
        s >>>= 0;
        return s / 4294967296;
    };
}
function randInt(r, lo, hi) {
    return lo + Math.floor(r() * (hi - lo + 1));
}
function randMatrix(r, m, n, lo = -5, hi = 5) {
    return Matrix.from(Array.from({ length: m }, () => Array.from({ length: n }, () => randInt(r, lo, hi))));
}
/** Leibniz formula — an independent determinant for n ≤ 5. */
function leibniz(A) {
    const n = A.rows;
    const perm = [...Array(n).keys()];
    let total = Q.ZERO;
    const permute = (k) => {
        if (k === n) {
            let inv = 0;
            for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (perm[i] > perm[j]) inv++;
            let p = inv % 2 ? Q.MINUS_ONE : Q.ONE;
            for (let i = 0; i < n; i++) p = p.mul(A.get(i, perm[i]));
            total = total.add(p);
            return;
        }
        for (let i = k; i < n; i++) {
            [perm[k], perm[i]] = [perm[i], perm[k]];
            permute(k + 1);
            [perm[k], perm[i]] = [perm[i], perm[k]];
        }
    };
    permute(0);
    return total;
}
function applyOps(A, ops) {
    const W = A.toArray();
    for (const op of ops) {
        if (op.op === 'swap') [W[op.i], W[op.j]] = [W[op.j], W[op.i]];
        else if (op.op === 'scale') W[op.i] = W[op.i].map((v) => v.mul(op.k));
        else W[op.i] = W[op.i].map((v, c) => v.add(op.k.mul(W[op.j][c])));
    }
    return Matrix.from(W);
}
function isRref(Mx, lim = Mx.cols) {
    let lastPivot = -1;
    let zeroSeen = false;
    for (let i = 0; i < Mx.rows; i++) {
        const row = Mx.row(i).slice(0, lim);
        const p = row.findIndex((v) => !v.isZero());
        if (p < 0) {
            zeroSeen = true;
            continue;
        }
        if (zeroSeen || p <= lastPivot || !row[p].isOne()) return false;
        for (let k = 0; k < Mx.rows; k++) if (k !== i && !Mx.get(k, p).isZero()) return false;
        lastPivot = p;
    }
    return true;
}
const evalPolyAtMatrix = (coefs, A) => {
    let R = Matrix.zeros(A.rows);
    for (let k = coefs.length - 1; k >= 0; k--) R = R.mul(A).add(Matrix.identity(A.rows).scale(coefs[k]));
    return R;
};

// ---------------------------------------------------------------- Matrix basics

test('Matrix construction, access and arithmetic', () => {
    const A = Matrix.from([
        [1, 2],
        ['1/2', 3],
    ]);
    assert.equal(A.rows, 2);
    assert.equal(A.cols, 2);
    assert.equal(A.get(1, 0).toString(), '1/2');
    assert.ok(A.get(0, 0) instanceof Q);
    const B = A.set(0, 0, '0,5');
    assert.equal(A.get(0, 0).toString(), '1', 'set is immutable');
    assert.equal(B.get(0, 0).toString(), '1/2');
    assert.equal(
        mstr(
            A.add([
                [1, 1],
                [1, 1],
            ]),
        ),
        '[[2, 3], [3/2, 4]]',
    );
    assert.equal(mstr(A.sub(A)), '[[0, 0], [0, 0]]');
    assert.equal(mstr(A.scale('2')), '[[2, 4], [1, 6]]');
    assert.equal(mstr(A.mul(2)), '[[2, 4], [1, 6]]');
    assert.equal(mstr(A.neg()), '[[-1, -2], [-1/2, -3]]');
    assert.equal(mstr(Matrix.from([[1, 2, 3]]).mul([[1], [2], [3]])), '[[14]]');
    assert.equal(mstr(Matrix.from([[1], [2]]).mul([[3, 4]])), '[[3, 4], [6, 8]]');
    assert.deepEqual(A.mul([2, 2]).map(String), ['6', '7']);
    assert.equal(
        mstr(
            Matrix.from([
                [1, 2, 3],
                [4, 5, 6],
            ]).transpose(),
        ),
        '[[1, 4], [2, 5], [3, 6]]',
    );
    assert.equal(A.trace().toString(), '4');
    assert.ok(
        A.equals([
            [1, 2],
            [0.5, 3],
        ]),
    );
    assert.ok(!A.equals([[1, 2]]));
    assert.ok(Matrix.identity(3).isSymmetric());
    assert.ok(Matrix.zeros(2, 3).isZero());
    assert.equal(Matrix.zeros(2, 3).cols, 3);
    assert.equal(mstr(Matrix.identity(2).augment([[5], [6]])), '[[1, 0, 5], [0, 1, 6]]');
    assert.equal(
        mstr(
            Matrix.from([
                [1, 2, 3],
                [4, 5, 6],
                [7, 8, 9],
            ]).minor(1, 1),
        ),
        '[[1, 3], [7, 9]]',
    );
    assert.equal(
        mstr(
            Matrix.fromColumns([
                [1, 2],
                [3, 4],
            ]),
        ),
        '[[1, 3], [2, 4]]',
    );
    assert.equal(mstr(Matrix.diag([1, 2])), '[[1, 0], [0, 2]]');
    assert.equal(mstr(Matrix.from([1, 2, 3])), '[[1], [2], [3]]', 'flat array → column');
    assert.deepEqual(A.toNumbers(), [
        [1, 2],
        [0.5, 3],
    ]);
    assert.deepEqual(A.toStrings(), [
        ['1', '2'],
        ['1/2', '3'],
    ]);
    assert.deepEqual(A.row(1).map(String), ['1/2', '3']);
    assert.deepEqual(A.col(1).map(String), ['2', '3']);
    assert.throws(
        () => Matrix.from([[1, 2], [3]]),
        (e) => e.name === 'MathError' && e.code === 'shape',
    );
    assert.throws(
        () => Matrix.from([]),
        (e) => e.code === 'shape',
    );
    assert.throws(
        () => A.mul([[1, 2, 3]]),
        (e) => /Нельзя умножить/.test(e.msg.ru),
    );
    assert.throws(
        () => A.add([[1]]),
        (e) => e.code === 'shape',
    );
    assert.throws(() => Matrix.from([[1, 2]]).trace());
});

test('TeX output: pmatrix, vmatrix, augmented bar, boxes', () => {
    const A = Matrix.from([
        [1, '-1/2'],
        [3, 4],
    ]);
    assert.equal(A.toTex(), '\\begin{pmatrix} 1 & -\\frac{1}{2} \\\\ 3 & 4 \\end{pmatrix}');
    assert.equal(A.toTex({ env: 'vmatrix' }), '\\begin{vmatrix} 1 & -\\frac{1}{2} \\\\ 3 & 4 \\end{vmatrix}');
    assert.equal(
        Matrix.from([
            [1, 2, 3],
            [4, 5, 6],
        ]).toTex({ augmented: 1 }),
        '\\left(\\begin{array}{cc|c} 1 & 2 & 3 \\\\ 4 & 5 & 6 \\end{array}\\right)',
    );
    assert.equal(
        Matrix.from([
            [1, 0, 1, 0],
            [0, 1, 0, 1],
        ]).toTex({ augmented: 2 }),
        '\\left(\\begin{array}{cc|cc} 1 & 0 & 1 & 0 \\\\ 0 & 1 & 0 & 1 \\end{array}\\right)',
    );
    assert.match(A.toTex({ boxed: [[0, 0]] }), /\\boxed\{1\}/);
});

// ---------------------------------------------------------------- row reduction

test('RREF of a system: steps replay to the final matrix', () => {
    const A = Matrix.from([
        [1, 2, -1, -4],
        [2, 3, -1, -11],
        [-2, 0, -3, 22],
    ]);
    const r = E.matRref(A, { augmented: 1, steps: true });
    assert.equal(mstr(r.matrix), '[[1, 0, 0, -8], [0, 1, 0, 1], [0, 0, 1, -2]]');
    assert.deepEqual(r.pivots, [0, 1, 2]);
    assert.equal(r.rank, 3);
    checkSteps(r.steps, 'rref');
    assert.ok(applyOps(A, r.ops).equals(r.matrix), 'ops replay');
    const opSteps = r.steps.filter((s) => s.data?.op);
    assert.equal(opSteps.length, r.ops.length);
    let cur = A;
    opSteps.forEach((s, k) => {
        cur = applyOps(cur, [r.ops[k]]);
        assert.equal(s.data.matrixTex, cur.toTex({ augmented: 1 }), `step ${k} shows the matrix after the operation`);
        assert.ok(s.tex.endsWith(s.data.matrixTex));
    });
    const first = opSteps[0];
    assert.equal(first.data.opTex, 'R_{2} \\to R_{2} - 2\\,R_{1}');
    assert.equal(first.text.ru, 'Обнуляем элемент под ведущим: из второй строки вычитаем первую, умноженную на 2.');
    assert.equal(first.text.en, 'Clear the entry below the pivot: subtract 2 times row 1 from row 2.');
    assert.ok(opSteps.some((s) => s.data.phase === 'backward'));
    assert.ok(opSteps.every((s) => ['swap', 'scale', 'add'].includes(s.data.op)));
});

test('pivot strategy keeps numbers small', () => {
    const r = E.matRref(
        [
            [3, 6],
            [1, 5],
        ],
        { steps: true },
    );
    const swap = r.steps.find((s) => s.data?.op === 'swap');
    assert.ok(swap, 'swaps to get the 1 on top');
    assert.match(swap.text.ru, /единица/);
    assert.equal(swap.data.opTex, 'R_{1} \\leftrightarrow R_{2}');
    assert.equal(mstr(r.matrix), '[[1, 0], [0, 1]]');
    const neg = E.matRref(
        [
            [-1, 2],
            [3, 1],
        ],
        { steps: true },
    );
    assert.equal(neg.ops[0].op, 'scale');
    assert.equal(neg.steps.find((s) => s.data?.op === 'scale').data.opTex, 'R_{1} \\to -R_{1}');
    const div = E.matRref(
        [
            [3, 5],
            [2, 4],
        ],
        { steps: true },
    );
    assert.equal(div.ops[0].op, 'swap', 'the row 2 4 divides by 2 without fractions');
    assert.match(
        E.matRref(
            [
                [0, 1],
                [1, 0],
            ],
            { steps: true },
        ).steps.find((s) => s.data?.op === 'swap').text.ru,
        /стоит 0/,
    );
    const scale = E.matRref(
        [
            [4, 6],
            [6, 3],
        ],
        { steps: true },
    ).steps.find((s) => s.data?.op === 'scale');
    assert.match(scale.data.opTex, /\\frac\{1\}\{/);
});

test('rank, null space, random RREF properties', () => {
    assert.equal(
        E.matRank([
            [1, 2],
            [2, 4],
        ]),
        1,
    );
    assert.equal(
        E.matRank([
            [0, 0],
            [0, 0],
        ]),
        0,
    );
    assert.equal(
        E.matRank([
            [1, 2, 3],
            [4, 5, 6],
            [7, 8, 9],
        ]),
        2,
    );
    assert.equal(E.matRank(Matrix.identity(5)), 5);
    const ns = E.matNullspace([
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9],
    ]);
    assert.deepEqual(
        ns.map((v) => v.map(String)),
        [['1', '-2', '1']],
    );
    const ns2 = E.matNullspace([[1, 2, 3]]);
    assert.equal(ns2.length, 2);
    assert.deepEqual(
        E.matNullspace([
            [1, 0],
            [0, 1],
        ]),
        [],
    );
    assert.deepEqual(
        E.matNullspace([[2, 1]], { integer: false }).map((v) => v.map(String)),
        [['-1/2', '1']],
    );
    const r = rng(42);
    for (let t = 0; t < 60; t++) {
        const m = randInt(r, 1, 4),
            n = randInt(r, 1, 5);
        const A = randMatrix(r, m, n, -4, 4);
        const red = E.matRref(A, { steps: t % 5 === 0 });
        assert.ok(isRref(red.matrix), `RREF shape for ${mstr(A)}`);
        assert.ok(applyOps(A, red.ops).equals(red.matrix), 'ops replay');
        assert.equal(E.matRank(A), red.rank);
        assert.equal(E.matRank(A.transpose()), red.rank, 'row rank = column rank');
        const N = E.matNullspace(A);
        assert.equal(N.length, n - red.rank, 'rank–nullity');
        for (const v of N)
            assert.ok(
                A.mul(v).every((x) => x.isZero()),
                'null vector',
            );
        if (red.steps) checkSteps(red.steps, 'random rref');
    }
});

// ---------------------------------------------------------------- determinants

test('determinants by every method agree (and with Leibniz)', () => {
    const C = Matrix.from([
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 10],
    ]);
    for (const method of ['gauss', 'cofactor', 'sarrus']) assert.equal(E.matDet(C, { method }).toString(), '-3', method);
    assert.equal(
        E.matDet([
            [1, 2],
            [3, 4],
        ]).toString(),
        '-2',
    );
    assert.equal(E.matDet([[5]]).toString(), '5');
    assert.equal(
        E.matDet([
            ['1/2', 1],
            [1, 4],
        ]).toString(),
        '1',
    );
    assert.equal(
        E.matDet([
            [1, 2, 3],
            [4, 5, 6],
            [7, 8, 9],
        ]).toString(),
        '0',
    );
    assert.equal(E.matDet(Matrix.identity(6)).toString(), '1');
    const V = Matrix.from([
        [1, 1, 1, 1],
        [1, 2, 4, 8],
        [1, 3, 9, 27],
        [1, 4, 16, 64],
    ]);
    assert.equal(E.matDet(V).toString(), '12', 'Vandermonde 1·2·3·1·2·1');
    assert.throws(
        () => E.matDet([[1, 2, 3]]),
        (e) => e.code === 'shape',
    );
    assert.throws(
        () =>
            E.matDet(
                [
                    [1, 2],
                    [3, 4],
                ],
                { method: 'sarrus' },
            ),
        (e) => e.code === 'method',
    );
    const r = rng(7);
    for (let t = 0; t < 80; t++) {
        const n = randInt(r, 1, 5);
        const A = randMatrix(r, n, n, -6, 6);
        const ref = leibniz(A);
        assert.equal(E.matDet(A).toString(), ref.toString());
        assert.equal(E.matDet(A, { method: 'gauss' }).toString(), ref.toString());
        assert.equal(E.matDet(A, { method: 'cofactor' }).toString(), ref.toString());
        if (n === 3) assert.equal(E.matDet(A, { method: 'sarrus' }).toString(), ref.toString());
        assert.equal(E.matDet(A.transpose()).toString(), ref.toString(), 'det Aᵀ = det A');
    }
    for (let t = 0; t < 20; t++) {
        const A = randMatrix(r, 3, 3),
            B = randMatrix(r, 3, 3);
        assert.equal(E.matDet(A.mul(B)).toString(), E.matDet(A).mul(E.matDet(B)).toString(), 'det(AB) = det A · det B');
    }
});

test('determinant steps for each method', () => {
    const s2 = E.matDet(
        [
            [2, 3],
            [1, 5],
        ],
        { steps: true },
    );
    assert.equal(s2.value.toString(), '7');
    assert.equal(s2.steps[0].tex, '\\begin{vmatrix} 2 & 3 \\\\ 1 & 5 \\end{vmatrix} = 2 \\cdot 5 - 3 \\cdot 1 = 7');
    checkSteps(s2.steps, 'det2');
    const s3 = E.matDet(
        [
            [2, 0, 1],
            [1, 3, 2],
            [1, 1, 1],
        ],
        { steps: true },
    );
    assert.equal(s3.method, 'sarrus');
    assert.equal(s3.value.toString(), '0');
    checkSteps(s3.steps, 'sarrus');
    assert.match(s3.steps[2].tex, /\(6 \+ 0 \+ 1\) - \(3 \+ 4 \+ 0\) = 0/);
    const g = E.matDet(
        [
            [0, 2, 1, 3],
            [1, 1, 0, 2],
            [2, 0, 1, 1],
            [1, 3, 2, 0],
        ],
        { steps: true },
    );
    assert.equal(g.method, 'gauss');
    assert.equal(
        g.value.toString(),
        leibniz(
            Matrix.from([
                [0, 2, 1, 3],
                [1, 1, 0, 2],
                [2, 0, 1, 1],
                [1, 3, 2, 0],
            ]),
        ).toString(),
    );
    checkSteps(g.steps, 'gauss det');
    assert.ok(g.steps.some((s) => s.data?.op === 'swap' && /меняет знак/.test(s.text.ru)));
    const c = E.matDet(
        [
            [1, 0, 2, 0],
            [3, 1, 0, 1],
            [0, 2, 1, 0],
            [1, 0, 0, 2],
        ],
        { steps: true, method: 'cofactor' },
    );
    assert.equal(c.value.toString(), '22');
    assert.equal(
        c.value.toString(),
        leibniz(
            Matrix.from([
                [1, 0, 2, 0],
                [3, 1, 0, 1],
                [0, 2, 1, 0],
                [1, 0, 0, 2],
            ]),
        ).toString(),
    );
    checkSteps(c.steps, 'cofactor');
    assert.ok(
        c.steps[1].sub.some((s) => /^M_\{11\} =/.test(s.tex)),
        'nested expansions are labelled by the minor',
    );
    const z = E.matDet(
        [
            [1, 2, 3],
            [2, 4, 6],
            [1, 1, 1],
        ],
        { steps: true, method: 'gauss' },
    );
    assert.equal(z.value.toString(), '0');
    checkSteps(z.steps, 'det zero');
});

// ---------------------------------------------------------------- inverse and systems

test('inverse by Gauss–Jordan, with steps and singular matrices', () => {
    const A = Matrix.from([
        [2, 1],
        [1, 2],
    ]);
    assert.equal(mstr(E.matInverse(A)), '[[2/3, -1/3], [-1/3, 2/3]]');
    const s = E.matInverse(
        [
            [1, 2],
            [3, 4],
        ],
        { steps: true },
    );
    assert.equal(mstr(s.value), '[[-2, 1], [3/2, -1/2]]');
    checkSteps(s.steps, 'inverse');
    assert.equal(s.steps[0].tex.ru.startsWith('(A \\mid E)'), true);
    assert.equal(s.steps[0].tex.en.startsWith('(A \\mid I)'), true);
    assert.ok(s.steps.some((x) => x.rule === 'inverse-2x2'));
    assert.match(s.steps.at(-1).tex.ru, /= E$/);
    assert.equal(
        E.matInverse([
            [1, 2],
            [2, 4],
        ]),
        null,
    );
    const sing = E.matInverse(
        [
            [1, 2, 3],
            [4, 5, 6],
            [7, 8, 9],
        ],
        { steps: true },
    );
    assert.equal(sing.value, null);
    checkSteps(sing.steps, 'inverse singular');
    assert.match(sing.steps.at(-1).text.ru, /обратной у неё нет/);
    const r = rng(99);
    for (let t = 0; t < 40; t++) {
        const n = randInt(r, 1, 4);
        const B = randMatrix(r, n, n);
        const inv = E.matInverse(B, { steps: t % 8 === 0 });
        const value = t % 8 === 0 ? inv.value : inv;
        if (E.matDet(B).isZero()) assert.equal(value, null);
        else {
            assert.ok(B.mul(value).equals(Matrix.identity(n)), 'A·A⁻¹ = E');
            assert.ok(value.mul(B).equals(Matrix.identity(n)), 'A⁻¹·A = E');
            assert.equal(E.matDet(value).toString(), E.matDet(B).inv().toString());
        }
        if (t % 8 === 0) checkSteps(inv.steps, 'random inverse');
    }
});

test('linear systems: unique, none, infinite (Gauss) and Cramer', () => {
    const u = E.matSolve(
        [
            [2, 1],
            [1, 3],
        ],
        [3, 5],
        { steps: true, vars: ['x', 'y'] },
    );
    assert.equal(u.kind, 'unique');
    assert.deepEqual(u.x.map(String), ['4/5', '7/5']);
    assert.equal(u.tex, 'x = \\frac{4}{5},\\quad y = \\frac{7}{5}');
    checkSteps(u.steps, 'solve unique');
    const n = E.matSolve(
        [
            [1, 2],
            [2, 4],
        ],
        [3, 7],
        { steps: true },
    );
    assert.equal(n.kind, 'none');
    assert.equal(n.rank, 1);
    assert.equal(n.rankAug, 2);
    checkSteps(n.steps, 'solve none');
    assert.match(n.steps.at(-1).text.ru, /Кронекера — Капелли/);
    const inf = E.matSolve(
        [
            [1, 1, 1],
            [1, 2, 3],
        ],
        [6, 14],
        { steps: true },
    );
    assert.equal(inf.kind, 'infinite');
    assert.deepEqual(inf.params, [{ name: 't', index: 2 }]);
    assert.equal(inf.tex, 'x_{1} = -2 + t,\\quad x_{2} = 8 - 2t,\\quad x_{3} = t');
    checkSteps(inf.steps, 'solve infinite');
    assert.match(inf.steps.find((s) => s.rule === 'free-vars').text.ru, /Неизвестной x₃ ведущий элемент не достался/);
    for (const tv of [-3, 0, 1, 7]) {
        const x = inf.x.map((v, j) => v.add(inf.basis[0][j].mul(tv)));
        assert.deepEqual(
            Matrix.from([
                [1, 1, 1],
                [1, 2, 3],
            ])
                .mul(x)
                .map(String),
            ['6', '14'],
        );
    }
    const two = E.matSolve([[1, 2, 3, 4]], [10]);
    assert.equal(two.params.length, 3);
    assert.deepEqual(
        two.params.map((p) => p.name),
        ['t', 's', 'u'],
    );
    const hom = E.matSolve(
        [
            [1, -1],
            [2, -2],
        ],
        [0, 0],
    );
    assert.equal(hom.kind, 'infinite');
    assert.throws(
        () =>
            E.matSolve(
                [
                    [1, 2],
                    [3, 4],
                ],
                [1],
            ),
        (e) => e.code === 'shape',
    );
    // Sunzi-style classic: 3x + 2y - z = 1, 2x - 2y + 4z = -2, -x + y/2 - z = 0
    const c = E.matSolve(
        [
            [3, 2, -1],
            [2, -2, 4],
            [-1, '1/2', -1],
        ],
        [1, -2, 0],
    );
    assert.deepEqual(c.x.map(String), ['1', '-2', '-2']);
    const cr = E.matSolveCramer(
        [
            [2, 1],
            [1, 3],
        ],
        [3, 5],
        { steps: true },
    );
    assert.deepEqual(cr.x.map(String), ['4/5', '7/5']);
    checkSteps(cr.steps, 'cramer');
    const cs = E.matSolveCramer(
        [
            [1, 2],
            [2, 4],
        ],
        [1, 2],
        { steps: true },
    );
    assert.equal(cs.kind, 'singular');
    checkSteps(cs.steps, 'cramer singular');
    const r = rng(5);
    for (let t = 0; t < 60; t++) {
        const n = randInt(r, 1, 3);
        const A = randMatrix(r, n, n);
        const b = Array.from({ length: n }, () => randInt(r, -9, 9));
        const g = E.matSolve(A, b, { steps: t % 10 === 0 });
        const k = E.matSolveCramer(A, b);
        if (E.matDet(A).isZero()) assert.equal(k.kind, 'singular');
        else {
            assert.equal(g.kind, 'unique');
            assert.deepEqual(g.x.map(String), k.x.map(String), 'Gauss = Cramer');
            assert.deepEqual(A.mul(g.x).map(String), b.map(String));
        }
        if (g.steps) checkSteps(g.steps, 'random solve');
    }
    for (let t = 0; t < 40; t++) {
        const A = randMatrix(r, randInt(r, 1, 4), randInt(r, 1, 4), -3, 3);
        const x0 = Array.from({ length: A.cols }, () => randInt(r, -3, 3));
        const b = A.mul(x0);
        const s = E.matSolve(A, b);
        assert.notEqual(s.kind, 'none', 'a consistent system is solvable');
        assert.deepEqual(A.mul(s.x).map(String), b.map(String));
        for (const v of s.basis) assert.ok(A.mul(v).every((z) => z.isZero()));
    }
});

// ---------------------------------------------------------------- spectral

test('characteristic polynomials (Faddeev–LeVerrier) and Cayley–Hamilton', () => {
    const p2 = E.matCharPoly([
        [2, 1],
        [1, 2],
    ]);
    assert.ok(p2 instanceof E.Poly);
    assert.deepEqual(p2.c.map(String), ['3', '-4', '1']);
    const s2 = E.matCharPoly(
        [
            [2, 1],
            [1, 2],
        ],
        { steps: true },
    );
    assert.equal(s2.tex, '\\lambda^{2} - 4\\lambda + 3');
    checkSteps(s2.steps, 'charpoly 2x2');
    assert.match(s2.steps[1].tex, /\(2 - \\lambda\)\(2 - \\lambda\) - 1 \\cdot 1 = \\lambda\^\{2\} - 4\\lambda \+ 3/);
    const s3 = E.matCharPoly(
        [
            [2, 1, 1],
            [1, 2, 1],
            [1, 1, 2],
        ],
        { steps: true },
    );
    assert.equal(s3.tex, '-\\lambda^{3} + 6\\lambda^{2} - 9\\lambda + 4');
    checkSteps(s3.steps, 'charpoly 3x3');
    assert.equal(s3.steps[0].tex.ru.startsWith('\\det(A - \\lambda E)'), true);
    assert.equal(s3.steps[0].tex.en.startsWith('\\det(A - \\lambda I)'), true);
    const s4 = E.matCharPoly(
        [
            [1, 2, 0, 0],
            [0, 1, 0, 0],
            [0, 0, 3, 1],
            [0, 0, 0, 3],
        ],
        { steps: true },
    );
    assert.equal(s4.tex, '\\lambda^{4} - 8\\lambda^{3} + 22\\lambda^{2} - 24\\lambda + 9');
    checkSteps(s4.steps, 'charpoly 4x4');
    const r = rng(11);
    for (let t = 0; t < 30; t++) {
        const n = randInt(r, 1, 5);
        const A = randMatrix(r, n, n, -4, 4);
        const c = E.matCharPoly(A, { steps: true }).coefs;
        assert.ok(evalPolyAtMatrix(c, A).isZero(), `Cayley–Hamilton for ${mstr(A)}`);
        assert.equal(c[0].toString(), E.matDet(A).toString(), 'p(0) = det A');
        assert.equal(c[n].toString(), n % 2 ? '-1' : '1');
        assert.equal(c[n - 1].mul(n % 2 ? 1 : -1).toString(), A.trace().toString(), 'the λ^(n−1) coefficient is (−1)^(n−1)·trace');
    }
});

test('eigenvalues: rational, quadratic surds, complex, approximate', () => {
    const e = E.matEigen([
        [2, 1],
        [1, 2],
    ]);
    assert.deepEqual(
        e.values.map((v) => v.value.toString()),
        ['1', '3'],
    );
    assert.deepEqual(
        e.values.map((v) => v.vectors.map((x) => x.map(String))),
        [[['1', '-1']], [['1', '1']]],
    );
    for (const v of e.values)
        assert.ok(
            Matrix.from([
                [2, 1],
                [1, 2],
            ])
                .mul(v.vectors[0])
                .every((x, i) => x.eq(v.vectors[0][i].mul(v.value))),
        );
    const fib = E.matEigen([
        [1, 1],
        [1, 0],
    ]);
    assert.deepEqual(
        fib.values.map((v) => v.kind),
        ['quadratic', 'quadratic'],
    );
    assert.deepEqual(
        fib.values.map((v) => v.tex),
        ['\\frac{1 - \\sqrt{5}}{2}', '\\frac{1 + \\sqrt{5}}{2}'],
    );
    close(fib.values[1].re, (1 + Math.sqrt(5)) / 2, 1e-15);
    const phiVec = fib.values[1].vectorsApprox[0];
    close(phiVec[0] / phiVec[1], (1 + Math.sqrt(5)) / 2, 1e-12, 'golden-ratio eigenvector');
    const rot = E.matEigen([
        [0, -1],
        [1, 0],
    ]);
    assert.deepEqual(
        rot.values.map((v) => v.tex),
        ['-i', 'i'],
    );
    assert.deepEqual(
        rot.values.map((v) => v.im),
        [-1, 1],
    );
    const cplx = E.matEigen([
        [1, -2],
        [1, 1],
    ]);
    assert.deepEqual(
        cplx.values.map((v) => v.tex),
        ['1 - \\sqrt{2}\\,i', '1 + \\sqrt{2}\\,i'],
    );
    const tri = E.matEigen([
        [2, -1, 0],
        [-1, 2, -1],
        [0, -1, 2],
    ]);
    assert.deepEqual(
        tri.values.map((v) => v.tex),
        ['2 - \\sqrt{2}', '2', '2 + \\sqrt{2}'],
    );
    const rep = E.matEigen([
        [2, 1, 1],
        [1, 2, 1],
        [1, 1, 2],
    ]);
    assert.equal(rep.values[0].multiplicity, 2);
    assert.equal(rep.values[0].geometric, 2);
    assert.equal(rep.values[1].value.toString(), '4');
    const jordan = E.matEigen([
        [1, 1],
        [0, 1],
    ]);
    assert.equal(jordan.values[0].multiplicity, 2);
    assert.equal(jordan.values[0].geometric, 1);
    const cube = E.matEigen([
        [0, 0, 2],
        [1, 0, 0],
        [0, 1, 0],
    ]);
    const real = cube.values.find((v) => v.im === 0);
    assert.equal(real.kind, 'approx');
    assert.equal(real.approx, true);
    close(real.re, Math.cbrt(2), 1e-12);
    assert.match(real.tex.ru, /\\approx 1\{,\}259921/);
    assert.match(real.tex.en, /\\approx 1\.259921/);
    assert.equal(cube.values.filter((v) => v.im !== 0).length, 2);
    const quart = E.matEigen([
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 1],
        [-1, 0, 7, 0],
    ]);
    // λ⁴ − 7λ² + 1 = (λ² − 3λ + 1)(λ² + 3λ + 1): four quadratic surds
    assert.deepEqual(
        quart.values.map((v) => v.kind),
        ['quadratic', 'quadratic', 'quadratic', 'quadratic'],
    );
    assert.deepEqual(
        quart.values.map((v) => v.tex),
        ['\\frac{-3 - \\sqrt{5}}{2}', '\\frac{-3 + \\sqrt{5}}{2}', '\\frac{3 - \\sqrt{5}}{2}', '\\frac{3 + \\sqrt{5}}{2}'],
    );
    const irr = E.matEigen([
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 1],
        [-1, 0, 5, 0],
    ]);
    assert.deepEqual(
        irr.values.map((v) => v.kind),
        ['approx', 'approx', 'approx', 'approx'],
        'λ⁴ − 5λ² + 1 is irreducible over Q',
    );
    irr.values.forEach((v) => close(v.re ** 4 - 5 * v.re ** 2 + 1, 0, 1e-12));
    const sq = E.matEigen([
        [0, 2, 0, 0],
        [1, 0, 0, 0],
        [0, 0, 0, 2],
        [0, 0, 1, 0],
    ]);
    assert.deepEqual(
        sq.values.map((v) => [v.tex, v.multiplicity]),
        [
            ['-\\sqrt{2}', 2],
            ['\\sqrt{2}', 2],
        ],
    );
    const r = rng(3);
    for (let t = 0; t < 25; t++) {
        const n = randInt(r, 1, 4);
        const A = randMatrix(r, n, n, -3, 3);
        const ev = E.matEigen(A);
        const total = ev.values.reduce((s, v) => s + v.multiplicity, 0);
        assert.equal(total, n, 'multiplicities add up to n');
        let sumRe = 0,
            prodRe = 1,
            prodIm = 0;
        for (const v of ev.values)
            for (let k = 0; k < v.multiplicity; k++) {
                sumRe += v.re;
                [prodRe, prodIm] = [prodRe * v.re - prodIm * v.im, prodRe * v.im + prodIm * v.re];
            }
        close(sumRe, A.trace().toNumber(), 1e-8, 'Σλ = trace');
        close(prodRe, E.matDet(A).toNumber(), 1e-7, 'Πλ = det');
        for (const v of ev.values.filter((x) => x.kind === 'rational')) {
            for (const vec of v.vectors)
                assert.ok(
                    A.mul(vec).every((x, i) => x.eq(vec[i].mul(v.value))),
                    'A v = λ v',
                );
        }
        for (const v of ev.values.filter((x) => x.vectorsApprox)) {
            const vec = v.vectorsApprox[0];
            const Av = E.fmatMul(A.toNumbers(), vec);
            Av.forEach((x, i) => close(x, v.re * vec[i], 1e-8, 'A v ≈ λ v'));
        }
    }
});

test('eigen steps and diagonalisation', () => {
    const s = E.matEigen(
        [
            [2, 1],
            [1, 2],
        ],
        { steps: true },
    );
    checkSteps(s.steps, 'eigen 2x2');
    assert.equal(s.steps[1].tex, '(\\lambda - 1)(\\lambda - 3) = 0');
    const vs = s.steps.find((x) => x.rule === 'eigenvectors');
    assert.equal(vs.tex.ru.startsWith('(A - E)\\mathbf v = 0'), true);
    assert.equal(vs.tex.en.startsWith('(A - I)\\mathbf v = 0'), true);
    checkSteps(
        E.matEigen(
            [
                [1, 1],
                [1, 0],
            ],
            { steps: true },
        ).steps,
        'eigen fib',
    );
    checkSteps(
        E.matEigen(
            [
                [0, 0, 2],
                [1, 0, 0],
                [0, 1, 0],
            ],
            { steps: true },
        ).steps,
        'eigen approx',
    );
    const s3 = E.matEigen(
        [
            [4, 1, 0],
            [1, 4, 1],
            [0, 1, 4],
        ],
        { steps: true },
    );
    checkSteps(s3.steps, 'eigen 3x3');
    assert.match(s3.steps[1].tex, /^-\(\\lambda - 4\)\(\\lambda\^\{2\} - 8\\lambda \+ 14\) = 0$/);
    const d = E.matDiagonalize(
        [
            [2, 1, 1],
            [1, 2, 1],
            [1, 1, 2],
        ],
        { steps: true },
    );
    assert.equal(d.diagonalizable, true);
    assert.ok(
        d.P.mul(d.D)
            .mul(d.Pinv)
            .equals([
                [2, 1, 1],
                [1, 2, 1],
                [1, 1, 2],
            ]),
        'A = P D P⁻¹',
    );
    checkSteps(d.steps, 'diagonalize');
    const j = E.matDiagonalize(
        [
            [1, 1],
            [0, 1],
        ],
        { steps: true },
    );
    assert.equal(j.diagonalizable, false);
    assert.equal(j.reason, 'defective');
    checkSteps(j.steps, 'defective');
    const irr = E.matDiagonalize([
        [1, 1],
        [1, 0],
    ]);
    assert.equal(irr.reason, 'irrational');
    assert.equal(irr.overReals, true);
    const rot = E.matDiagonalize([
        [0, -1],
        [1, 0],
    ]);
    assert.equal(rot.overReals, false);
    assert.equal(rot.overComplex, true);
    const r = rng(8);
    for (let t = 0; t < 15; t++) {
        // A = P D P⁻¹ with integer P, D: always diagonalisable
        const n = randInt(r, 2, 3);
        let P;
        do {
            P = randMatrix(r, n, n, -2, 2);
        } while (E.matDet(P).isZero());
        const D = Matrix.diag(Array.from({ length: n }, () => randInt(r, -3, 3)));
        const A = P.mul(D).mul(E.matInverse(P));
        const dg = E.matDiagonalize(A);
        assert.equal(dg.diagonalizable, true, `diagonalisable ${mstr(A)}`);
        assert.ok(dg.P.mul(dg.D).mul(dg.Pinv).equals(A));
    }
});

test('matrix powers: Fibonacci, negative powers', () => {
    const F = Matrix.from([
        [1, 1],
        [1, 0],
    ]);
    assert.equal(mstr(E.matPower(F, 10)), '[[89, 55], [55, 34]]');
    assert.equal(mstr(E.matPower(F, 0)), '[[1, 0], [0, 1]]');
    const fib = [0n, 1n];
    for (let i = 2; i <= 101; i++) fib.push(fib[i - 1] + fib[i - 2]);
    for (const n of [1, 2, 5, 30, 90, 100]) {
        const P = F.pow(n);
        assert.equal(P.get(0, 1).n, fib[n], `F(${n})`);
        assert.equal(P.get(0, 0).n, fib[n + 1]);
    }
    assert.equal(mstr(E.matPower(F, -1)), '[[0, 1], [1, -1]]');
    assert.ok(E.matPower(F, -5).mul(E.matPower(F, 5)).equals(Matrix.identity(2)));
    assert.equal(
        mstr(
            E.matPower(
                [
                    [2, 0],
                    [0, '1/2'],
                ],
                3,
            ),
        ),
        '[[8, 0], [0, 1/8]]',
    );
    assert.throws(
        () =>
            E.matPower(
                [
                    [1, 2],
                    [2, 4],
                ],
                -1,
            ),
        (e) => e.code === 'singular',
    );
});

test('orthogonality: Gram–Schmidt, projections, least squares', () => {
    const g = E.matGramSchmidt(
        [
            [1, 1, 0],
            [1, 0, 1],
            [0, 1, 1],
        ],
        { steps: true },
    );
    assert.deepEqual(
        g.orthogonal.map((v) => v.map(String)),
        [
            ['1', '1', '0'],
            ['1/2', '-1/2', '1'],
            ['-2/3', '2/3', '2/3'],
        ],
    );
    const dot = (u, v) => u.reduce((s, x, i) => s.add(x.mul(v[i])), Q.ZERO);
    for (let i = 0; i < 3; i++) for (let j = i + 1; j < 3; j++) assert.ok(dot(g.orthogonal[i], g.orthogonal[j]).isZero());
    for (const u of g.normalized) close(Math.hypot(...u), 1, 1e-15);
    checkSteps(g.steps, 'gram-schmidt');
    const dep = E.matGramSchmidt(
        [
            [1, 2],
            [2, 4],
            [0, 1],
        ],
        { steps: true },
    );
    assert.deepEqual(dep.dropped, [1]);
    assert.equal(dep.orthogonal.length, 2);
    checkSteps(dep.steps, 'gram-schmidt dependent');
    assert.deepEqual(E.matProjection([1, 2, 3], [1, 1, 1]).map(String), ['2', '2', '2']);
    assert.deepEqual(
        E.matProjection(
            [1, 2, 3],
            [
                [1, 0, 0],
                [0, 1, 0],
            ],
        ).map(String),
        ['1', '2', '0'],
    );
    assert.deepEqual(E.matProjection([3, 4], [1, 0]).map(String), ['3', '0']);
    const ls = E.matLeastSquares(
        [
            [1, 1],
            [1, 2],
            [1, 3],
            [1, 4],
        ],
        [6, 5, 7, 10],
        { steps: true },
    );
    assert.equal(ls.kind, 'unique');
    assert.deepEqual(ls.x.map(String), ['7/2', '7/5']);
    const reg = E.statLinearRegression([
        [1, 6],
        [2, 5],
        [3, 7],
        [4, 10],
    ]);
    close(ls.x[1].toNumber(), reg.a, 1e-14, 'slope matches regression');
    close(ls.x[0].toNumber(), reg.b, 1e-14);
    const At = Matrix.from([
        [1, 1],
        [1, 2],
        [1, 3],
        [1, 4],
    ]).transpose();
    assert.ok(
        At.mul(ls.residual).every((x) => x.isZero()),
        'residual ⟂ columns',
    );
    checkSteps(ls.steps, 'least squares');
});

// ---------------------------------------------------------------- float toolkit

test('float toolkit: products, inverses, solves', () => {
    assert.deepEqual(
        E.fmatMul(
            [
                [1, 2],
                [3, 4],
            ],
            [
                [5, 6],
                [7, 8],
            ],
        ),
        [
            [19, 22],
            [43, 50],
        ],
    );
    assert.deepEqual(
        E.fmatMul(
            [
                [1, 2],
                [3, 4],
            ],
            [1, 1],
        ),
        [3, 7],
    );
    assert.deepEqual(E.fmatTranspose([[1, 2, 3]]), [[1], [2], [3]]);
    const inv = E.fmatInv([
        [4, 7],
        [2, 6],
    ]);
    [
        [0.6, -0.7],
        [-0.2, 0.4],
    ].forEach((row, i) => row.forEach((v, j) => close(inv[i][j], v, 1e-14)));
    assert.equal(
        E.fmatInv([
            [1, 2],
            [2, 4],
        ]),
        null,
    );
    assert.deepEqual(
        E.fmatSolve(
            [
                [1, 1],
                [1, -1],
            ],
            [3, 1],
        ),
        [2, 1],
    );
    const r = rng(21);
    for (let t = 0; t < 20; t++) {
        const n = randInt(r, 2, 8);
        const A = Array.from({ length: n }, () => Array.from({ length: n }, () => r() * 2 - 1));
        const Ai = E.fmatInv(A);
        const I = E.fmatMul(A, Ai);
        I.forEach((row, i) => row.forEach((v, j) => close(v, i === j ? 1 : 0, 1e-9)));
    }
});

test('float toolkit: symmetric eigen (Jacobi), SVD, truncated SVD, QR', () => {
    const es = E.fmatEigSym([
        [2, 1],
        [1, 2],
    ]);
    close(es.values[0], 3, 1e-14);
    close(es.values[1], 1, 1e-14);
    close(Math.abs(es.vectors[0][0]), Math.SQRT1_2, 1e-14);
    const r = rng(77);
    for (let t = 0; t < 10; t++) {
        const n = randInt(r, 2, 9);
        const B = Array.from({ length: n }, () => Array.from({ length: n }, () => r() * 2 - 1));
        const S = E.fmatMul(B, E.fmatTranspose(B));
        const { values, vectors } = E.fmatEigSym(S);
        for (let k = 1; k < n; k++) assert.ok(values[k - 1] >= values[k], 'descending');
        vectors.forEach((v, k) => E.fmatMul(S, v).forEach((x, i) => close(x, values[k] * v[i], 1e-9, 'S v = λ v')));
        const exact = E.matEigen(
            Matrix.from([
                [2, 1],
                [1, 2],
            ]),
        );
        assert.equal(exact.values.length, 2);
    }
    const A = [
        [3, 1, 1],
        [-1, 3, 1],
    ];
    const svd = E.fmatSvd(A);
    close(svd.S[0], Math.sqrt(12), 1e-13);
    close(svd.S[1], Math.sqrt(10), 1e-13);
    const back = E.fmatLowRank(svd);
    A.forEach((row, i) => row.forEach((v, j) => close(back[i][j], v, 1e-13)));
    for (let t = 0; t < 5; t++) {
        const m = randInt(r, 3, 30),
            n = randInt(r, 2, 20);
        const X = Array.from({ length: m }, () => Array.from({ length: n }, () => r() * 2 - 1));
        const d = E.fmatSvd(X);
        const rec = E.fmatLowRank(d);
        X.forEach((row, i) => row.forEach((v, j) => close(rec[i][j], v, 1e-10, 'U S Vᵀ = A')));
        const k = Math.min(m, n);
        for (let a = 0; a < k; a++)
            for (let b = 0; b < k; b++) {
                const uu = d.U.reduce((s, row) => s + row[a] * row[b], 0);
                const vv = d.V.reduce((s, row) => s + row[a] * row[b], 0);
                close(uu, a === b ? 1 : 0, 1e-10, 'UᵀU = I');
                close(vv, a === b ? 1 : 0, 1e-10, 'VᵀV = I');
            }
    }
    // an "image": rank-3 structure plus a little noise, 120×100
    const img = Array.from({ length: 120 }, (_, i) =>
        Array.from(
            { length: 100 },
            (_, j) => Math.sin(i / 7) * Math.cos(j / 9) + 0.5 * Math.sin((i + j) / 13) + 0.2 * (((i * 7 + j * 3) % 11) / 11 - 0.5) + (i > 60 && j < 40 ? 1 : 0),
        ),
    );
    const full = E.fmatSvd(img);
    const tr = E.fmatSvdTruncated(img, 8, { powerIters: 3 });
    assert.equal(tr.S.length, 8);
    for (let k = 0; k < 5; k++) close(tr.S[k], full.S[k], 1e-6, `σ${k + 1}`);
    const approx = E.fmatLowRank(tr);
    const bestErr = Math.sqrt(full.S.slice(8).reduce((s, x) => s + x * x, 0));
    let err = 0;
    img.forEach((row, i) =>
        row.forEach((v, j) => {
            err += (approx[i][j] - v) ** 2;
        }),
    );
    assert.ok(Math.sqrt(err) < bestErr * 1.05, 'randomised SVD is near the optimal rank-8 error');
    const { Q: Qm, R: Rm } = E.fmatQr([
        [1, 2],
        [3, 4],
        [5, 6],
    ]);
    const QR = E.fmatMul(Qm, Rm);
    [
        [1, 2],
        [3, 4],
        [5, 6],
    ].forEach((row, i) => row.forEach((v, j) => close(QR[i][j], v, 1e-13)));
    assert.equal(Rm[1][0], 0);
    for (let a = 0; a < 2; a++)
        for (let b = 0; b < 2; b++)
            close(
                Qm.reduce((s, row) => s + row[a] * row[b], 0),
                a === b ? 1 : 0,
                1e-14,
            );
    const wide = E.fmatQr([
        [1, 2, 3],
        [4, 5, 6],
    ]);
    const W2 = E.fmatMul(wide.Q, wide.R);
    [
        [1, 2, 3],
        [4, 5, 6],
    ].forEach((row, i) => row.forEach((v, j) => close(W2[i][j], v, 1e-13)));
});

test('exported matrix names', () => {
    for (const name of [
        'Matrix',
        'matRref',
        'matRank',
        'matNullspace',
        'matDet',
        'matInverse',
        'matSolve',
        'matSolveCramer',
        'matCharPoly',
        'matEigen',
        'matDiagonalize',
        'matPower',
        'matGramSchmidt',
        'matProjection',
        'matLeastSquares',
        'fmatMul',
        'fmatTranspose',
        'fmatSolve',
        'fmatInv',
        'fmatEigSym',
        'fmatSvd',
        'fmatSvdTruncated',
        'fmatLowRank',
        'fmatQr',
    ]) {
        assert.equal(typeof E[name], 'function', name);
    }
});
