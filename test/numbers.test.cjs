// tests/Js/math-engine-numbers.test.cjs — number theory (numtheory.js) and numerical methods (numeric.js)
const { test, before } = require('node:test');
const assert = require('node:assert/strict');

let E;
before(async () => {
    E = await import('../src/index.js');
});

// ---------------------------------------------------------------- helpers

const close = (a, b, tol = 1e-9, msg) => {
    const ok = Math.abs(a - b) <= tol * Math.max(1, Math.abs(b));
    assert.ok(ok, `${msg ?? ''} expected ${b}, got ${a} (tol ${tol})`);
};
/** Every step: bilingual title, tex string or {ru, en}, bilingual text; recursively. */
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
                assert.ok(!/undefined|NaN|\[object/.test(t), `${where}: bad tex ${t}`);
                let depth = 0;
                for (const ch of t.replace(/\\[{}]/g, '')) {
                    if (ch === '{') depth++;
                    if (ch === '}') depth--;
                    assert.ok(depth >= 0, `${where}: braces in ${t}`);
                }
                assert.equal(depth, 0, `${where}: unbalanced braces in ${t}`);
            }
        }
        if (s.text !== undefined) {
            assert.equal(typeof s.text.ru, 'string', `${where}: text.ru`);
            assert.equal(typeof s.text.en, 'string', `${where}: text.en`);
            assert.ok(!/undefined|NaN|\[object/.test(s.text.ru + s.text.en), `${where}: bad text ${s.text.ru}`);
            assert.ok(/[а-яё]/i.test(s.text.ru) || !/[a-z]{4}/i.test(s.text.ru), `${where}: RU text looks English: ${s.text.ru}`);
        }
        if (s.sub) checkSteps(s.sub, where + ' > ' + s.title.en);
    }
}
function* pairs(n, seed = 1) {
    let s = seed;
    const rnd = () => (s = (s * 1103515245 + 12345) % 2147483648) / 2147483648;
    for (let i = 0; i < n; i++) yield [Math.floor(rnd() * 5000) - 1000, Math.floor(rnd() * 5000) - 1000];
}
const bruteGcd = (a, b) => {
    a = Math.abs(a);
    b = Math.abs(b);
    while (b) [a, b] = [b, a % b];
    return a;
};

// ---------------------------------------------------------------- gcd / lcm / Bézout

test('gcd(1071, 462) = 21 with the Euclid table', () => {
    assert.equal(E.ntGcd(1071, 462), 21n);
    const r = E.ntGcd(1071n, 462n, { steps: true });
    assert.equal(r.value, 21n);
    assert.deepEqual(
        r.rows.map((x) => [x.a, x.b, x.q, x.r]),
        [
            [1071n, 462n, 2n, 147n],
            [462n, 147n, 3n, 21n],
            [147n, 21n, 7n, 0n],
        ],
    );
    checkSteps(r.steps, 'gcd');
    assert.match(r.steps[1].title.ru, /Делим 1071 на 462/);
    assert.match(r.steps[1].text.ru, /Получаем 2, остаток 147/);
    assert.equal(r.steps[1].tex, '1071 = 2 \\cdot 462 + 147');
    assert.match(r.steps.at(-1).tex.ru, /\\text\{НОД\}\(1071,\\,462\) = 21/);
    assert.match(r.steps.at(-1).tex.en, /\\gcd\(1071, 462\) = 21/);
});

test('gcd edge cases and inputs', () => {
    assert.equal(E.ntGcd(0, 0), 0n);
    assert.equal(E.ntGcd(0, 7), 7n);
    assert.equal(E.ntGcd(-12, 18), 6n);
    assert.equal(E.ntGcd('600 851 475 143', 71), 71n);
    assert.equal(E.ntGcd(E.Q.of(12), 8), 4n);
    assert.equal(E.ntGcd(2n ** 100n, 6n ** 50n), 2n ** 50n);
    checkSteps(E.ntGcd(0, 0, { steps: true }).steps, 'gcd00');
    checkSteps(E.ntGcd(-12, 0, { steps: true }).steps, 'gcd-12,0');
    checkSteps(E.ntGcd(462, 1071, { steps: true }).steps, 'gcd swapped');
    assert.throws(
        () => E.ntGcd(1.5, 2),
        (e) => e.name === 'MathError' && /целое/.test(e.msg.ru),
    );
    assert.throws(() => E.ntGcd('abc', 2), /not an integer/);
    for (const [a, b] of pairs(150, 7)) assert.equal(E.ntGcd(a, b), BigInt(bruteGcd(a, b)), `gcd(${a}, ${b})`);
});

test('lcm and lists', () => {
    assert.equal(E.ntLcm(4, 6), 12n);
    assert.equal(E.ntLcm(-4, 6), 12n);
    assert.equal(E.ntLcm(0, 5), 0n);
    assert.equal(E.ntLcm(21, 6), 42n);
    const r = E.ntLcm(12, 18, { steps: true });
    assert.equal(r.value, 36n);
    checkSteps(r.steps, 'lcm');
    assert.ok(r.steps.some((s) => s.rule === 'lcm-factor' && /2\^\{2\} \\cdot 3\^\{2\}/.test(s.tex.ru)));
    checkSteps(E.ntLcm(0, 3, { steps: true }).steps, 'lcm0');
    assert.equal(E.ntGcdMany([12, 18, 24]), 6n);
    assert.equal(E.ntGcdMany(12, 18, 27), 3n);
    assert.equal(E.ntLcmMany([2, 3, 4, 5, 6]), 60n);
    assert.equal(E.ntLcmMany(1, 2, 3, 4, 5, 6, 7, 8, 9, 10), 2520n);
    const m = E.ntGcdMany([84, 126, 210], { steps: true });
    assert.equal(m.value, 42n);
    checkSteps(m.steps, 'gcdMany');
    const l = E.ntLcmMany([4, 6, 10], { steps: true });
    assert.equal(l.value, 60n);
    checkSteps(l.steps, 'lcmMany');
    for (const [a, b] of pairs(100, 11)) {
        if (!a || !b) continue;
        assert.equal(E.ntLcm(a, b) * E.ntGcd(a, b), BigInt(Math.abs(a * b)), `lcm·gcd for ${a}, ${b}`);
    }
});

test('extended Euclid with back-substitution', () => {
    const r = E.ntEgcd(1071, 462, { steps: true });
    assert.deepEqual([r.g, r.x, r.y], [21n, -3n, 7n]);
    checkSteps(r.steps, 'egcd');
    const sub = r.steps.find((s) => /Подставляем 147/.test(s.title.ru));
    assert.ok(sub, 'substitution step');
    assert.equal(sub.tex, '21 = 462 - 3 \\cdot 147 = 462 - 3 \\cdot (1071 - 2 \\cdot 462) = -3 \\cdot 1071 + 7 \\cdot 462');
    assert.match(r.steps.at(-1).tex, /1071 \\cdot \(-3\) \+ 462 \\cdot 7 = -3213 \+ 3234 = 21/);
    for (const [a, b] of pairs(200, 3)) {
        const e = E.ntEgcd(a, b);
        assert.equal(BigInt(a) * e.x + BigInt(b) * e.y, e.g, `bezout ${a}, ${b}`);
        assert.equal(e.g, BigInt(bruteGcd(a, b)));
    }
    for (const [a, b] of [
        [240, 46],
        [-240, 46],
        [17, 0],
        [0, -5],
        [5, 25],
        [0, 0],
        [1, 1],
        [-7, -21],
    ]) {
        const e = E.ntEgcd(a, b, { steps: true });
        assert.equal(BigInt(a) * e.x + BigInt(b) * e.y, e.g);
        checkSteps(e.steps, `egcd ${a},${b}`);
    }
});

test('linear Diophantine equations', () => {
    const r = E.ntDiophantine(3, 5, 7, { steps: true });
    assert.equal(r.solvable, true);
    assert.equal(r.x0, 4n);
    assert.equal(r.y0, -1n);
    assert.equal(3n * r.x0 + 5n * r.y0, 7n);
    checkSteps(r.steps, 'dioph');
    const no = E.ntDiophantine(6, 9, 7, { steps: true });
    assert.equal(no.solvable, false);
    checkSteps(no.steps, 'dioph none');
    for (const [a, b] of pairs(60, 5)) {
        const c = (a * 3 + b * 7) % 1000;
        const d = E.ntDiophantine(a, b, c);
        const g = bruteGcd(a, b);
        if (g === 0) continue;
        assert.equal(d.solvable, c % g === 0);
        if (d.solvable) {
            for (const k of [-2n, 0n, 3n]) assert.equal(BigInt(a) * (d.x0 + d.dx * k) + BigInt(b) * (d.y0 + d.dy * k), BigInt(c));
        }
    }
});

// ---------------------------------------------------------------- primes and factorisation

test('primality: sieve agreement, Carmichael numbers, big primes', () => {
    const primes = E.ntPrimesUpTo(20000);
    assert.equal(primes.length, 2262);
    const set = new Set(primes);
    for (let n = -5; n <= 20000; n++) if (n < 200 || n % 7 === 0 || set.has(n)) assert.equal(E.ntIsPrime(n), set.has(n), `isPrime(${n})`);
    for (const c of [561, 1105, 1729, 2465, 2821, 6601, 8911, 41041, 825265, 321197185]) {
        assert.equal(E.ntIsPrime(c), false, `${c} composite`);
        assert.equal(E.ntIsCarmichael(c), true, `${c} Carmichael`);
    }
    assert.equal(E.ntIsCarmichael(563), false);
    assert.equal(E.ntIsCarmichael(560), false);
    // strong pseudoprimes to base 2 and the classic hard composite
    for (const c of [2047n, 3215031751n, 3825123056546413051n, 318665857834031151167461n, 3317044064679887385961981n])
        assert.equal(E.ntIsPrime(c), false, `${c}`);
    for (const p of [1000000007n, 2n ** 61n - 1n, 2n ** 89n - 1n, 2n ** 127n - 1n, 18446744073709551557n]) assert.equal(E.ntIsPrime(p), true, `${p} prime`);
    assert.equal(E.ntIsPrime(2n ** 128n + 1n), false);
    assert.equal(E.ntIsPrime((2n ** 61n - 1n) * (2n ** 31n - 1n)), false);
});

test('Miller–Rabin in detail: 561 exposed by base 2', () => {
    const r = E.ntMillerRabin(561, { steps: true });
    assert.equal(r.prime, false);
    assert.equal(r.witness, 2n);
    assert.equal(r.s, 4);
    assert.equal(r.d, 35n);
    assert.deepEqual(r.rounds[0].seq, [263n, 166n, 67n, 1n]);
    checkSteps(r.steps, 'MR 561');
    assert.match(r.steps[1].text.ru, /67/);
    const p = E.ntMillerRabin(97, { steps: true });
    assert.equal(p.prime, true);
    assert.equal(p.certain, true);
    checkSteps(p.steps, 'MR 97');
    const big = E.ntMillerRabin(2n ** 127n - 1n);
    assert.equal(big.prime, true);
    assert.equal(big.certain, false);
    const onlyBase2 = E.ntMillerRabin(2047, { bases: [2] });
    assert.equal(onlyBase2.prime, true, '2047 = 23·89 is a strong pseudoprime to base 2');
    assert.equal(onlyBase2.certain, false);
    for (const n of [0, 1, 2, 3, 4, 10]) checkSteps(E.ntMillerRabin(n, { steps: true }).steps, `MR ${n}`);
});

test('factorisation: Project Euler 3, ladders, Pollard rho', () => {
    assert.deepEqual(E.ntFactor(600851475143), [
        { p: 71n, e: 1 },
        { p: 839n, e: 1 },
        { p: 1471n, e: 1 },
        { p: 6857n, e: 1 },
    ]);
    const r = E.ntFactor(600851475143n, { steps: true });
    checkSteps(r.steps, 'factor PE3');
    assert.equal(r.tex, '71 \\cdot 839 \\cdot 1471 \\cdot 6857');
    assert.deepEqual(
        r.ladder.map((x) => x.p),
        [71n, 839n, 1471n, 6857n],
    );
    assert.ok(r.steps.some((s) => s.rule === 'sqrt-bound'));
    const s = E.ntFactor(360, { steps: true });
    assert.equal(s.tex, '2^{3} \\cdot 3^{2} \\cdot 5');
    assert.deepEqual(
        s.ladder.map((x) => [x.n, x.p]),
        [
            [360n, 2n],
            [180n, 2n],
            [90n, 2n],
            [45n, 3n],
            [15n, 3n],
            [5n, 5n],
        ],
    );
    checkSteps(s.steps, 'factor 360');
    assert.match(s.steps.find((x) => x.rule === 'divide').text.ru, /последняя цифра чётная/);
    assert.deepEqual(E.ntFactor(1), []);
    assert.deepEqual(E.ntFactor(-12), [
        { p: 2n, e: 2 },
        { p: 3n, e: 1 },
    ]);
    assert.deepEqual(E.ntFactor(97), [{ p: 97n, e: 1 }]);
    assert.throws(
        () => E.ntFactor(0),
        (e) => e.name === 'MathError',
    );
    // large: rho and prime powers
    assert.deepEqual(E.ntFactor(1000000016000000063n), [
        { p: 1000000007n, e: 1 },
        { p: 1000000009n, e: 1 },
    ]);
    assert.deepEqual(E.ntFactor(2n ** 64n + 1n), [
        { p: 274177n, e: 1 },
        { p: 67280421310721n, e: 1 },
    ]);
    assert.deepEqual(E.ntFactor(1000003n ** 3n * 999983n), [
        { p: 999983n, e: 1 },
        { p: 1000003n, e: 3 },
    ]);
    assert.deepEqual(E.ntFactor(2n ** 100n), [{ p: 2n, e: 100 }]);
    const big = E.ntFactor(1000000016000000063n, { steps: true });
    checkSteps(big.steps, 'factor rho');
    assert.ok(big.steps.some((x) => x.rule === 'pollard-rho'));
    checkSteps(E.ntFactor(1000000007, { steps: true }).steps, 'factor big prime');
    checkSteps(E.ntFactor(-(2n ** 20n), { steps: true }).steps, 'factor power');
    checkSteps(E.ntFactor(1, { steps: true }).steps, 'factor 1');
    // products reassemble
    for (let n = 2; n < 3000; n += 7) {
        const f = E.ntFactor(n);
        assert.equal(
            f.reduce((acc, { p, e }) => acc * p ** BigInt(e), 1n),
            BigInt(n),
        );
        assert.ok(f.every(({ p }) => E.ntIsPrime(p)));
    }
    assert.equal(E.ntFactorTex([]), '1');
});

test('divisors, τ, σ, φ, μ', () => {
    assert.deepEqual(E.ntDivisors(28), [1n, 2n, 4n, 7n, 14n, 28n]);
    assert.equal(E.ntSigma(28), 56n, '28 is perfect');
    assert.equal(E.ntSigma(496) - 496n, 496n);
    assert.equal(E.ntTau(360), 24n);
    assert.equal(E.ntSigma(12, 0), 6n);
    assert.equal(E.ntSigma(10, 2), 1n + 4n + 25n + 100n);
    assert.equal(E.ntPhi(36), 12n);
    assert.equal(E.ntPhi(1), 1n);
    assert.equal(E.ntPhi(97), 96n);
    assert.equal(E.ntPhi(2n ** 20n), 2n ** 19n);
    assert.equal(E.ntMobius(30), -1);
    assert.equal(E.ntMobius(12), 0);
    assert.equal(E.ntMobius(1), 1);
    const r = E.ntPhi(36, { steps: true });
    assert.equal(r.value, 12n);
    checkSteps(r.steps, 'phi 36');
    assert.ok(r.steps.some((s) => /\\varphi\(36\) = 36 \\left\(1 - \\frac\{1\}\{2\}\\right\)/.test(s.tex)));
    assert.match(r.steps.at(-1).text.ru, /их 12/);
    checkSteps(E.ntPhi(1, { steps: true }).steps, 'phi 1');
    checkSteps(E.ntPhi(13, { steps: true }).steps, 'phi 13');
    for (let n = 1; n <= 300; n++) {
        let c = 0;
        for (let k = 1; k <= n; k++) if (bruteGcd(k, n) === 1) c++;
        assert.equal(E.ntPhi(n), BigInt(c), `phi(${n})`);
        const divs = E.ntDivisors(n);
        assert.equal(BigInt(divs.length), E.ntTau(n));
        assert.equal(
            divs.reduce((a, b) => a + b, 0n),
            E.ntSigma(n),
        );
    }
    assert.throws(() => E.ntPhi(0));
});

test('prime counting, sieve, next/previous prime', () => {
    assert.equal(E.ntPrimePi(10), 4);
    assert.equal(E.ntPrimePi(100), 25);
    assert.equal(E.ntPrimePi(1e6), 78498);
    assert.equal(E.ntPrimePi(1e7), 664579);
    assert.equal(E.ntPrimePi(1e8), 5761455);
    assert.equal(E.ntPrimePi(1), 0);
    assert.equal(E.ntPrimesUpTo(30).join(','), '2,3,5,7,11,13,17,19,23,29');
    assert.deepEqual(E.ntPrimesUpTo(1), []);
    const s = E.ntSieve(100);
    assert.equal(s.primes.length, 25);
    assert.equal(s.spf[91], 7);
    assert.equal(s.spf[97], 97);
    assert.equal(s.isPrime[89], 1);
    assert.equal(s.isPrime[91], 0);
    assert.equal(E.ntNextPrime(1), 2n);
    assert.equal(E.ntNextPrime(2), 3n);
    assert.equal(E.ntNextPrime(13), 17n);
    assert.equal(E.ntNextPrime(1000000000), 1000000007n);
    assert.equal(E.ntPrevPrime(2), null);
    assert.equal(E.ntPrevPrime(3), 2n);
    assert.equal(E.ntPrevPrime(100), 97n);
    assert.equal(E.ntIsPerfectSquare(144), true);
    assert.equal(E.ntIsPerfectSquare(145), false);
    assert.equal(E.ntIsPerfectSquare(-4), false);
    assert.equal(E.ntIsPerfectSquare(10n ** 40n), true);
    assert.equal(E.ntDigitSum(1234), 10n);
    assert.equal(E.ntDigitSum(255, 2), 8n);
    assert.equal(E.ntDigitSum(-99), 18n);
});

// ---------------------------------------------------------------- modular arithmetic

test('modular power: 2^100 mod 13 and the squaring table', () => {
    assert.equal(E.ntModPow(2, 100, 13), 3n);
    const r = E.ntModPow(2, 100, 13, { steps: true });
    assert.equal(r.value, 3n);
    checkSteps(r.steps, 'modpow');
    assert.deepEqual(
        r.rows.map((x) => x.value),
        [2n, 4n, 3n, 9n, 3n, 9n, 3n],
    );
    assert.deepEqual(
        r.rows.filter((x) => x.bit).map((x) => x.k),
        [2, 5, 6],
    );
    assert.equal(r.steps[0].tex, '100 = 1100100_2 = 64 + 32 + 4');
    assert.ok(r.steps.some((s) => s.rule === 'fermat'));
    assert.equal(E.ntModPow(3, 0, 7), 1n);
    assert.equal(E.ntModPow(5, 3, 1), 0n);
    assert.equal(E.ntModPow(-2, 3, 7), 6n);
    assert.equal(E.ntModPow(3, -1, 7), 5n);
    assert.equal(E.ntModPow(2, -1, 4), null);
    checkSteps(E.ntModPow(3, -2, 7, { steps: true }).steps, 'modpow negative');
    checkSteps(E.ntModPow(4, 13, 497, { steps: true }).steps, 'modpow 4^13');
    assert.equal(E.ntModPow(4, 13, 497), 445n);
    checkSteps(E.ntModPow(7, 0, 5, { steps: true }).steps, 'modpow e=0');
    checkSteps(E.ntModPow(7, 5, 1, { steps: true }).steps, 'modpow m=1');
    for (let a = -5; a < 12; a++)
        for (let e = 0; e < 30; e += 3)
            for (const m of [1, 2, 7, 12, 97]) {
                const expect = ((BigInt(a) ** BigInt(e) % BigInt(m)) + BigInt(m)) % BigInt(m);
                assert.equal(E.ntModPow(a, e, m), expect, `${a}^${e} mod ${m}`);
            }
    assert.throws(
        () => E.ntModPow(2, 3, 0),
        (e) => e.name === 'MathError',
    );
});

test('modular inverse, linear congruences, order and primitive roots', () => {
    assert.equal(E.ntModInv(3, 7), 5n);
    assert.equal(E.ntModInv(7, 40), 23n);
    assert.equal(E.ntModInv(-3, 7), 2n);
    assert.equal(E.ntModInv(4, 6), null);
    const inv = E.ntModInv(7, 40, { steps: true });
    assert.equal(inv.value, 23n);
    checkSteps(inv.steps, 'modinv');
    checkSteps(E.ntModInv(4, 6, { steps: true }).steps, 'modinv none');
    for (let m = 2; m < 60; m++)
        for (let a = 0; a < m; a++) {
            const v = E.ntModInv(a, m);
            if (bruteGcd(a, m) === 1) assert.equal((BigInt(a) * v) % BigInt(m), 1n % BigInt(m));
            else assert.equal(v, null);
        }
    const c = E.ntSolveCongruence(6, 4, 10, { steps: true });
    assert.equal(c.solvable, true);
    assert.equal(c.d, 2n);
    assert.deepEqual(c.solutions, [4n, 9n]);
    checkSteps(c.steps, 'congruence');
    assert.match(c.steps.at(-1).title.ru, /2 решения по модулю 10/);
    const none = E.ntSolveCongruence(6, 5, 10, { steps: true });
    assert.equal(none.solvable, false);
    checkSteps(none.steps, 'congruence none');
    const all = E.ntSolveCongruence(0, 0, 5, { steps: true });
    assert.deepEqual(all.solutions, [0n, 1n, 2n, 3n, 4n]);
    checkSteps(all.steps, 'congruence all');
    checkSteps(E.ntSolveCongruence(3, 2, 7, { steps: true }).steps, 'congruence unique');
    for (let m = 1; m < 30; m++)
        for (let a = -3; a < m; a += 2)
            for (let b = 0; b < m; b += 3) {
                const r = E.ntSolveCongruence(a, b, m);
                const brute = [];
                for (let x = 0; x < m; x++) if ((((a * x - b) % m) + m) % m === 0) brute.push(BigInt(x));
                assert.deepEqual(r.solvable ? r.solutions : [], brute, `${a}x ≡ ${b} mod ${m}`);
            }
    assert.equal(E.ntOrder(2, 7), 3n);
    assert.equal(E.ntOrder(3, 7), 6n);
    assert.equal(E.ntOrder(2, 6), null);
    assert.equal(E.ntOrder(10, 7), 6n);
    assert.equal(E.ntPrimitiveRoot(7), 3n);
    assert.equal(E.ntPrimitiveRoot(23), 5n);
    assert.equal(E.ntPrimitiveRoot(8), null);
    assert.equal(E.ntPrimitiveRoot(18), 5n);
    assert.equal(E.ntPrimitiveRoot(2), 1n);
});

test('Chinese remainder theorem: Sunzi, non-coprime moduli, conflicts', () => {
    assert.deepEqual(E.ntCrt([2, 3, 2], [3, 5, 7]), { solvable: true, x: 23n, m: 105n });
    const r = E.ntCrt([2, 3, 2], [3, 5, 7], { steps: true });
    checkSteps(r.steps, 'crt');
    assert.ok(r.steps.some((s) => /x = 8 \+ 15\(1 \+ 7u\) = 23 \+ 105u/.test(s.tex)));
    assert.deepEqual(E.ntCrt([3, 5], [4, 6]), { solvable: true, x: 11n, m: 12n });
    const bad = E.ntCrt([1, 2], [4, 6], { steps: true });
    assert.equal(bad.solvable, false);
    checkSteps(bad.steps, 'crt conflict');
    checkSteps(E.ntCrt([3, 5], [4, 6], { steps: true }).steps, 'crt noncoprime');
    checkSteps(E.ntCrt([10, 20, 5], [17, 31, 97], { steps: true }).steps, 'crt bigger moduli');
    assert.deepEqual(E.ntCrt([7], [10]), { solvable: true, x: 7n, m: 10n });
    for (let i = 0; i < 80; i++) {
        const ms = [3 + (i % 5), 4 + ((i * 7) % 9), 5 + ((i * 3) % 11)];
        const x = (i * 37) % 997;
        const rs = ms.map((m) => x % m);
        const c = E.ntCrt(rs, ms);
        assert.equal(c.solvable, true);
        ms.forEach((m, k) => assert.equal(c.x % BigInt(m), BigInt(rs[k])));
        assert.equal(c.m, E.ntLcmMany(ms));
    }
    assert.throws(
        () => E.ntCrt([1, 2], [3]),
        (e) => e.name === 'MathError',
    );
});

test('toy RSA: encrypt then decrypt', () => {
    const k = E.ntRsaKey(61, 53, { e: 17, steps: true });
    assert.equal(k.n, 3233n);
    assert.equal(k.phi, 3120n);
    assert.equal(k.d, 2753n);
    checkSteps(k.steps, 'rsa');
    const c = E.ntModPow(65, k.e, k.n);
    assert.equal(c, 2790n);
    assert.equal(E.ntModPow(c, k.d, k.n), 65n);
    const k2 = E.ntRsaKey(1000003n, 1000033n);
    assert.equal(k2.e, 65537n);
    for (const m of [0n, 1n, 42n, 123456789n]) assert.equal(E.ntModPow(E.ntModPow(m, k2.e, k2.n), k2.d, k2.n), m);
    assert.equal(E.ntRsaKey(11, 13).e, 7n, 'falls back to the smallest valid odd e');
    assert.throws(() => E.ntRsaKey(10, 13));
});

// ---------------------------------------------------------------- number bases

test('bases: integers, fractions with periods, letters, signs', () => {
    assert.equal(E.ntToBase(25, 2), '11001');
    assert.equal(E.ntToBase(255, 16), 'FF');
    assert.equal(E.ntToBase(0, 7), '0');
    assert.equal(E.ntToBase(-2748, 16), '-ABC');
    assert.equal(E.ntToBase('0.1', 2), '0.0(0011)');
    assert.equal(E.ntToBase('0,1', 2), '0.0(0011)');
    assert.equal(E.ntToBase(0.1, 2), '0.0(0011)');
    assert.equal(E.ntToBase('1/3', 2), '0.(01)');
    assert.equal(E.ntToBase('1/3', 3), '0.1');
    assert.equal(E.ntToBase('-5.75', 2), '-101.11');
    assert.equal(E.ntToBase('26.5', 16), '1A.8');
    assert.equal(E.ntToBase(E.Q.of('1/7'), 10), '0.(142857)');
    assert.equal(E.ntToBase(10n ** 30n, 36), (10n ** 30n).toString(36).toUpperCase());
    const r = E.ntToBase('0.1', 2, { steps: true });
    assert.equal(r.pre, '0');
    assert.equal(r.period, '0011');
    assert.equal(r.tex.ru, '0{,}0(0011)_{2}');
    assert.equal(r.tex.en, '0.0(0011)_{2}');
    checkSteps(r.steps, 'toBase 0.1');
    assert.match(r.steps.find((s) => s.rule === 'repeated-multiplication').text.ru, /0,2 уже встречалась/);
    const t = E.ntToBase(25, 2, { steps: true });
    checkSteps(t.steps, 'toBase 25');
    assert.deepEqual(
        t.steps.find((s) => s.rule === 'repeated-division').data.rows.map((x) => x.r),
        [1n, 0n, 0n, 1n, 1n],
    );
    checkSteps(E.ntToBase(-2748, 16, { steps: true }).steps, 'toBase hex');
    const tr = E.ntToBase('1/97', 2, { steps: true, maxDigits: 20 });
    assert.equal(tr.truncated, true);
    checkSteps(tr.steps, 'toBase truncated');
    assert.throws(
        () => E.ntToBase(5, 1),
        (e) => e.name === 'MathError',
    );
    assert.throws(() => E.ntToBase(5, 37));
    for (let b = 2; b <= 36; b++)
        for (const n of [0, 1, 7, 35, 36, 1000, 65535, -99]) {
            assert.equal(E.ntToBase(n, b), n < 0 ? '-' + (-n).toString(b).toUpperCase() : n.toString(b).toUpperCase());
            assert.equal(E.ntFromBase(E.ntToBase(n, b), b), BigInt(n), `round trip ${n} base ${b}`);
        }
});

test('from base: positional sums, Horner, periods', () => {
    assert.equal(E.ntFromBase('11001', 2), 25n);
    assert.equal(E.ntFromBase('ff', 16), 255n);
    assert.equal(E.ntFromBase('-ABC', 16), -2748n);
    assert.equal(E.ntFromBase('1A.8', 16).toString(), '53/2');
    assert.equal(E.ntFromBase('1A,8', 16).toString(), '53/2');
    assert.equal(E.ntFromBase('0.(3)', 10).toString(), '1/3');
    assert.equal(E.ntFromBase('0.0(0011)', 2).toString(), '1/10');
    assert.equal(E.ntFromBase('0.1(6)', 10).toString(), '1/6');
    assert.equal(E.ntFromBase('.5', 10).toString(), '1/2');
    assert.ok(E.ntFromBase('1A.8', 16) instanceof E.Q);
    const r = E.ntFromBase('1A.8', 16, { steps: true });
    checkSteps(r.steps, 'fromBase');
    assert.equal(r.steps[0].tex.ru, '1A{,}8_{16} = 1 \\cdot 16^{1} + 10 \\cdot 16^{0} + 8 \\cdot 16^{-1} = 16 + 10 + 0{,}5 = 26{,}5');
    const h = E.ntFromBase('101101', 2, { steps: true });
    assert.ok(h.steps.some((s) => s.rule === 'horner' && /22 \\cdot 2 \+ 1 = 45/.test(s.tex)));
    checkSteps(E.ntFromBase('0.(0011)', 2, { steps: true }).steps, 'fromBase period');
    checkSteps(E.ntFromBase('-777', 8, { steps: true }).steps, 'fromBase negative');
    assert.throws(
        () => E.ntFromBase('129', 2),
        (e) => e.name === 'MathError' && /Цифры «2» нет/.test(e.msg.ru),
    );
    assert.throws(() => E.ntFromBase('1.2.3', 10));
    assert.throws(() => E.ntFromBase('', 10));
    for (const s of ['0.5', '2.75', '0.(142857)', '3.1(4)', '-0.125']) {
        const q = E.ntFromBase(s, 10);
        const back = E.ntToBase(q, 10);
        assert.equal(E.ntFromBase(back, 10).toString(), q.toString(), `decimal round trip ${s}`);
    }
});

// ---------------------------------------------------------------- continued fractions, Egyptian fractions

test('continued fractions and convergents', () => {
    assert.deepEqual(E.ntContinuedFraction('415/93').terms, [4n, 2n, 6n, 7n]);
    assert.deepEqual(E.ntContinuedFraction(E.Q.of('-7/3')).terms, [-3n, 1n, 2n]);
    assert.deepEqual(E.ntContinuedFraction(5).terms, [5n]);
    const r = E.ntContinuedFraction('415/93', { steps: true });
    checkSteps(r.steps, 'cf');
    assert.match(r.steps.at(-1).tex, /4 \+ \\cfrac\{1\}\{2 \+ \\cfrac\{1\}\{6 \+ \\cfrac\{1\}\{7\}\}\}/);
    const s7 = E.ntContinuedFraction({ sqrt: 7 }, { steps: true });
    assert.deepEqual(s7.period, [1n, 1n, 1n, 4n]);
    assert.equal(s7.tex, '\\sqrt{7} = [2;\\ \\overline{1,\\ 1,\\ 1,\\ 4}]');
    checkSteps(s7.steps, 'cf sqrt7');
    assert.deepEqual(E.ntContinuedFraction({ sqrt: 2 }).period, [2n]);
    assert.deepEqual(E.ntContinuedFraction({ sqrt: 61 }).period.length, 11);
    assert.deepEqual(E.ntContinuedFraction({ sqrt: 16 }).terms, [4n]);
    const pi = E.ntContinuedFraction(Math.PI);
    assert.deepEqual(pi.terms.slice(0, 5), [3n, 7n, 15n, 1n, 292n]);
    assert.equal(pi.exact, false);
    const conv = E.ntConvergents([3n, 7n, 15n, 1n]);
    assert.deepEqual(
        conv.map((c) => `${c.p}/${c.q}`),
        ['3/1', '22/7', '333/106', '355/113'],
    );
    const pell = E.ntConvergents(E.ntContinuedFraction({ sqrt: 2 }), { count: 6 });
    for (const { p, q } of pell) assert.ok(p * p - 2n * q * q === 1n || p * p - 2n * q * q === -1n);
    const s61 = E.ntConvergents(E.ntContinuedFraction({ sqrt: 61 }), { count: 11 }).at(-1);
    assert.equal(s61.p * s61.p - 61n * s61.q * s61.q, -1n);
    assert.deepEqual(E.ntBestApprox(Math.PI, 1000), { p: 355n, q: 113n });
    assert.deepEqual(E.ntBestApprox(Math.PI, 10), { p: 22n, q: 7n });
    assert.deepEqual(E.ntBestApprox(Math.PI, 100), { p: 311n, q: 99n });
    assert.deepEqual(E.ntBestApprox('0.333', 10), { p: 1n, q: 3n });
    assert.deepEqual(E.ntBestApprox(Math.E, 1000), { p: 1457n, q: 536n });
    for (const [x, D] of [
        [Math.SQRT2, 50],
        [0.1234, 30],
        [2.718281828, 200],
    ]) {
        const best = E.ntBestApprox(x, D);
        let bestErr = Infinity;
        for (let q = 1; q <= D; q++) bestErr = Math.min(bestErr, Math.abs(Math.round(x * q) / q - x));
        close(Math.abs(Number(best.p) / Number(best.q) - x), bestErr, 1e-12, `best approx of ${x}`);
    }
});

test('Egyptian fractions (greedy)', () => {
    assert.deepEqual(E.ntEgyptian('4/13'), [4n, 18n, 468n]);
    assert.deepEqual(E.ntEgyptian('2/3'), [2n, 6n]);
    assert.deepEqual(E.ntEgyptian('1/5'), [5n]);
    assert.deepEqual(E.ntEgyptian(1), [1n]);
    assert.deepEqual(E.ntEgyptian('5/121'), [25n, 757n, 763309n, 873960180913n, 1527612795642093418846225n]);
    const r = E.ntEgyptian('4/13', { steps: true });
    checkSteps(r.steps, 'egyptian');
    assert.throws(() => E.ntEgyptian('3/2'));
    assert.throws(() => E.ntEgyptian(0));
    for (let d = 2; d < 40; d++)
        for (let n = 1; n < d; n++) {
            const dens = E.ntEgyptian(`${n}/${d}`);
            let sn = 0n,
                sd = 1n;
            for (const x of dens) {
                sn = sn * x + sd;
                sd *= x;
            }
            assert.equal(sn * BigInt(d), sd * BigInt(n), `${n}/${d}`);
            for (let i = 1; i < dens.length; i++) assert.ok(dens[i] > dens[i - 1]);
        }
});

test('divisibility rules with explanations', () => {
    const cases = [
        [123456, 3, true],
        [123457, 3, false],
        [918082, 11, true],
        [918083, 11, false],
        [7128, 12, true],
        [1000, 8, true],
        [1004, 8, false],
        [375, 25, true],
        [370, 25, false],
        [4096, 4, true],
        [4098, 4, false],
        [999999999999, 9, true],
        [98765, 5, true],
        [98764, 5, false],
        [120, 10, true],
        [121, 2, false],
        [0, 11, true],
        [7, 4, false],
        [36, 6, true],
        [135, 45, true],
        [2250, 75, true],
        [1500, 100, true],
        [360, 36, true],
        [5050, 20, false],
    ];
    for (const [n, d, ok] of cases) {
        const r = E.ntDivisibilityRule(n, d);
        assert.equal(r.divides, ok, `${n} ÷ ${d}`);
        assert.equal(r.remainder, BigInt(n % d));
        checkSteps(r.steps, `rule ${n}/${d}`);
    }
    assert.equal(E.ntDivisibilityRule(123456, 3).steps[0].tex, '1 + 2 + 3 + 4 + 5 + 6 = 21');
    assert.match(E.ntDivisibilityRule('98 765 432 123 456 789 000', 9).steps[0].text.ru, /Сумма цифр/);
    for (let n = 0; n < 3000; n += 13)
        for (const d of [2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 15, 18, 25]) {
            assert.equal(E.ntDivisibilityRule(n, d).divides, n % d === 0, `${n} % ${d}`);
        }
    assert.throws(
        () => E.ntDivisibilityRule(10, 7),
        (e) => e.name === 'MathError',
    );
});

// ---------------------------------------------------------------- numeric: roots and optimisation

test('roots: bisection, Brent, Newton, all roots', () => {
    const b = E.numBisect((x) => x * x - 2, 0, 2, { trace: true });
    close(b.root, Math.SQRT2, 1e-11);
    assert.equal(b.converged, true);
    assert.ok(b.trace.length > 30 && b.trace[0].m === 1);
    assert.throws(
        () => E.numBisect((x) => x * x + 1, -1, 1),
        (e) => e.name === 'MathError' && e.code === 'no-sign-change',
    );
    assert.equal(E.numBisect((x) => x, 0, 1).root, 0);
    close(E.numBrent(Math.cos, 0, 3).root, Math.PI / 2, 1e-14);
    close(E.numBrent((x) => x ** 3 - 2 * x - 5, 2, 3).root, 2.0945514815423265, 1e-14);
    close(E.numBrent((x) => Math.exp(x) - 10, 0, 5).root, Math.log(10), 1e-14);
    const n = E.numNewton(
        (x) => x * x - 2,
        (x) => 2 * x,
        1,
        { trace: true },
    );
    close(n.root, Math.SQRT2, 1e-15);
    assert.ok(n.iterations <= 7);
    close(E.numNewton((x) => Math.cos(x) - x, null, 1).root, 0.7390851332151607, 1e-12);
    assert.equal(
        E.numNewton(
            (x) => x * x + 1,
            (x) => 2 * x,
            0,
        ).reason,
        'flat',
    );
    const roots = E.numFindRoots((x) => (x - 1) ** 2 * (x + 2) * Math.sin(x), -4, 4);
    assert.deepEqual(
        roots.map((r) => r.kind),
        ['cross', 'cross', 'cross', 'touch', 'cross'],
    );
    [-Math.PI, -2, 0, 1, Math.PI].forEach((x, i) => close(roots[i].x, x, 1e-7));
    assert.equal(roots[3].multiplicity, 2);
    assert.equal(roots[1].multiplicity, 1);
    const cubic = E.numFindRoots((x) => (x - 0.5) ** 3, -1, 2);
    assert.equal(cubic.length, 1);
    assert.equal(cubic[0].multiplicity, 3);
    const tan = E.numFindRoots(Math.tan, -4, 4);
    assert.equal(tan.length, 3, 'poles of tan are not roots');
    assert.equal(E.numFindRoots((x) => x * x + 1e-6, -1, 1).length, 0);
    assert.equal(E.numFindRoots((x) => Math.floor(x) - 0.5, 0, 3).length, 0, 'a jump is not a root');
    const flat = E.numFindRoots((x) => Math.max(0, x) * (x - 2), -1, 3);
    assert.deepEqual(
        flat.map((r) => r.kind),
        ['interval', 'cross'],
    );
    assert.equal(flat[0].from, -1);
    close(flat[0].to, 0, 1e-12);
    close(flat[1].x, 2, 1e-12);
    assert.deepEqual(
        E.numFindRoots(() => 0, 0, 1).map((r) => [r.kind, r.from, r.to]),
        [['interval', 0, 1]],
    );
    const sq = E.numFindRoots((x) => x * x - 2, -3, 3);
    close(sq[0].x, -Math.SQRT2, 1e-12);
    close(sq[1].x, Math.SQRT2, 1e-12);
});

test('optimisation: golden section, extrema', () => {
    const g = E.numGoldenMin((x) => (x - 0.3) ** 2 + 1, -1, 2, { trace: true });
    close(g.x, 0.3, 1e-7);
    close(g.fx, 1, 1e-12);
    assert.ok(g.trace.length > 10);
    const ex = E.numExtrema(Math.sin, 0, 10);
    assert.deepEqual(
        ex.map((e) => e.kind),
        ['max', 'min', 'max'],
    );
    close(ex[0].x, Math.PI / 2, 1e-7);
    close(ex[1].x, (3 * Math.PI) / 2, 1e-7);
    const cubic = E.numExtrema((x) => x ** 3 - 3 * x, -3, 3);
    assert.equal(cubic.length, 2);
    close(cubic[0].x, -1, 1e-7);
    close(cubic[0].y, 2, 1e-12);
    assert.equal(cubic[1].kind, 'min');
    assert.equal(E.numExtrema((x) => 2 * x + 1, -5, 5).length, 0);
    const kink = E.numExtrema((x) => Math.abs(x - 0.25), -1, 1);
    assert.equal(kink.length, 1);
    close(kink[0].x, 0.25, 1e-7);
});

// ---------------------------------------------------------------- numeric: calculus

test('derivatives by Richardson extrapolation', () => {
    close(E.numDerivative(Math.exp, 1), Math.E, 1e-12);
    close(E.numDerivative(Math.sin, 2), Math.cos(2), 1e-12);
    close(
        E.numDerivative((x) => x ** 3, 2),
        12,
        1e-12,
    );
    close(E.numDerivative(Math.sin, 1, { order: 2 }), -Math.sin(1), 1e-10);
    close(E.numDerivative(Math.sin, 1, { order: 3 }), -Math.cos(1), 1e-9);
    // near the pole of tan the first tableau from a wide step is garbage; the restart must catch it
    const scc = (x) => Math.sin(Math.cos(Math.tan(x)));
    const t13 = Math.tan(1.3);
    close(E.numDerivative(scc, 1.3), -Math.cos(Math.cos(t13)) * Math.sin(t13) * (1 + t13 * t13), 1e-9);
    close(E.numDerivative(Math.exp, 0.5, { order: 4 }), Math.exp(0.5), 1e-8);
    close(E.numDerivative(Math.log, 1e-3), 1000, 1e-8);
    const d = E.numDerivative(Math.atan, 1, { info: true });
    close(d.value, 0.5, 1e-12);
    assert.ok(d.error < 1e-10);
    assert.throws(() => E.numDerivative(Math.sin, 0, { order: 5 }));
    for (let x = -3; x <= 3; x += 0.25)
        close(
            E.numDerivative((t) => Math.sin(t) * Math.exp(t / 3), x),
            Math.cos(x) * Math.exp(x / 3) + (Math.sin(x) * Math.exp(x / 3)) / 3,
            1e-10,
            `d at ${x}`,
        );
});

test('integrals versus closed forms (incl. singular ends and infinite limits)', () => {
    const cases = [
        [Math.sin, 0, Math.PI, 2],
        [(x) => x * x, 0, 3, 9],
        [Math.exp, 0, 1, Math.E - 1],
        [(x) => 1 / x, 1, Math.E, 1],
        [(x) => 1 / (1 + x * x), 0, 1, Math.PI / 4],
        [(x) => Math.sqrt(1 - x * x), -1, 1, Math.PI / 2],
        [(x) => Math.abs(x - 0.3), 0, 1, 0.29],
        [(x) => (x < 0.5 ? 1 : 3), 0, 1, 2],
        [(x) => 1 / Math.sqrt(x), 0, 1, 2],
        [Math.log, 0, 1, -1],
        [(x) => x ** -0.9, 0, 1, 10],
        [(x) => Math.log(x) * Math.log(1 - x), 0, 1, 2 - Math.PI ** 2 / 6],
        [(x) => Math.exp(-x * x), -Infinity, Infinity, Math.sqrt(Math.PI)],
        [(x) => 1 / (1 + x * x), 0, Infinity, Math.PI / 2],
        [(x) => Math.exp(x), -Infinity, 0, 1],
        [(x) => Math.exp(-x) * Math.log(x), 0, Infinity, -0.5772156649015329],
        [(x) => Math.sin(x) ** 2, 0, 2 * Math.PI, Math.PI],
        [(x) => Math.cos(50 * x), 0, 1, Math.sin(50) / 50],
    ];
    for (const [f, a, b, v] of cases) close(E.numIntegrate(f, a, b), v, 1e-9, `∫ ${f} from ${a} to ${b}`);
    close(
        E.numIntegrate((x) => x, 1, 0),
        -0.5,
        1e-14,
    );
    assert.equal(E.numIntegrate(Math.sin, 2, 2), 0);
    const info = E.numIntegrate(Math.log, 0, 1, { info: true });
    assert.equal(info.method, 'tanh-sinh');
    assert.ok(info.error < 1e-10);
    const gk = E.numIntegrate((x) => x ** 5, 0, 2, { info: true });
    close(gk.value, 64 / 6, 1e-14);
    assert.equal(gk.method, 'gauss-kronrod');
    assert.ok(Array.isArray(gk.intervals));
});

test('Riemann sums: left, right, mid, trapezoid, Simpson', () => {
    const f = (x) => x * x;
    assert.equal(E.numRiemann(f, 0, 1, 4, 'left').value, 0.21875);
    assert.equal(E.numRiemann(f, 0, 1, 4, 'right').value, 0.46875);
    close(E.numRiemann(f, 0, 1, 4, 'mid').value, 0.328125, 1e-15);
    close(E.numRiemann(f, 0, 1, 4, 'trapezoid').value, 0.34375, 1e-15);
    close(E.numRiemann(f, 0, 1, 4, 'simpson').value, 1 / 3, 1e-15);
    const s = E.numRiemann((x) => x ** 3, 0, 2, 3, 'simpson');
    assert.equal(s.n, 4);
    close(s.value, 4, 1e-14);
    assert.equal(s.pieces.length, 2);
    const l = E.numRiemann(f, 0, 1, 10, 'left');
    assert.equal(l.pieces.length, 10);
    assert.deepEqual(Object.keys(l.pieces[3]).sort(), ['h', 'x0', 'x1']);
    close(l.pieces[3].h, 0.09, 1e-15);
    const t = E.numRiemann(f, 0, 1, 2, 'trapezoid');
    assert.equal(t.pieces[1].y1, 1);
    assert.throws(() => E.numRiemann(f, 0, 1, 4, 'upper'));
    let prev = Infinity;
    for (const n of [4, 8, 16, 32]) {
        const err = Math.abs(E.numRiemann(Math.sin, 0, Math.PI, n, 'mid').value - 2);
        assert.ok(err < prev / 3.5, 'midpoint rule is second order');
        prev = err;
    }
});

// ---------------------------------------------------------------- numeric: ODEs

test('ODEs: Euler, RK4, Dormand–Prince, model systems', () => {
    const eu = E.numEuler((t, y) => y, 0, 1, 0.1, 10);
    assert.equal(eu.t.length, 11);
    close(eu.y[10], 1.1 ** 10, 1e-12);
    const rk = E.numRk4((t, y) => y, 0, 1, 0.1, 10);
    close(rk.y[10], Math.E, 1e-5);
    const rkErr = [0.2, 0.1].map((h) => Math.abs(E.numRk4((t, y) => y, 0, 1, h, Math.round(1 / h)).y.at(-1) - Math.E));
    assert.ok(rkErr[0] / rkErr[1] > 14, 'RK4 is fourth order');
    const osc = E.numRk4((t, [x, v]) => [v, -x], 0, [1, 0], 0.01, 628);
    close(osc.y.at(-1)[0], Math.cos(6.28), 1e-8);
    const dp = E.numOdeAdaptive((t, y) => y, 0, 1, 1, { rtol: 1e-10, atol: 1e-12 });
    close(dp.y.at(-1), Math.E, 1e-9);
    assert.equal(dp.ok, true);
    const back = E.numOdeAdaptive((t, y) => y, 1, Math.E, 0, { rtol: 1e-10 });
    close(back.y.at(-1), 1, 1e-8);
    const samp = E.numOdeAdaptive((t, [x, v]) => [v, -x], 0, [1, 0], Math.PI, { samples: 20, rtol: 1e-9, atol: 1e-12 });
    assert.equal(samp.t.length, 21);
    samp.t.forEach((t, i) => close(samp.y[i][0], Math.cos(t), 1e-6, `cos at ${t}`));
    const stiffish = E.numOdeAdaptive((t, y) => -50 * (y - Math.cos(t)), 0, 0, 2, { rtol: 1e-6 });
    assert.equal(stiffish.ok, true);
    // models
    const sir = E.numOdeAdaptive(E.odeSir(0.3, 0.1), 0, [0.99, 0.01, 0], 160, { samples: 160 });
    for (const y of sir.y) close(y[0] + y[1] + y[2], 1, 1e-6, 'SIR conserves population');
    assert.ok(Math.max(...sir.y.map((y) => y[1])) > 0.25);
    const lv = E.odeLotkaVolterra(1.1, 0.4, 0.1, 0.4);
    const V = ([x, y]) => 0.1 * x - 0.4 * Math.log(x) + 0.4 * y - 1.1 * Math.log(y);
    const orbit = E.numOdeAdaptive(lv, 0, [10, 10], 50, { rtol: 1e-10, atol: 1e-12 });
    close(V(orbit.y.at(-1)), V([10, 10]), 1e-7, 'Lotka–Volterra invariant');
    const pend = E.numOdeAdaptive(E.odePendulum(9.81, 1), 0, [0.1, 0], 10, { rtol: 1e-10, atol: 1e-12 });
    const energy = ([th, w]) => 0.5 * w * w - 9.81 * Math.cos(th);
    close(energy(pend.y.at(-1)), energy([0.1, 0]), 1e-8, 'pendulum energy');
    const lor = E.numOdeAdaptive(E.odeLorenz(), 0, [1, 1, 1], 1, { rtol: 1e-10, atol: 1e-12 });
    assert.equal(lor.y.at(-1).length, 3);
    assert.throws(() => E.numRk4((t, y) => y, 0, 'x', 0.1, 3));
});

// ---------------------------------------------------------------- numeric: plot sampling

test('sampleFunction splits at poles, jumps and domain edges', () => {
    const tan = E.sampleFunction(Math.tan, -5, 5, { yRange: [-5, 5] });
    assert.equal(tan.length, 5);
    for (const seg of tan) for (let i = 1; i < seg.length; i++) assert.ok(seg[i][0] > seg[i - 1][0], 'x increases');
    for (const seg of tan) for (const [, y] of seg) assert.ok(y >= -25 && y <= 25, 'clamped to two view heights around the view');
    const floor = E.sampleFunction(Math.floor, -3, 3);
    assert.equal(floor.length, 6);
    for (const seg of floor) assert.equal(new Set(seg.map(([, y]) => y)).size, 1, 'each step is flat');
    const sign = E.sampleFunction(Math.sign, -2, 2);
    assert.equal(sign.length, 2);
    const sq = E.sampleFunction(Math.sqrt, -1, 4);
    assert.equal(sq.length, 1);
    assert.ok(sq[0][0][0] >= 0 && sq[0][0][0] < 1e-6, 'starts at the edge of the domain');
    const log = E.sampleFunction(Math.log, -1, 3, { yRange: [-4, 4] });
    assert.equal(log.length, 1);
    assert.ok(log[0][0][1] <= -4, 'log dives below the view near 0');
    const inv = E.sampleFunction((x) => 1 / x, -2, 2, { yRange: [-10, 10] });
    assert.equal(inv.length, 2);
    assert.ok(inv[0].at(-1)[1] < -10 && inv[1][0][1] > 10);
    const smooth = E.sampleFunction(Math.sin, 0, 10);
    assert.equal(smooth.length, 1);
    assert.ok(smooth[0].length >= 401);
    const steep = E.sampleFunction((x) => Math.atan(1000 * x), -1, 1);
    assert.equal(steep.length, 1, 'steep but continuous stays in one piece');
    const circle = E.sampleFunction((x) => Math.sqrt(1 - x * x), -2, 2);
    assert.equal(circle.length, 1);
    close(circle[0][0][0], -1, 1e-6);
    close(circle[0].at(-1)[0], 1, 1e-6);
    const throwsInside = E.sampleFunction(
        (x) => {
            if (x > 0) throw new Error('boom');
            return x;
        },
        -1,
        1,
    );
    assert.equal(throwsInside.length, 1);
    assert.deepEqual(
        E.sampleFunction(() => NaN, 0, 1),
        [],
    );
    const recip = E.sampleFunction((x) => 1 / (x * x), -1, 1, { yRange: [0, 5] });
    assert.equal(recip.length, 2, 'even pole: both branches go up');
});

// ---------------------------------------------------------------- numeric: signals

test('DFT and FFT: known spectra and round trips', () => {
    const x = [1, 2, 3, 4];
    const d = E.numDft(x);
    assert.deepEqual(
        Array.from(d.re).map((v) => +v.toFixed(12)),
        [10, -2, -2, -2],
    );
    assert.deepEqual(
        Array.from(d.im).map((v) => +v.toFixed(12) + 0),
        [0, 2, 0, -2],
    );
    const f = E.numFft(x);
    for (let k = 0; k < 4; k++) {
        close(f.re[k], d.re[k], 1e-12);
        close(f.im[k], d.im[k], 1e-12);
    }
    const N = 256;
    const sig = Array.from({ length: N }, (_, i) => Math.sin((2 * Math.PI * 5 * i) / N) + 0.5 * Math.cos((2 * Math.PI * 12 * i) / N));
    const S = E.numFft(sig);
    close(S.im[5], -N / 2, 1e-9);
    close(S.re[12], N / 4, 1e-9);
    close(Math.hypot(S.re[7], S.im[7]), 0, 1e-9);
    const back = E.numIfft(S.re, S.im);
    sig.forEach((v, i) => close(back.re[i], v, 1e-12));
    const padded = E.numFft([1, 1, 1]);
    assert.equal(padded.re.length, 4);
    const rnd = Array.from({ length: 50 }, (_, i) => Math.sin(i * i));
    const D2 = E.numDft(rnd),
        D3 = E.numDft(D2.re, D2.im, { inverse: true });
    rnd.forEach((v, i) => close(D3.re[i], v, 1e-12));
    const F = E.numFft(rnd.slice(0, 32));
    const Dd = E.numDft(rnd.slice(0, 32));
    for (let k = 0; k < 32; k++) close(F.re[k], Dd.re[k], 1e-10);
});

test('Fourier coefficients of the square wave and a sawtooth', () => {
    const sq = (x) => (Math.sin(x) >= 0 ? 1 : -1);
    const c = E.numFourierCoefficients(sq, 7);
    for (let k = 1; k <= 7; k++) close(c.b[k], k % 2 ? 4 / (Math.PI * k) : 0, 1e-3, `square b${k}`);
    for (let k = 0; k <= 7; k++) close(c.a[k], 0, 1e-3, `square a${k}`);
    const saw = E.numFourierCoefficients((x) => x, 5);
    for (let k = 1; k <= 5; k++) close(saw.b[k], (2 * (-1) ** (k + 1)) / k, 1e-3, `saw b${k}`);
    const cosine = E.numFourierCoefficients((x) => 3 + 2 * Math.cos(2 * x), 4, 2 * Math.PI);
    close(cosine.a[0], 6, 1e-12);
    close(cosine.mean, 3, 1e-12);
    close(cosine.a[2], 2, 1e-12);
    close(E.numFourierEval(cosine, 0.7), 3 + 2 * Math.cos(1.4), 1e-12);
    const tri = E.numFourierCoefficients((x) => Math.abs(x), 3, 2, { from: -1 });
    close(tri.a[0] / 2, 0.5, 1e-6);
    close(tri.a[1], -4 / Math.PI ** 2, 1e-5);
});

// ---------------------------------------------------------------- statistics and probability

test('descriptive statistics', () => {
    const xs = [2, 4, 4, 4, 5, 5, 7, 9];
    assert.equal(E.statMean(xs), 5);
    assert.equal(E.statMedian(xs), 4.5);
    assert.equal(E.statMedian([3, 1, 2]), 2);
    assert.deepEqual(E.statMode(xs), [4]);
    assert.deepEqual(E.statMode([1, 1, 2, 2, 3]), [1, 2]);
    assert.deepEqual(E.statMode([1, 2, 3]), []);
    assert.deepEqual(E.statMode([7]), [7]);
    assert.equal(E.statVariance(xs), 4);
    assert.equal(E.statStd(xs), 2);
    close(E.statVariance(xs, 'sample'), 32 / 7, 1e-15);
    close(E.statStd(xs, { sample: true }), Math.sqrt(32 / 7), 1e-15);
    assert.equal(E.statQuantile([1, 2, 3, 4, 5], 0.5), 3);
    assert.equal(E.statQuantile([1, 2, 3, 4], 0.25), 1.75);
    assert.equal(E.statQuantile([1, 2, 3, 4], 0), 1);
    assert.equal(E.statQuantile([1, 2, 3, 4], 1), 4);
    close(E.statCorrelation([1, 2, 3, 4, 5], [2, 4, 6, 8, 10]), 1, 1e-15);
    close(E.statCorrelation([1, 2, 3, 4, 5], [5, 4, 3, 2, 1]), -1, 1e-15);
    close(E.statCorrelation([1, 2, 3, 4], [1, 3, 2, 4]), 0.8, 1e-15);
    const big = Array.from({ length: 1000 }, () => 1e9 + 0.1);
    close(E.statMean(big), 1e9 + 0.1, 1e-15);
    close(E.statVariance([1e9 + 1, 1e9 + 2, 1e9 + 3]), 2 / 3, 1e-9);
    assert.throws(
        () => E.statMean([]),
        (e) => e.name === 'MathError',
    );
    assert.throws(() => E.statMean([1, 'x']));
    assert.throws(() => E.statVariance([1], 'sample'));
    assert.throws(() => E.statQuantile([1, 2], 1.5));
});

test('regression and polynomial fit', () => {
    const r = E.statLinearRegression([
        [1, 3],
        [2, 5],
        [3, 7],
        [4, 9],
    ]);
    close(r.a, 2, 1e-14);
    close(r.b, 1, 1e-14);
    close(r.r2, 1, 1e-14);
    const n = E.statLinearRegression([
        { x: 1, y: 1 },
        { x: 2, y: 2 },
        { x: 3, y: 1.3 },
        { x: 4, y: 3.75 },
        { x: 5, y: 2.25 },
    ]);
    close(n.slope, 0.425, 1e-12);
    close(n.intercept, 0.785, 1e-12);
    close(n.r, 4.25 / Math.sqrt(10 * 4.597), 1e-12);
    assert.throws(
        () =>
            E.statLinearRegression([
                [1, 1],
                [1, 2],
            ]),
        (e) => e.code === 'degenerate',
    );
    const p = E.statPolyFit(
        [
            [0, 1],
            [1, 0],
            [2, 1],
            [3, 4],
        ],
        2,
    );
    [1, -2, 1].forEach((c, i) => close(p.coefs[i], c, 1e-10));
    close(p.r2, 1, 1e-12);
    const pts = Array.from({ length: 30 }, (_, i) => {
        const x = 1990 + i;
        return [x, 0.5 * (x - 2000) ** 3 - 2 * (x - 2000) + 7];
    });
    const cub = E.statPolyFit(pts, 3);
    for (const [x, y] of pts)
        close(
            cub.coefs.reduceRight((acc, c) => acc * x + c, 0),
            y,
            1e-6,
            `poly fit at ${x}`,
        );
    const line = E.statPolyFit(
        [
            [0, 0],
            [1, 1],
            [2, 2],
        ],
        1,
    );
    close(line.coefs[1], 1, 1e-14);
    assert.throws(() => E.statPolyFit([[0, 1]], 2));
});

test('special functions and distributions against reference values', () => {
    const erf = [
        [0, 0],
        [0.1, 0.1124629160182849],
        [0.5, 0.5204998778130465],
        [1, 0.8427007929497149],
        [2, 0.9953222650189527],
        [3, 0.9999779095030014],
    ];
    for (const [x, v] of erf) {
        close(E.probErf(x), v, 2e-15, `erf(${x})`);
        close(E.probErf(-x), -v, 2e-15);
    }
    close(E.probErfc(3), 2.209049699858544e-5, 1e-13);
    close(E.probErfc(5), 1.5374597944280349e-12, 1e-12);
    close(E.probErfc(10), 2.088487583762545e-45, 1e-12);
    close(E.probErfc(-1), 1.8427007929497148, 1e-15);
    close(E.probNormalCdf(0), 0.5, 1e-16);
    close(E.probNormalCdf(1.96), 0.9750021048517795, 1e-15);
    close(E.probNormalCdf(-1), 0.15865525393145707, 1e-14);
    close(E.probNormalCdf(-10), 7.619853024160527e-24, 1e-12);
    close(E.probNormalCdf(110, 100, 15), 0.7475074624530771, 1e-14);
    close(E.probNormalPdf(0), 0.3989422804014327, 1e-15);
    close(E.probNormalInv(0.975), 1.959963984540054, 1e-14);
    close(E.probNormalInv(0.5), 0, 1e-15);
    close(E.probNormalInv(0.001), -3.090232306167813, 1e-13);
    close(E.probNormalInv(1e-10), -6.361340902404056, 1e-12);
    close(E.probNormalInv(0.95, 10, 2), 10 + 2 * 1.6448536269514722, 1e-14);
    for (let p = 0.01; p < 1; p += 0.07) close(E.probNormalCdf(E.probNormalInv(p)), p, 1e-14, `Φ(Φ⁻¹(${p}))`);
    assert.equal(E.probNormalInv(0), -Infinity);
    assert.throws(() => E.probNormalInv(1.2));
    // Student t (tables): t_{0.975} for df = 1, 2, 5, 10, 30; cdf values
    const tq = [
        [1, 12.706204736174698],
        [2, 4.302652729749464],
        [5, 2.570581835636314],
        [10, 2.228138851986273],
        [30, 2.042272456301236],
    ];
    for (const [df, q] of tq) {
        close(E.probStudentTInv(0.975, df), q, 1e-10, `t(0.975, ${df})`);
        close(E.probStudentTCdf(q, df), 0.975, 1e-12);
    }
    close(E.probStudentTCdf(1, 1), 0.75, 1e-14);
    close(E.probStudentTCdf(-2, 3), 0.06966298427942164, 1e-12);
    close(E.probStudentTInv(0.05, 8), -1.8595480375228428, 1e-10);
    close(E.probStudentTCdf(1.5, Infinity), E.probNormalCdf(1.5), 1e-15);
    assert.equal(E.probStudentTInv(0.5, 4), 0);
    // gamma family
    close(E.numGamma(5), 24, 1e-15);
    close(E.numGamma(0.5), Math.sqrt(Math.PI), 1e-14);
    close(E.numGamma(-0.5), -2 * Math.sqrt(Math.PI), 1e-14);
    close(E.numLogGamma(100), 359.1342053695754, 1e-14);
    assert.ok(Number.isNaN(E.numGamma(-2)));
    close(E.probChiSquareCdf(3.841458820694124, 1), 0.95, 1e-12);
    close(E.probChiSquareCdf(18.307038053275146, 10), 0.95, 1e-12);
    close(E.probBetaRegularized(0.5, 2, 3), 0.6875, 1e-14);
    close(E.probGammaRegularized(1, 2), 1 - Math.exp(-2), 1e-14);
});

test('discrete distributions and exact combinatorics', () => {
    assert.equal(E.probChoose(5, 2), 10n);
    assert.equal(E.probChoose(52, 5), 2598960n);
    assert.equal(E.probChoose(100, 50), 100891344545564193334812497256n);
    assert.equal(E.probChoose(5, 7), 0n);
    assert.equal(E.probChoose(5, -1), 0n);
    assert.equal(E.probFactorial(20), 2432902008176640000n);
    assert.equal(E.probFactorial(0), 1n);
    assert.equal(E.probArrangements(5, 2), 20n);
    assert.equal(E.probBinomialPmf(3, 10, 0.5), 120 / 1024);
    close(E.probBinomialCdf(3, 10, 0.5), 176 / 1024, 1e-15);
    close(E.probBinomialPmf(0, 5, 0), 1, 0);
    assert.equal(E.probBinomialPmf(11, 10, 0.5), 0);
    let total = 0;
    for (let k = 0; k <= 60; k++) total += E.probBinomialPmf(k, 60, 0.37);
    close(total, 1, 1e-13);
    close(E.probBinomialCdf(500, 1200, 0.4), E.probBetaRegularized(0.6, 700, 501), 1e-12);
    close(E.probBinomialPmf(1500, 3000, 0.5), 0.01456609851579575, 1e-14, 'exact C(3000,1500)/2^3000');
    close(E.probBinomialCdf(1500, 3000, 0.5), 0.5072830492578979, 1e-12);
    close(E.probPoissonPmf(100, 100), 0.03986099680914713, 1e-13);
    close(E.probBinomialPmf(0, 100, 0.01), 0.99 ** 100, 1e-13);
    close(E.probPoissonPmf(2, 3), 4.5 * Math.exp(-3), 1e-14);
    close(E.probPoissonCdf(2, 3), 8.5 * Math.exp(-3), 1e-13);
    close(E.probPoissonPmf(0, 0), 1, 0);
    close(E.probGeometricPmf(3, 0.2), 0.8 * 0.8 * 0.2, 1e-15);
    close(E.probGeometricCdf(3, 0.2), 1 - 0.8 ** 3, 1e-15);
    assert.equal(E.probGeometricPmf(0, 0.2), 0);
});

// ---------------------------------------------------------------- interpolation and polynomial roots

test('Lagrange interpolation and polynomial roots', () => {
    const L = E.numLagrange([
        [0, 1],
        [1, 3],
        [2, 11],
    ]);
    [1, -1, 3].forEach((c, i) => close(L.coefs[i], c, 1e-12));
    close(L.fn(1.5), 1 - 1.5 + 3 * 2.25, 1e-12);
    assert.equal(L.fn(2), 11);
    assert.throws(
        () =>
            E.numLagrange([
                [1, 2],
                [1, 3],
            ]),
        (e) => e.code === 'degenerate',
    );
    const pts = [-2, -1, 0, 1, 2, 3].map((x) => [x, x ** 5 - 3 * x ** 2 + 1]);
    const L5 = E.numLagrange(pts);
    [1, 0, -3, 0, 0, 1].forEach((c, i) => close(L5.coefs[i], c, 1e-10));
    close(L5.fn(0.37), 0.37 ** 5 - 3 * 0.37 ** 2 + 1, 1e-12);
    assert.deepEqual(E.numLinspace(0, 1, 5), [0, 0.25, 0.5, 0.75, 1]);
    assert.deepEqual(E.numLinspace(3, 3, 1), [3]);
    const r = E.numPolyRoots([-6, 11, -6, 1]);
    [1, 2, 3].forEach((v, i) => {
        close(r[i].re, v, 1e-12);
        assert.equal(r[i].im, 0);
    });
    const c = E.numPolyRoots([1, 0, 1]);
    close(c[0].im, -1, 1e-14);
    close(c[1].im, 1, 1e-14);
    const d = E.numPolyRoots([1, -2, 1]);
    close(d[0].re, 1, 1e-12);
    assert.equal(d[1].im, 0);
    const t = E.numPolyRoots([-1, 3, -3, 1]);
    t.forEach((z) => close(z.re, 1, 1e-10));
    const z0 = E.numPolyRoots([0, 0, 1, 1]);
    assert.deepEqual(
        z0.map((z) => z.re),
        [-1, 0, 0],
    );
    const w = E.numPolyRoots([-1, 0, 0, 0, 0, 1]);
    assert.equal(w.length, 5);
    for (const z of w) close(Math.hypot(z.re, z.im), 1, 1e-13, 'fifth roots of unity');
    const wilk = E.numPolyRoots([24, -50, 35, -10, 1]);
    [1, 2, 3, 4].forEach((v, i) => close(wilk[i].re, v, 1e-11));
    assert.deepEqual(E.numPolyRoots([5]), []);
});

test('exported names are unique and prefixed', () => {
    const mine = [
        'ntGcd',
        'ntLcm',
        'ntGcdMany',
        'ntLcmMany',
        'ntEgcd',
        'ntDiophantine',
        'ntIsPrime',
        'ntMillerRabin',
        'ntIsCarmichael',
        'ntFactor',
        'ntFactorTex',
        'ntDivisors',
        'ntTau',
        'ntSigma',
        'ntMobius',
        'ntPhi',
        'ntPrimesUpTo',
        'ntSieve',
        'ntPrimePi',
        'ntNextPrime',
        'ntPrevPrime',
        'ntIsPerfectSquare',
        'ntDigitSum',
        'ntModPow',
        'ntModInv',
        'ntSolveCongruence',
        'ntCrt',
        'ntOrder',
        'ntPrimitiveRoot',
        'ntRsaKey',
        'ntToBase',
        'ntFromBase',
        'ntContinuedFraction',
        'ntConvergents',
        'ntBestApprox',
        'ntEgyptian',
        'ntDivisibilityRule',
        'numLinspace',
        'numBisect',
        'numBrent',
        'numNewton',
        'numFindRoots',
        'numGoldenMin',
        'numExtrema',
        'numDerivative',
        'numIntegrate',
        'numIntegrateInfo',
        'numRiemann',
        'numEuler',
        'numRk4',
        'numOdeAdaptive',
        'odeSir',
        'odeLotkaVolterra',
        'odePendulum',
        'odeLorenz',
        'sampleFunction',
        'numDft',
        'numFft',
        'numIfft',
        'numFourierCoefficients',
        'numFourierEval',
        'statMean',
        'statMedian',
        'statMode',
        'statVariance',
        'statStd',
        'statQuantile',
        'statCorrelation',
        'statLinearRegression',
        'statPolyFit',
        'numLogGamma',
        'numGamma',
        'probErf',
        'probErfc',
        'probNormalPdf',
        'probNormalCdf',
        'probNormalInv',
        'probChoose',
        'probFactorial',
        'probArrangements',
        'probBinomialPmf',
        'probBetaRegularized',
        'probGammaRegularized',
        'probBinomialCdf',
        'probPoissonPmf',
        'probPoissonCdf',
        'probGeometricPmf',
        'probGeometricCdf',
        'probStudentTCdf',
        'probStudentTInv',
        'probChiSquareCdf',
        'numLagrange',
        'numPolyRoots',
    ];
    for (const name of mine) assert.equal(typeof E[name], 'function', `${name} is exported through index.js`);
});

test('numIntegrateInfo: divergent and unreliable integrals are flagged, good ones pass', () => {
    const I = (f, a, b) => E.numIntegrateInfo(f, a, b);
    // divergent: tails, poles inside and at the ends
    const div = [
        [(x) => 1 / x, 1, Infinity, 'tail', Infinity],
        [(x) => 1 / (x * x - 1), 0, 2, 'pole', NaN, 1],
        [(x) => 1 / x, 0, 1, 'pole', Infinity, 0],
        [(x) => 1 / x, -1, 1, 'pole', NaN, 0],
        [(x) => 1 / (x - 1) ** 2, 0, 2, 'pole', Infinity, 1],
        [(x) => 1 / (x - 0.3), 0, 1, 'pole', NaN, 0.3],
        [Math.tan, 0, 3, 'pole', NaN, Math.PI / 2],
        [Math.sin, 0, Infinity, 'tail', NaN],
        [Math.cos, -Infinity, Infinity, 'tail', NaN],
        [Math.exp, 0, Infinity, 'tail', Infinity],
        [(x) => x * Math.exp(-x), -Infinity, 0, 'tail', -Infinity],
        [(x) => 1 / Math.sqrt(x), 0, Infinity, 'tail', Infinity],
        [(x) => 1 / x, -Infinity, -1, 'tail', -Infinity],
    ];
    for (const [f, a, b, reason, value, at] of div) {
        const r = I(f, a, b);
        const what = `∫ ${f} from ${a} to ${b}`;
        assert.equal(r.ok, false, what);
        assert.equal(r.divergent, true, what);
        assert.equal(r.reason, reason, what);
        assert.ok(Number.isNaN(value) ? Number.isNaN(r.value) : r.value === value, `${what}: ${r.value}`);
        assert.ok(Number.isFinite(r.estimate), what);
        if (at !== undefined) close(r.at, at, 1e-9, `${what}: at`);
        assert.ok(r.msg.ru && r.msg.en);
    }
    // the old call is unchanged: a bare number (and the same one as the raw estimate)
    assert.equal(
        E.numIntegrate((x) => 1 / x, 1, Infinity),
        I((x) => 1 / x, 1, Infinity).estimate,
    );
    assert.equal(E.numIntegrate((x) => 1 / x, 2, 1, { info: true }).ok, undefined);
    // reversed limits: the sign flips, the verdict stays
    assert.equal(I((x) => 1 / x, Infinity, 1).value, -Infinity);
    // unreliable, but not proven divergent
    for (const [f, a, b, reason] of [
        [(x) => Math.sqrt(1 - x), 0, 2, 'domain'],
        [Math.log, -1, 1, 'domain'],
        [(x) => 1 / (x * Math.log(x) ** 2), 2, Infinity, 'inaccurate'],
        [(x) => Math.sin(1 / x), 0, 1, 'inaccurate'],
    ]) {
        const r = I(f, a, b);
        assert.equal(r.ok, false, `∫ ${f} from ${a} to ${b}`);
        assert.equal(r.divergent, false, `∫ ${f} from ${a} to ${b}`);
        assert.equal(r.reason, reason, `∫ ${f} from ${a} to ${b}: ${r.reason}`);
    }
    // oscillating tails that converge conditionally are summed lobe by lobe
    for (const [f, a, b, want] of [
        [(x) => Math.sin(x) / x, 0, Infinity, Math.PI / 2],
        [(x) => Math.sin(x) / Math.sqrt(x), 0, Infinity, Math.sqrt(Math.PI / 2)],
        [(x) => Math.sin(x * x), 0, Infinity, Math.sqrt(Math.PI / 8)],
        [(x) => Math.cos(x * x), -Infinity, Infinity, Math.sqrt(Math.PI / 2)],
        [(x) => Math.cos(x) / (1 + x * x), 0, Infinity, Math.PI / (2 * Math.E)],
    ]) {
        const r = I(f, a, b);
        assert.equal(r.ok, true, `∫ ${f} from ${a} to ${b}: ${r.reason}`);
        close(r.value, want, 1e-8);
    }
    // bounded lobes that never shrink stay divergent
    assert.equal(I(Math.sin, 0, Infinity).ok, false);
    assert.equal(I((x) => x * Math.sin(x), 0, Infinity).ok, false);
    // convergent ones stay ok (integrable singularities inside are split off and integrated properly)
    const good = [
        [Math.sin, 0, Math.PI, 2],
        [(x) => 1 / Math.sqrt(x), 0, 1, 2],
        [Math.log, 0, 1, -1],
        [(x) => x ** -0.9, 0, 1, 10],
        [(x) => Math.exp(-x * x), -Infinity, Infinity, Math.sqrt(Math.PI)],
        [(x) => 1 / (1 + x * x), 0, Infinity, Math.PI / 2],
        [(x) => Math.exp(x), -Infinity, 0, 1],
        [(x) => Math.exp(-x) * Math.log(x), 0, Infinity, -0.5772156649015329],
        [(x) => Math.cos(50 * x), 0, 1, Math.sin(50) / 50],
        [(x) => 1 / x ** 2, 1, Infinity, 1],
        [(x) => (x < 0.5 ? 1 : 3), 0, 1, 2],
        [(x) => 1 / Math.sqrt(Math.abs(x - 1)), 0, 2, 4],
        [(x) => Math.log(Math.abs(x - 1)), 0, 2, -2],
        [(x) => Math.exp(-x) * Math.sin(x), 0, Infinity, 0.5],
        [(x) => 1 / Math.sqrt(1 - x * x), -1, 1, Math.PI],
        [(x) => 1 / (x * x + 1e-14), -1, 1, 2e7 * Math.atan(1e7)],
        [Math.tan, 0, 1.5, -Math.log(Math.cos(1.5))],
    ];
    for (const [f, a, b, v] of good) {
        const r = I(f, a, b);
        assert.equal(r.ok, true, `∫ ${f} from ${a} to ${b}: ${r.reason}`);
        assert.equal(r.divergent, false);
        assert.equal(r.reason, null);
        close(r.value, v, 1e-7, `∫ ${f} from ${a} to ${b}`);
    }
    // an interior integrable singularity: better than the plain quadrature
    assert.ok(Math.abs(E.numIntegrate((x) => 1 / Math.sqrt(Math.abs(x - 1)), 0, 2) - 4) > 0.1);
    assert.equal(I(Math.sin, 2, 2).ok, true);
});
