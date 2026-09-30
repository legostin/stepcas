// theory/modular — modular arithmetic: powers, inverses, congruences, the Chinese remainder theorem, orders,
// primitive roots, RSA keys.

import { G, L, S, T, big, bmod, coefX, fail, gcdCore, invCore, powmod, ruPl, sn, tn, tp } from './common.js';
import { gcdSteps, ntEgcd } from './gcd.js';
import { factorMap, isPrimeBig, ntPhi } from './primes.js';

// ---------------------------------------------------------------- modular arithmetic

function needModulus(m) {
    const M = big(m, 'модуль');
    if (M <= 0n) throw fail('Модуль должен быть натуральным числом.', 'The modulus must be a positive integer.', 'modulus');
    return M;
}
const eqv = (m) => `\\pmod{${tn(m)}}`;

/**
 * a^e mod m by repeated squaring (result in [0, m)). A negative e uses the inverse (null if none).
 * {steps: true} → {value, rows: [{k, power, value, bit}], steps}.
 */
export function ntModPow(a, e, m, opts = {}) {
    const A = big(a), E = big(e), M = needModulus(m);
    if (E < 0n) {
        const inv = invCore(A, M);
        const value = inv === null ? null : powmod(inv, -E, M);
        if (!opts.steps) return value;
        const st = [S(L('Отрицательная степень', 'A negative exponent'), `${tp(A)}^{${tn(E)}} = \\left(${tp(A)}^{-1}\\right)^{${tn(-E)}}`,
            inv === null ? L(`Обратного к ${sn(A)} по модулю ${sn(M)} нет, поэтому отрицательная степень не определена.`, `${sn(A)} has no inverse modulo ${sn(M)}, so a negative power is undefined.`)
                : L(`Сначала находим обратный: ${sn(A)}⁻¹ ≡ ${sn(inv)} (mod ${sn(M)}), затем возводим его в степень ${sn(-E)}.`, `First the inverse: ${sn(A)}⁻¹ ≡ ${sn(inv)} (mod ${sn(M)}), then raise it to the power ${sn(-E)}.`),
            { rule: 'negative-power' })];
        if (inv === null) return { value, rows: [], steps: st };
        const r = ntModPow(inv, -E, M, { steps: true });
        return { value, rows: r.rows, steps: [...st, ...r.steps] };
    }
    const value = powmod(A, E, M);
    if (!opts.steps) return value;
    const st = [];
    const rows = [];
    if (M === 1n) {
        st.push(S(L('Модуль 1', 'Modulus 1'), `${tp(A)}^{${tn(E)}} \\equiv 0 \\pmod{1}`, L('По модулю 1 любое число сравнимо с нулём.', 'Every number is congruent to 0 modulo 1.'), { rule: 'answer' }));
        return { value, rows, steps: st };
    }
    if (E === 0n) {
        st.push(S(L('Нулевая степень', 'Power zero'), `${tp(A)}^{0} = 1`, L('Любое число в нулевой степени равно 1.', 'Anything to the power zero is 1.'), { rule: 'answer' }));
        return { value, rows, steps: st };
    }
    const bin = E.toString(2);
    const bits = bin.length;
    const used = [];
    for (let k = 0; k < bits; k++) if (bin[bits - 1 - k] === '1') used.push(k);
    const P = (k) => (k < 20 ? tn(1n << BigInt(k)) : `2^{${k}}`);
    const base = bmod(A, M);
    const sq = bits - 1;
    st.push(S(L('Показатель — в двоичную запись', 'Write the exponent in binary'),
        `${tn(E)} = ${bin}_2${used.length > 1 && used.length <= 12 ? ` = ${[...used].reverse().map(P).join(' + ')}` : ''}`,
        L(`Тогда ${sn(A)}^${sn(E)} — произведение степеней вида ${sn(A)}^(2^k) для единичных разрядов, а каждая такая степень — квадрат предыдущей. Всего ${sq} ${sq % 10 === 1 && sq % 100 !== 11 ? 'возведение' : sq % 10 >= 2 && sq % 10 <= 4 && (sq % 100 < 12 || sq % 100 > 14) ? 'возведения' : 'возведений'} в квадрат вместо ${sn(E - 1n)} умножений.`,
            `Then ${sn(A)}^${sn(E)} is the product of the powers ${sn(A)}^(2^k) for the one-bits, and each such power is the square of the previous one: ${sq} squaring${sq === 1 ? '' : 's'} instead of ${sn(E - 1n)} multiplications.`),
        { rule: 'binary' }));
    let cur = base;
    for (let k = 0; k < bits; k++) {
        if (k > 0) cur = (cur * cur) % M;
        rows.push({ k, power: 1n << BigInt(k), value: cur, bit: bin[bits - 1 - k] === '1' });
    }
    if (bits <= 64) {
        const lines = [];
        let prev = null;
        for (const r of rows) {
            let rhs;
            if (r.k === 0) rhs = base === A ? tn(A) : `${tn(A)} \\equiv ${tn(base)}`;
            else {
                const s2 = prev * prev;
                rhs = `${tp(prev)}^2 = ${tn(s2)}${s2 !== r.value ? ` \\equiv ${tn(r.value)}` : ''}`;
            }
            lines.push(`${tp(A)}^{${P(r.k)}} & ${rhs} & ${r.bit ? '\\checkmark' : ''}`);
            prev = r.value;
        }
        st.push(S(L('Возводим в квадрат по кругу', 'Square again and again'), `\\begin{array}{r|l|c} ${lines.join(' \\\\ ')} \\end{array}`,
            L(`Каждая строка — квадрат предыдущей, и сразу берём остаток от деления на ${sn(M)}, чтобы числа не росли. Галочки — разряды, где в двоичной записи показателя стоит 1.`,
                `Each line is the square of the previous one, reduced modulo ${sn(M)} right away so the numbers stay small. Ticks mark the bits of the exponent equal to 1.`),
            { rule: 'squaring' }));
    }
    if (used.length > 1) {
        const picks = used.map((k) => rows[k].value);
        let run = picks[0];
        const runs = [];
        for (let i = 1; i < picks.length; i++) {
            const prod = run * picks[i];
            const r = prod % M;
            runs.push(`${sn(run)} · ${sn(picks[i])} = ${sn(prod)}${prod !== r ? ` ≡ ${sn(r)}` : ''}`);
            run = r;
        }
        const short = used.length <= 16;
        st.push(S(L('Перемножаем отмеченные строки', 'Multiply the ticked lines'),
            short ? `${tp(A)}^{${tn(E)}} = ${[...used].reverse().map((k) => `${tp(A)}^{${P(k)}}`).join(' \\cdot ')} \\equiv ${[...used].reverse().map((k) => tn(rows[k].value)).join(' \\cdot ')} \\equiv ${tn(value)} ${eqv(M)}`
                : `${tp(A)}^{${tn(E)}} \\equiv ${tn(value)} ${eqv(M)}`,
            short ? L(`Умножаем по одному и каждый раз берём остаток: ${runs.join('; ')}.`, `Multiply one at a time, reducing each time: ${runs.join('; ')}.`) : null,
            { rule: 'multiply' }));
    }
    st.push(S(L('Ответ', 'Answer'), `${tp(A)}^{${tn(E)}} \\equiv ${tn(value)} ${eqv(M)}`, null, { rule: 'answer' }));
    // a second route: Euler's theorem (Fermat's little theorem for a prime modulus)
    if (M <= 10n ** 12n && M > 2n && gcdCore(A, M) === 1n) {
        const ph = ntPhi(M);
        if (E >= ph) {
            const q = E / ph, r = E % ph;
            const prime = isPrimeBig(M);
            st.push(S(prime ? L('Проверка малой теоремой Ферма', "Check with Fermat's little theorem") : L('Проверка теоремой Эйлера', "Check with Euler's theorem"),
                `${tp(A)}^{${tn(ph)}} \\equiv 1 ${eqv(M)},\\quad ${tn(E)} = ${tn(q)} \\cdot ${tn(ph)} + ${tn(r)} \\;\\Rightarrow\\; ${tp(A)}^{${tn(E)}} \\equiv ${tp(A)}^{${tn(r)}} \\equiv ${tn(value)}`,
                prime ? L(`Модуль ${sn(M)} простой и не делит ${sn(A)}, поэтому ${sn(A)}^${sn(ph)} ≡ 1. Значит, от показателя важен только остаток от деления на ${sn(ph)}.`,
                    `The modulus ${sn(M)} is prime and does not divide ${sn(A)}, so ${sn(A)}^${sn(ph)} ≡ 1. Only the remainder of the exponent modulo ${sn(ph)} matters.`)
                    : L(`${sn(A)} взаимно просто с ${sn(M)}, а φ(${sn(M)}) = ${sn(ph)}, поэтому ${sn(A)}^${sn(ph)} ≡ 1. Значит, от показателя важен только остаток от деления на ${sn(ph)}.`,
                        `${sn(A)} is coprime to ${sn(M)} and φ(${sn(M)}) = ${sn(ph)}, so ${sn(A)}^${sn(ph)} ≡ 1. Only the remainder of the exponent modulo ${sn(ph)} matters.`),
                { rule: prime ? 'fermat' : 'euler' }));
        }
    }
    return { value, rows, steps: st };
}

/** Inverse of a modulo m in [0, m), or null when gcd(a, m) ≠ 1. {steps: true} → {value, steps}. */
export function ntModInv(a, m, opts = {}) {
    const A = big(a), M = needModulus(m);
    const value = invCore(A, M);
    if (!opts.steps) return value;
    const st = [];
    const g = gcdCore(A, M);
    st.push(S(L('Что ищем', 'What we look for'), `${tp(A)} \\cdot x \\equiv 1 ${eqv(M)}`,
        L(`Ищем x, для которого ${sn(A)}·x даёт остаток 1 при делении на ${sn(M)}. Это то же самое, что ${sn(A)}·x + ${sn(M)}·y = 1 для какого-то целого y.`,
            `We want x such that ${sn(A)}·x leaves remainder 1 on division by ${sn(M)}, which is the same as ${sn(A)}·x + ${sn(M)}·y = 1 for some integer y.`), { rule: 'inverse-def' }));
    if (M === 1n) {
        st.push(S(L('Модуль 1', 'Modulus 1'), 'x \\equiv 0 \\pmod{1}', L('По модулю 1 все числа сравнимы с нулём.', 'Modulo 1 every number is 0.'), { rule: 'answer' }));
        return { value, steps: st };
    }
    if (value === null) {
        st.push(S(L('Обратного нет', 'No inverse'), T((l) => `${G(l, A, M)} = ${tn(g)} \\ne 1`),
            L(`${sn(A)}·x + ${sn(M)}·y при любых x и y делится на ${sn(g)}, а 1 — нет. Обратный существует только у чисел, взаимно простых с модулем.`,
                `${sn(A)}·x + ${sn(M)}·y is divisible by ${sn(g)} for all x and y, but 1 is not. Only numbers coprime to the modulus have inverses.`),
            { rule: 'answer', sub: gcdSteps(A, M).st }));
        return { value, steps: st };
    }
    const e = ntEgcd(A, M, { steps: true });
    const yP = e.y < 0n ? `(${sn(e.y)})` : sn(e.y);
    st.push(S(L('Расширенный алгоритм Евклида', 'The extended Euclidean algorithm'),
        `${tp(A)} \\cdot ${tp(e.x)} + ${tn(M)} \\cdot ${tp(e.y)} = 1`,
        L('НОД равен 1, и обратный ход алгоритма Евклида даёт нужное представление единицы.', 'The gcd is 1, and running Euclid backwards gives the representation of 1 we need.'),
        { rule: 'egcd', sub: e.steps }));
    st.push(S(L('Отбрасываем кратное модуля', 'Drop the multiple of the modulus'),
        `${tp(A)} \\cdot ${tp(e.x)} \\equiv 1 ${eqv(M)} \\;\\Rightarrow\\; x \\equiv ${e.x !== value ? `${tn(e.x)} \\equiv ` : ''}${tn(value)} ${eqv(M)}`,
        e.x !== value ? L(`Слагаемое ${sn(M)}·${yP} делится на ${sn(M)} и на остаток не влияет. Приводим ${sn(e.x)} к промежутку от 0 до ${sn(M - 1n)}.`,
            `The term ${sn(M)}·${yP} is a multiple of ${sn(M)} and does not affect the remainder. We bring ${sn(e.x)} into the range 0 to ${sn(M - 1n)}.`)
            : L(`Слагаемое ${sn(M)}·${yP} делится на ${sn(M)} и на остаток не влияет.`, `The term ${sn(M)}·${yP} is a multiple of ${sn(M)} and does not affect the remainder.`),
        { rule: 'reduce' }));
    const prod = A * value;
    st.push(S(L('Проверка', 'Check'), `${tp(A)} \\cdot ${tn(value)} = ${tn(prod)} = ${tn((prod - 1n) / M)} \\cdot ${tn(M)} + 1 \\equiv 1 ${eqv(M)}`, null, { rule: 'check' }));
    return { value, steps: st };
}

/**
 * Linear congruence a·x ≡ b (mod m) → {solvable, d, x0, m0, solutions?}: all solutions are
 * x ≡ x0 (mod m0), m0 = m / d, i.e. d residues modulo m (listed in `solutions` when d ≤ 1000).
 */
export function ntSolveCongruence(a, b, m, opts = {}) {
    const A = big(a), B = big(b), M = needModulus(m);
    const a1 = bmod(A, M), b1 = bmod(B, M);
    const d = gcdCore(a1, M); // gcd(0, M) = M
    const st = [];
    const cong = (x, y, mm) => `${coefX(x)} \\equiv ${tn(y)} ${eqv(mm)}`;
    if (opts.steps) {
        st.push(S(L('Что значит сравнение', 'What the congruence means'), cong(A, B, M),
            L(`Нужны такие x, что ${A === 1n ? 'x' : `${sn(A)}·x`} − ${sn(B)} делится на ${sn(M)}.${a1 !== A || b1 !== B ? ` Сначала заменяем коэффициенты остатками от деления на ${sn(M)}: ${sn(a1)}x ≡ ${sn(b1)}.` : ''}`,
                `We need x such that ${A === 1n ? 'x' : `${sn(A)}·x`} − ${sn(B)} is divisible by ${sn(M)}.${a1 !== A || b1 !== B ? ` First replace the coefficients by their remainders modulo ${sn(M)}: ${sn(a1)}x ≡ ${sn(b1)}.` : ''}`),
            { rule: 'congruence-def' }));
        st.push(S(L(`НОД(${sn(a1)}, ${sn(M)}) = ${sn(d)}`, `gcd(${sn(a1)}, ${sn(M)}) = ${sn(d)}`), T((l) => `d = ${G(l, a1, M)} = ${tn(d)}`),
            L('От НОД коэффициента и модуля зависит, сколько решений.', 'The gcd of the coefficient and the modulus decides how many solutions there are.'),
            { rule: 'gcd', sub: gcdSteps(a1, M).st }));
    }
    if (b1 % d !== 0n) {
        const res = { solvable: false, d, x0: null, m0: null, solutions: [] };
        if (opts.steps) {
            st.push(S(L('Решений нет', 'No solutions'), `${tn(d)} \\nmid ${tn(b1)}`,
                L(`Если ${sn(a1)}x − ${sn(b1)} = k·${sn(M)}, то ${sn(b1)} = ${sn(a1)}x − k·${sn(M)} делится на ${sn(d)}, ведь на ${sn(d)} делятся и ${sn(a1)}, и ${sn(M)}. Но ${sn(b1)} на ${sn(d)} не делится — значит, решений нет.`,
                    `If ${sn(a1)}x − ${sn(b1)} = k·${sn(M)}, then ${sn(b1)} = ${sn(a1)}x − k·${sn(M)} is divisible by ${sn(d)}, since both ${sn(a1)} and ${sn(M)} are. But ${sn(b1)} is not, so there are no solutions.`),
                { rule: 'answer' }));
            res.steps = st;
        }
        return res;
    }
    const a2 = a1 / d, b2 = b1 / d, m2 = M / d;
    const inv = invCore(a2, m2);
    const x0 = m2 === 1n ? 0n : bmod(b2 * inv, m2);
    const res = { solvable: true, d, x0, m0: m2 };
    if (d <= 1000n) {
        res.solutions = [];
        for (let k = 0n; k < d; k++) res.solutions.push(x0 + k * m2);
    }
    if (!opts.steps) return res;
    if (a1 === 0n) {
        st.push(S(L('Подходит любое x', 'Every x works'), `0 \\cdot x \\equiv 0 ${eqv(M)}`,
            L('И коэффициент при x, и правая часть делятся на модуль: сравнение верно при любом x.', 'Both the coefficient and the right side are multiples of the modulus: the congruence holds for every x.'), { rule: 'answer' }));
        res.steps = st;
        return res;
    }
    if (d > 1n) {
        st.push(S(L(`Делим всё на ${sn(d)}`, `Divide everything by ${sn(d)}`), `${cong(a1, b1, M)} \\;\\Leftrightarrow\\; ${cong(a2, b2, m2)}`,
            L(`${sn(b1)} делится на ${sn(d)}, значит, решения есть. Делим обе части и модуль на ${sn(d)}: равенство ${sn(a1)}x − ${sn(b1)} = k·${sn(M)} равносильно ${sn(a2)}x − ${sn(b2)} = k·${sn(m2)}.`,
                `${sn(b1)} is divisible by ${sn(d)}, so solutions exist. Divide both sides and the modulus by ${sn(d)}: ${sn(a1)}x − ${sn(b1)} = k·${sn(M)} is the same as ${sn(a2)}x − ${sn(b2)} = k·${sn(m2)}.`),
            { rule: 'divide' }));
    }
    if (m2 === 1n) {
        st.push(S(L('Подходит любое x', 'Every x works'), 'x \\equiv 0 \\pmod{1}', L('По модулю 1 сравнение выполняется всегда.', 'Modulo 1 the congruence always holds.')));
    } else if (a2 !== 1n) {
        const iv = ntModInv(a2, m2, { steps: true });
        st.push(S(L(`Умножаем на обратный к ${sn(a2)}`, `Multiply by the inverse of ${sn(a2)}`),
            `${tn(a2)}^{-1} \\equiv ${tn(inv)} ${eqv(m2)} \\;\\Rightarrow\\; x \\equiv ${tn(b2)} \\cdot ${tn(inv)} = ${tn(b2 * inv)}${b2 * inv !== x0 ? ` \\equiv ${tn(x0)}` : ''} ${eqv(m2)}`,
            L(`${sn(a2)} и ${sn(m2)} взаимно просты, поэтому у ${sn(a2)} есть обратный: ${sn(a2)}·${sn(inv)} = ${sn(a2 * inv)} ≡ 1. Умножив на него обе части, мы как бы делим на ${sn(a2)}.`,
                `${sn(a2)} and ${sn(m2)} are coprime, so ${sn(a2)} has an inverse: ${sn(a2)}·${sn(inv)} = ${sn(a2 * inv)} ≡ 1. Multiplying both sides by it in effect divides by ${sn(a2)}.`),
            { rule: 'inverse', sub: iv.steps }));
    }
    if (d > 1n) {
        st.push(S(L(`${sn(d)} ${ruPl(d, 'решение', 'решения', 'решений')} по модулю ${sn(M)}`, `${sn(d)} solutions modulo ${sn(M)}`),
            res.solutions && d <= 12n ? `x \\equiv ${res.solutions.map(tn).join(',\\ ')} ${eqv(M)}` : `x = ${tn(x0)} + ${tn(m2)}k`,
            L(`Все решения — это x = ${sn(x0)} + ${sn(m2)}k. По исходному модулю ${sn(M)} они дают ровно ${sn(d)} ${ruPl(d, 'остаток', 'разных остатка', 'разных остатков')}.`,
                `All solutions are x = ${sn(x0)} + ${sn(m2)}k. Modulo the original ${sn(M)} they give exactly ${sn(d)} different remainders.`), { rule: 'answer' }));
    } else {
        st.push(S(L('Ответ и проверка', 'Answer and check'), `x \\equiv ${tn(x0)} ${eqv(M)},\\quad ${tn(a1)} \\cdot ${tn(x0)} = ${tn(a1 * x0)} \\equiv ${tn(bmod(a1 * x0, M))} ${eqv(M)}`,
            L(`Решение единственно по модулю ${sn(M)}: x = ${sn(x0)} + ${sn(M)}k.`, `The solution is unique modulo ${sn(M)}: x = ${sn(x0)} + ${sn(M)}k.`), { rule: 'answer' }));
    }
    res.steps = st;
    return res;
}

/**
 * Chinese remainder theorem for any moduli (not necessarily coprime):
 * {solvable: true, x, m} with the answer x (mod m), m = lcm; or {solvable: false, conflict: i}.
 */
export function ntCrt(residues, moduli, opts = {}) {
    if (!Array.isArray(residues) || !Array.isArray(moduli) || residues.length !== moduli.length || !residues.length) {
        throw fail('Нужны два списка одинаковой длины: остатки и модули.', 'Two lists of the same length are needed: remainders and moduli.');
    }
    const rs = residues.map((r) => big(r)), ms = moduli.map((m) => needModulus(m));
    let X = bmod(rs[0], ms[0]), Mx = ms[0];
    const st = [];
    const lin = (c, mult, v) => `${tn(c)} + ${tn(mult)}${v}`;
    if (opts.steps) {
        st.push(S(L('Система сравнений', 'The system'), `\\begin{cases} ${rs.map((r, i) => `x \\equiv ${tn(r)} ${eqv(ms[i])}`).join(' \\\\ ')} \\end{cases}`,
            L('Решаем подстановкой: из первого сравнения выражаем x через новую неизвестную и подставляем в следующее. После каждого шага остаётся одно сравнение, которое заменяет все уже учтённые.',
                'We solve by substitution: express x from the first congruence through a new unknown and plug it into the next one. After each step a single congruence replaces all those used so far.'),
            { rule: 'crt' }));
        st.push(S(L('Из первого сравнения', 'From the first congruence'), `x = ${lin(X, Mx, 't')}`,
            L(`Числа с остатком ${sn(X)} при делении на ${sn(Mx)} — это ${sn(X)} + ${sn(Mx)}t, где t — любое целое.`,
                `Numbers leaving remainder ${sn(X)} on division by ${sn(Mx)} are ${sn(X)} + ${sn(Mx)}t for any integer t.`)));
    }
    const vars = ['t', 's', 'u', 'v', 'w', 'z'];
    for (let i = 1; i < rs.length; i++) {
        const r = bmod(rs[i], ms[i]), m = ms[i];
        const g = gcdCore(Mx, m);
        const diff = bmod(r - X, m);
        const v = vars[(i - 1) % vars.length], vn = vars[i % vars.length];
        if (diff % g !== 0n) {
            const res = { solvable: false, x: null, m: null, conflict: i };
            if (opts.steps) {
                st.push(S(L('Противоречие', 'A contradiction'), `${lin(X, Mx, v)} \\equiv ${tn(r)} ${eqv(m)}`,
                    L(`Модули ${sn(Mx)} и ${sn(m)} имеют общий делитель ${sn(g)}. По модулю ${sn(g)} прежние условия дают остаток ${sn(bmod(X, g))}, а новое — ${sn(bmod(r, g))}. Одно число не может давать два разных остатка, поэтому у системы нет решений.`,
                        `The moduli ${sn(Mx)} and ${sn(m)} share the divisor ${sn(g)}. Modulo ${sn(g)} the conditions so far give remainder ${sn(bmod(X, g))}, but the new one gives ${sn(bmod(r, g))}. One number cannot have two different remainders, so the system has no solutions.`),
                    { rule: 'answer' }));
                res.steps = st;
            }
            return res;
        }
        const m2 = m / g;
        const a = bmod(Mx, m);
        const t0 = m2 === 1n ? 0n : bmod((diff / g) * invCore(Mx / g, m2), m2);
        const newX = X + Mx * t0, newM = Mx * m2;
        if (opts.steps) {
            const trivial = a === 1n && g === 1n;
            let how, sub;
            if (trivial) how = L('', '');
            else if (m2 <= 12n) {
                const at = (a / g) * t0;
                const range = (l) => (m2 === 2n ? (l === 'ru' ? '0 и 1' : '0 and 1') : m2 <= 4n ? [...Array(Number(m2)).keys()].join(', ') : `0, 1, …, ${sn(m2 - 1n)}`);
                const red = g > 1n ? L(` Делим сравнение и модуль на НОД = ${sn(g)}: ${sn(a / g)}${v} ≡ ${sn(diff / g)} (mod ${sn(m2)}).`,
                    ` Divide the congruence and the modulus by the gcd ${sn(g)}: ${sn(a / g)}${v} ≡ ${sn(diff / g)} (mod ${sn(m2)}).`) : L('', '');
                how = L(`${red.ru} Перебираем ${v} = ${range('ru')}: подходит ${v} = ${sn(t0)}, ведь ${sn(a / g)}·${sn(t0)} = ${sn(at)}${at !== bmod(at, m2) ? ` ≡ ${sn(bmod(at, m2))}` : ''}.`,
                    `${red.en} Try ${v} = ${range('en')}: ${v} = ${sn(t0)} works, since ${sn(a / g)}·${sn(t0)} = ${sn(at)}${at !== bmod(at, m2) ? ` ≡ ${sn(bmod(at, m2))}` : ''}.`);
            } else {
                how = L(' Решаем его, умножив на обратный элемент (подробности внутри).', ' We solve it with a modular inverse (details inside).');
                sub = ntSolveCongruence(a, diff, m, { steps: true }).steps;
            }
            st.push(S(L(`Подставляем в ${i + 1}-е сравнение`, `Substitute into congruence ${i + 1}`),
                `${lin(X, Mx, v)} \\equiv ${tn(r)} ${eqv(m)} \\;\\Rightarrow\\; ${coefX(a, v)} \\equiv ${tn(diff)} ${eqv(m)}${trivial ? '' : ` \\;\\Rightarrow\\; ${v} \\equiv ${tn(t0)} ${eqv(m2)}`}`,
                L(`Переносим ${sn(X)} вправо и приводим по модулю ${sn(m)}; получилось линейное сравнение относительно ${v}.${how.ru}`,
                    `Move ${sn(X)} to the right and reduce modulo ${sn(m)}; this is a linear congruence in ${v}.${how.en}`),
                { rule: 'substitute', ...(sub ? { sub } : {}) }));
            st.push(S(L('Новое общее условие', 'The combined condition'),
                `${v} = ${lin(t0, m2, vn)} \\;\\Rightarrow\\; x = ${tn(X)} + ${tn(Mx)}(${lin(t0, m2, vn)}) = ${lin(newX, newM, vn)}`,
                L(`Теперь x задаётся одним условием: x ≡ ${sn(bmod(newX, newM))} (mod ${sn(newM)}).${g > 1n ? ` Модуль — НОК(${sn(Mx)}, ${sn(m)}) = ${sn(newM)}, а не произведение: у модулей общий делитель ${sn(g)}.` : ''}`,
                    `Now x is described by a single condition: x ≡ ${sn(bmod(newX, newM))} (mod ${sn(newM)}).${g > 1n ? ` The modulus is lcm(${sn(Mx)}, ${sn(m)}) = ${sn(newM)}, not the product: the moduli share the divisor ${sn(g)}.` : ''}`),
                { rule: 'combine' }));
        }
        X = bmod(newX, newM);
        Mx = newM;
    }
    const res = { solvable: true, x: X, m: Mx };
    if (opts.steps) {
        const checks = ms.map((mm) => `${sn(X)} = ${sn(X / mm)}·${sn(mm)} + ${sn(bmod(X, mm))}`).join('; ');
        st.push(S(L('Ответ', 'Answer'), `x \\equiv ${tn(X)} ${eqv(Mx)}`,
            L(`Проверка: ${checks}.`, `Check: ${checks}.`), { rule: 'answer' }));
        res.steps = st;
    }
    return res;
}

/** Multiplicative order of a modulo m (the smallest k > 0 with a^k ≡ 1), or null if gcd(a, m) ≠ 1. */
export function ntOrder(a, m) {
    const A = big(a), M = needModulus(m);
    if (M === 1n) return 1n;
    if (gcdCore(A, M) !== 1n) return null;
    let ord = ntPhi(M);
    for (const [p] of factorMap(ord)) {
        while (ord % p === 0n && powmod(A, ord / p, M) === 1n) ord /= p;
    }
    return ord;
}

/** The smallest primitive root modulo m, or null when there is none (it exists for 1, 2, 4, p^k, 2p^k). */
export function ntPrimitiveRoot(m) {
    const M = needModulus(m);
    if (M <= 2n) return M === 1n ? 0n : 1n;
    if (M === 4n) return 3n;
    const odd = M % 2n === 0n ? M / 2n : M;
    if (odd % 2n === 0n || factorMap(odd).size !== 1) return null;
    const ph = ntPhi(M);
    const ps = [...factorMap(ph).keys()];
    for (let g = 2n; g < M; g++) {
        if (gcdCore(g, M) !== 1n) continue;
        if (ps.every((p) => powmod(g, ph / p, M) !== 1n)) return g;
    }
    return null;
}

/** A toy RSA key from primes p ≠ q → {n, phi, e, d}; e is {e} or 65537, else the smallest odd valid e. */
export function ntRsaKey(p, q, opts = {}) {
    const P = big(p), Qn = big(q);
    if (P === Qn || !isPrimeBig(P) || !isPrimeBig(Qn)) throw fail('Нужны два разных простых числа.', 'Two different primes are needed.');
    const n = P * Qn, phi = (P - 1n) * (Qn - 1n);
    let e = opts.e != null ? big(opts.e) : 65537n;
    if (opts.e == null && (e >= phi || gcdCore(e, phi) !== 1n)) {
        e = 3n;
        while (gcdCore(e, phi) !== 1n) e += 2n;
    }
    if (e <= 1n || e >= phi || gcdCore(e, phi) !== 1n) {
        throw fail(`e = ${e} не подходит: нужно 1 < e < φ(n) = ${phi} и НОД(e, φ(n)) = 1.`, `e = ${e} does not work: we need 1 < e < φ(n) = ${phi} and gcd(e, φ(n)) = 1.`);
    }
    const d = invCore(e, phi);
    const res = { n, phi, e, d };
    if (!opts.steps) return res;
    res.steps = [
        S(L('Открытый модуль', 'The public modulus'), `n = p \\cdot q = ${tn(P)} \\cdot ${tn(Qn)} = ${tn(n)}`,
            L('Перемножить два простых легко, а разложить большое n обратно на множители очень трудно. На этом и держится шифр.',
                'Multiplying two primes is easy; factoring a large n back is very hard. The cipher relies on exactly that.'), { rule: 'rsa-n' }),
        S(L('Функция Эйлера', "Euler's function"), `\\varphi(n) = (p - 1)(q - 1) = ${tn(P - 1n)} \\cdot ${tn(Qn - 1n)} = ${tn(phi)}`,
            L('Её знает только владелец ключа: чтобы вычислить φ(n), нужно знать p и q.', 'Only the key owner knows it: computing φ(n) requires p and q.'), { rule: 'rsa-phi' }),
        S(L('Открытая экспонента', 'The public exponent'), T((l) => `e = ${tn(e)},\\quad ${G(l, e, phi)} = 1`),
            L('e должно быть взаимно просто с φ(n), иначе у него не будет обратного.', 'e must be coprime to φ(n), otherwise it has no inverse.'), { rule: 'rsa-e' }),
        S(L('Секретная экспонента', 'The private exponent'), `d \\equiv e^{-1} \\pmod{\\varphi(n)}:\\quad d = ${tn(d)},\\quad ${tn(e)} \\cdot ${tn(d)} = ${tn(e * d)} \\equiv 1 \\pmod{${tn(phi)}}`,
            L('Тогда (m^e)^d ≡ m (mod n) для любого сообщения m — расшифровка отменяет шифрование (по теореме Эйлера).',
                "Then (m^e)^d ≡ m (mod n) for every message m: decryption undoes encryption (by Euler's theorem)."),
            { rule: 'rsa-d', sub: ntModInv(e, phi, { steps: true }).steps }),
    ];
    return res;
}
