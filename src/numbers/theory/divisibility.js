// theory/divisibility — divisibility rules explained on the number.

import { L, S, babs, big, bmod, fail, sn, tn } from './common.js';

// ---------------------------------------------------------------- divisibility rules

const RULE_BASES = [2, 3, 4, 5, 8, 9, 10, 11, 25];
const RULE_COMBOS = { 6: [2, 3], 12: [3, 4], 15: [3, 5], 18: [2, 9], 20: [4, 5], 36: [4, 9], 45: [5, 9], 75: [3, 25], 100: [4, 25] };

function ruleFor(s, d) {
    // s — the decimal digits of |n|
    const last = s[s.length - 1];
    if (d === 2 || d === 5 || d === 10) {
        const ok = d === 2 ? '02468'.includes(last) : d === 5 ? '05'.includes(last) : last === '0';
        const need = d === 2 ? L('чётная (0, 2, 4, 6 или 8)', 'even (0, 2, 4, 6 or 8)') : d === 5 ? L('0 или 5', '0 or 5') : L('0', '0');
        return {
            divides: ok,
            tex: s.length > 1 ? `\\ldots${last}` : last,
            text: L(`Последняя цифра — ${last}. Число делится на ${d} тогда и только тогда, когда его последняя цифра ${need.ru}. ${ok ? 'Делится.' : 'Не делится.'}`,
                `The last digit is ${last}. A number is divisible by ${d} exactly when its last digit is ${need.en}. ${ok ? 'It is divisible.' : 'It is not divisible.'}`),
            why: L(`Число = (число десятков)·10 + последняя цифра, а 10 делится на ${d}. Значит, всё решает последняя цифра.`,
                `The number = (number of tens)·10 + last digit, and 10 is divisible by ${d}. So only the last digit matters.`),
        };
    }
    if (d === 4 || d === 25 || d === 8) {
        const k = d === 8 ? 3 : 2;
        const t = BigInt(s.slice(-k));
        const D = BigInt(d);
        const ok = t % D === 0n;
        const pw = d === 8 ? '1000' : '100';
        return {
            divides: ok,
            tex: ok ? `${tn(t)} = ${d} \\cdot ${tn(t / D)}` : `${tn(t)} = ${d} \\cdot ${tn(t / D)} + ${tn(t % D)}`,
            text: L(`Смотрим на ${s.length > k ? `последние ${k === 2 ? 'две цифры' : 'три цифры'}` : 'само число'}: ${sn(t)}. ${ok ? `${sn(t)} делится на ${d} — значит, и всё число делится.` : `${sn(t)} на ${d} не делится (остаток ${sn(t % D)}) — значит, и число не делится.`}`,
                `Look at ${s.length > k ? `the last ${k === 2 ? 'two' : 'three'} digits` : 'the number itself'}: ${sn(t)}. ${ok ? `${sn(t)} is divisible by ${d}, so the whole number is.` : `${sn(t)} is not divisible by ${d} (remainder ${sn(t % D)}), so neither is the number.`}`),
            why: L(`${pw} делится на ${d}, поэтому разряды начиная с ${pw === '100' ? 'сотен' : 'тысяч'} на делимость не влияют.`,
                `${pw} is divisible by ${d}, so the places from the ${pw === '100' ? 'hundreds' : 'thousands'} up do not matter.`),
        };
    }
    if (d === 3 || d === 9) {
        const chain = [];
        let cur = s;
        let sum;
        do {
            sum = cur.split('').reduce((acc, c) => acc + BigInt(c), 0n);
            chain.push({ digits: cur, sum });
            cur = sum.toString();
        } while (sum >= 100n && chain.length < 5);
        const D = BigInt(d);
        const ok = sum % D === 0n;
        return {
            divides: ok,
            tex: chain.map((c) => (c.digits.length <= 24 ? `${c.digits.split('').join(' + ')} = ${tn(c.sum)}` : `\\ldots = ${tn(c.sum)}`)).join(',\\quad '),
            text: L(`Сумма цифр — ${sn(sum)}${chain.length > 1 ? ' (цифры складывали несколько раз)' : ''}. ${ok ? `${sn(sum)} делится на ${d}, значит, и число делится.` : `${sn(sum)} на ${d} не делится (остаток ${sn(sum % D)}), значит, и число не делится — и даёт тот же остаток.`}`,
                `The digit sum is ${sn(sum)}${chain.length > 1 ? ' (we added digits more than once)' : ''}. ${ok ? `${sn(sum)} is divisible by ${d}, so the number is too.` : `${sn(sum)} is not divisible by ${d} (remainder ${sn(sum % D)}), so neither is the number — and it leaves the same remainder.`}`),
            why: L(`10, 100, 1000, … дают остаток 1 при делении на ${d} (например, 100 = 99 + 1), поэтому число и сумма его цифр дают одинаковые остатки.`,
                `10, 100, 1000, … all leave remainder 1 when divided by ${d} (for example, 100 = 99 + 1), so a number and its digit sum leave the same remainder.`),
        };
    }
    // d === 11
    const ds = s.split('').reverse().map(Number);
    let odd = 0, even = 0;
    ds.forEach((v, i) => { if (i % 2 === 0) odd += v; else even += v; });
    const diff = odd - even;
    const ok = diff % 11 === 0;
    const oddDigits = ds.filter((_, i) => i % 2 === 0), evenDigits = ds.filter((_, i) => i % 2 === 1);
    return {
        divides: ok,
        tex: `(${oddDigits.join(' + ') || '0'}) - (${evenDigits.join(' + ') || '0'}) = ${odd} - ${even} = ${diff}`,
        text: L(`Складываем цифры через одну, начиная с последней (${odd}), и отдельно остальные (${even}). Разность ${sn(diff)} ${ok ? 'делится на 11 — значит, и число делится.' : 'на 11 не делится — значит, и число не делится.'}`,
            `Add every other digit starting from the last one (${odd}) and, separately, the rest (${even}). The difference ${sn(diff)} ${ok ? 'is divisible by 11, so the number is too.' : 'is not divisible by 11, so neither is the number.'}`),
        why: L('10 = 11 − 1, поэтому 10 ≡ −1, 100 ≡ 1, 1000 ≡ −1, … по модулю 11: разряды входят в остаток попеременно с плюсом и минусом.',
            '10 = 11 − 1, so 10 ≡ −1, 100 ≡ 1, 1000 ≡ −1, … modulo 11: the places enter the remainder with alternating signs.'),
    };
}

/**
 * A divisibility test with an explanation, d ∈ {2, 3, 4, 5, 8, 9, 10, 11, 25} or one of the
 * combinations 6, 12, 15, 18, 20, 36, 45, 75, 100 → {divides, remainder, steps}.
 */
export function ntDivisibilityRule(n, d) {
    const N = big(n);
    const D = Number(d);
    const s = babs(N).toString();
    const remainder = bmod(N, BigInt(D || 1));
    if (RULE_BASES.includes(D)) {
        const r = ruleFor(s, D);
        return {
            divides: r.divides, remainder,
            steps: [
                S(L(`Признак делимости на ${D}`, `The test for ${D}`), r.tex, r.text, { rule: `div-${D}` }),
                S(L('Почему это работает', 'Why it works'), null, r.why, { rule: 'why' }),
            ],
        };
    }
    if (RULE_COMBOS[D]) {
        const [p, q] = RULE_COMBOS[D];
        const a = ruleFor(s, p), b = ruleFor(s, q);
        const ok = a.divides && b.divides;
        return {
            divides: ok, remainder,
            steps: [
                S(L(`Делимость на ${D} — это делимость на ${p} и на ${q}`, `Divisible by ${D} means divisible by ${p} and by ${q}`), `${D} = ${p} \\cdot ${q}`,
                    L(`${p} и ${q} взаимно просты, поэтому число делится на ${D} ровно тогда, когда делится и на ${p}, и на ${q}.`,
                        `${p} and ${q} are coprime, so a number is divisible by ${D} exactly when it is divisible by both ${p} and ${q}.`), { rule: 'combo' }),
                S(L(`Проверяем делимость на ${p}`, `Test for ${p}`), a.tex, a.text, { rule: `div-${p}`, sub: [S(L('Почему это работает', 'Why it works'), null, a.why)] }),
                S(L(`Проверяем делимость на ${q}`, `Test for ${q}`), b.tex, b.text, { rule: `div-${q}`, sub: [S(L('Почему это работает', 'Why it works'), null, b.why)] }),
                S(L('Вывод', 'Conclusion'), null, ok ? L(`Оба признака выполнены: ${sn(N)} делится на ${D}.`, `Both tests pass: ${sn(N)} is divisible by ${D}.`)
                    : L(`Хотя бы один признак не выполнен: ${sn(N)} на ${D} не делится.`, `At least one test fails: ${sn(N)} is not divisible by ${D}.`), { rule: 'answer' }),
            ],
        };
    }
    throw fail(`Для ${D} признака делимости в движке нет.`, `There is no divisibility rule for ${D} in the engine.`, 'unsupported');
}
