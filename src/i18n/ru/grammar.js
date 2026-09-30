// Russian grammar the templates need: ordinal numerals in the cases a sentence asks for.

const ORDINAL = {
    gen: ['первой', 'второй', 'третьей', 'четвёртой', 'пятой', 'шестой', 'седьмой', 'восьмой', 'девятой', 'десятой'], // (из) второй (строки)
    acc: ['первую', 'вторую', 'третью', 'четвёртую', 'пятую', 'шестую', 'седьмую', 'восьмую', 'девятую', 'десятую'], // (делим) вторую (строку)
    datM: ['первому', 'второму', 'третьему', 'четвёртому', 'пятому', 'шестому'], // (по) второму (столбцу)
};

/** Row n (from 1) in a case: gen «второй строки», acc «вторую строку», accShort «вторую», dat «ко второй строке», loc «во второй строке». */
export const row = {
    gen: (n) => (n <= 10 ? `${ORDINAL.gen[n - 1]} строки` : `строки ${n}`),
    acc: (n) => (n <= 10 ? `${ORDINAL.acc[n - 1]} строку` : `строку ${n}`),
    accShort: (n) => (n <= 10 ? ORDINAL.acc[n - 1] : `строку ${n}`),
    dat: (n) => (n <= 10 ? `${n === 2 ? 'ко' : 'к'} ${ORDINAL.gen[n - 1]} строке` : `к строке ${n}`),
    loc: (n) => (n <= 10 ? `${n === 2 ? 'во' : 'в'} ${ORDINAL.gen[n - 1]} строке` : `в строке ${n}`),
    /** «(по) второй строке» for the first six, else the number. */
    along: (n) => `${ORDINAL.gen.slice(0, 6)[n - 1] ?? n} строке`,
};

/** Column n in the dative: «(по) второму столбцу». */
export const column = {
    along: (n) => `${ORDINAL.datM[n - 1] ?? n} столбцу`,
};

/** The Russian plural form for n: plural(3, 'корень', 'корня', 'корней') → 'корня'. */
export function plural(n, one, few, many) {
    const k = Math.abs(Number(n)) % 100;
    const d = k % 10;
    if (k > 10 && k < 20) return many;
    if (d === 1) return one;
    if (d >= 2 && d <= 4) return few;
    return many;
}

const EQUATION = {
    gen: ['первого', 'второго', 'третьего'], // (из) второго (уравнения)
    acc: ['первое', 'второе', 'третье'], // (подставляем во) второе (уравнение)
};

/** Equation n (from 1): gen «второго», acc «второе», into «во второе». */
export const equation = {
    gen: (n) => EQUATION.gen[n - 1] ?? `${n}-го`,
    acc: (n) => EQUATION.acc[n - 1] ?? `${n}-е`,
    into: (n) => `${n === 2 ? 'во' : 'в'} ${EQUATION.acc[n - 1] ?? `${n}-е`}`,
};

/** The first letter capitalised: «синус» → «Синус». */
export const capital = (s) => (s ? s[0].toUpperCase() + s.slice(1) : s);
