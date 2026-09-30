// Russian mathematical notation: how numbers, lists, intervals and functions are written in a Russian school.
export default {
    decimalTex: '{,}', // 2{,}5 — the decimal comma
    decimalText: ',',
    thousandsComma: false, // 1,000 is one point zero, not a thousand
    listTex: ';\\ ', // numbers are separated by semicolons, since the comma is the decimal separator
    listText: '; ',
    listWideTex: ';\\quad ',
    intervalTex: ';\\,', // (1;\,2)
    log10Text: 'lg',
    log10Tex: '\\lg',
    combinedSine: true, // sin x = a: x = (−1)ⁿ arcsin a + πn, one formula
    identity: 'E', // the identity matrix
    // words people type in answers (read in any registered language)
    words: {
        none: ['нет решений', 'нет корней', 'решений нет', 'корней нет'],
        all: ['любое число', 'любое', 'все'],
        or: ['или'],
        infinity: ['бесконечность'],
        sum: ['сумма'],
    },
    fnTex: {
        tan: '\\operatorname{tg}',
        cot: '\\operatorname{ctg}',
        csc: '\\operatorname{cosec}',
        atan: '\\operatorname{arctg}',
        acot: '\\operatorname{arcctg}',
        sinh: '\\operatorname{sh}',
        cosh: '\\operatorname{ch}',
        tanh: '\\operatorname{th}',
        coth: '\\operatorname{cth}',
        asinh: '\\operatorname{arsh}',
        acosh: '\\operatorname{arch}',
        atanh: '\\operatorname{arth}',
        lg: '\\lg',
    },
    fnText: { tan: 'tg', cot: 'ctg', asin: 'arcsin', acos: 'arccos', atan: 'arctg', acot: 'arcctg', sinh: 'sh', cosh: 'ch', tanh: 'th', coth: 'cth', asinh: 'arsh', acosh: 'arch', atanh: 'arth' },
};
