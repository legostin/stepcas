// Первый курс: производные (цепное правило, логарифмическое дифференцирование, обратные функции, частные).
import { set } from '../_helpers.mjs';

const t = set('university', 'derivatives', 'uni-diff');

export default [
    t.diff('x^x', 'x^x (ln(x) + 1)'),
    t.diff('sin(x)^cos(x)', 'sin(x)^cos(x) (cos(x)^2/sin(x) - sin(x) ln(sin(x)))'),
    t.diff('arcsin(sqrt(x))', '1/(2sqrt(x) sqrt(1 - x))'),
    t.diff('ln(tg(x/2))', '1/sin(x)'),
    t.diff('e^(x^2) cos(3x)', 'e^(x^2) (2x cos(3x) - 3sin(3x))'),
    t.diff('sh(x)^2', 'sh(2x)'),
    t.diff('arctg((1 + x)/(1 - x))', '1/(1 + x^2)'),
    t.diff('ln(x + sqrt(x^2 + 1))', '1/sqrt(x^2 + 1)'),
    t.diff('x^3 ln(x)^2', 'x^2 ln(x) (3ln(x) + 2)'),
    t.diff('sqrt((1 + x)/(1 - x))', '1/((1 - x)^2 sqrt((1 + x)/(1 - x)))'),
    t.diff('log_2(x^2 + 1)', '2x/((x^2 + 1) ln(2))'),
    t.diff('2^(3x)', '3 ln(2) 2^(3x)'),
    t.diff('cos(x)/(1 + sin(x))', '-1/(1 + sin(x))'),
    t.diff('x arcsin(x) + sqrt(1 - x^2)', 'arcsin(x)'),
    t.diff('tg(x)^3', '3tg(x)^2/cos(x)^2'),
];
