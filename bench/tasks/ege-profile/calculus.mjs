// ЕГЭ профиль, задания 8 и 11: производная, наибольшее и наименьшее значения на отрезке.
import { set } from '../_helpers.mjs';

const t = set('ege-profile', 'calculus', 'egep-calc');

export default [
    t.diff('x^3 - 3x^2 + 2', '3x^2 - 6x'),
    t.diff('sin(2x)', '2cos(2x)'),
    t.diff('x e^x', 'e^x (x + 1)'),
    t.diff('ln(x^2 + 1)', '2x/(x^2 + 1)'),
    t.diff('(x + 1)/(x - 1)', '-2/(x - 1)^2'),
    t.diff('sqrt(x) + 1/x', '1/(2sqrt(x)) - 1/x^2'),
    t.diff('tg(x)', '1/cos(x)^2'),
    t.diff('e^(3x) cos(x)', 'e^(3x) (3cos(x) - sin(x))'),
    t.diff('arctg(2x)', '2/(1 + 4x^2)'),
    t.diff('(x^2 - 1)^5', '10x (x^2 - 1)^4'),
    t.value('3 * 2^2 - 6 * 2', '0', { note: 'f\'(2) для x^3 - 3x^2' }),
    t.extremum('x^3 - 3x + 4', 'max', ['-2', '0'], '6'),
    t.extremum('x^3 - 27x + 19', 'min', ['0', '4'], '-35'),
    t.extremum('(x - 9)e^(x - 8)', 'min', ['7', '9'], '-1'),
    t.extremum('2x^2 - 13x + 9ln(x) + 8', 'max', ['13/14', '15/14'], '-3'),
    t.extremum('11 + 24x - 2x sqrt(x)', 'max', ['63', '65'], '523'),
    t.extremum('7sin(x) - 8x + 9', 'min', ['-3pi/2', '0'], '9'),
    t.extremum('x^3 - 6x^2 + 9x + 3', 'max', ['0', '2'], '7'),
    t.extremum('5ln(x + 5) - 5x', 'max', ['-4.5', '0'], '20'),
    t.extremum('16/x + x + 3', 'min', ['1', '20'], '11'),
    t.extremum('x^3 + 2x^2 + x + 3', 'min', ['-4', '-1'], '-33'),
    t.extremum('(x^2 + 25)/x', 'max', ['-10', '-1'], '-10'),
    t.extremum('3x - 3ln(x + 3)', 'min', ['-2.5', '0'], '-6'),
    t.extremum('e^(2x) - 6e^x + 3', 'min', ['1', '2'], '-6'),
];
