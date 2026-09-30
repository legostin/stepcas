// ЕГЭ профиль, задание 14 (бывшее 15): неравенства.
import { set } from '../_helpers.mjs';

const t = set('ege-profile', 'inequalities', 'egep-ineq');

export default [
    t.ineq('log_2(x - 1) < 3', '(1; 9)'),
    t.ineq('log_(1/2)(2x + 1) > -2', '(-1/2; 3/2)'),
    t.ineq('(x - 1)(x + 3)/(x - 2) >= 0', '[-3; 1] U (2; +inf)'),
    t.ineq('x^2 - 5x + 6 < 0', '(2; 3)'),
    t.ineq('2^x > 8', '(3; +inf)'),
    t.ineq('(1/3)^x <= 9', '[-2; +inf)'),
    t.ineq('4^x - 5 * 2^x + 4 <= 0', '[0; 2]'),
    t.ineq('9^x - 4 * 3^x + 3 > 0', '(-inf; 0) U (1; +inf)'),
    t.ineq('log_3(x^2 - x) <= log_3(x + 3)', '[-1; 0) U (1; 3]'),
    t.ineq('(x^2 - 4)/(x + 1) < 0', '(-inf; -2) U (-1; 2)'),
    t.ineq('|x - 2| < 3', '(-1; 5)'),
    t.ineq('|2x + 1| >= 5', '(-inf; -3] U [2; +inf)'),
    t.ineq('sqrt(x + 2) < 3', '[-2; 7)'),
    t.ineq('x^3 - 4x > 0', '(-2; 0) U (2; +inf)'),
    t.ineq('(x - 3)^2 (x + 1) <= 0', '(-inf; -1] U {3}'),
    t.ineq('log_2(x) + log_2(x - 2) > 3', '(4; +inf)'),
    t.ineq('(x + 2)/(x - 5) <= 0', '[-2; 5)'),
    t.ineq('x^2 >= 16', '(-inf; -4] U [4; +inf)'),
    t.ineq('25^x - 6 * 5^x + 5 < 0', '(0; 1)'),
    t.ineq('log_(0.5)(x - 3) >= -1', '(3; 5]'),
    t.ineq('(x^2 - 9)/(x^2 - 4) >= 0', '(-inf; -3] U (-2; 2) U [3; +inf)'),
    t.ineq('lg(x)^2 - lg(x) - 2 <= 0', '[1/10; 100]'),
    t.ineq('3^(x + 1) + 3^x < 108', '(-inf; 3)'),
    t.ineq('1/(x - 1) + 1/(x + 1) >= 0', '(-1; 0] U (1; +inf)'),
];
