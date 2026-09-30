// ЕГЭ база: вычисления и простые уравнения.
import { set } from '../_helpers.mjs';

const v = set('ege-base', 'values', 'egeb-val');
const e = set('ege-base', 'equations', 'egeb-eq');

export default [
    v.value('(3/5 + 7/10) * 20', '26'),
    v.value('2.7 * 1.3 - 0.51', '3'),
    v.value('(3 * 10^2)^2 * (2 * 10^(-3))', '180'),
    v.value('(2^6 * 3^4)/(6^3)', '24'),
    v.value('sqrt(65^2 - 56^2)', '33'),
    v.value('(sqrt(28) - sqrt(7)) * sqrt(7)', '7'),
    v.value('5^(0.36) * 25^(0.32)', '5'),
    v.value('log_4(64)', '3'),
    v.value('log_3(54) - log_3(2)', '3'),
    v.value('4^(log_4(3))', '3'),
    v.value('(1/3)^(-2) - 2^3', '1'),
    v.value('0.8/(1/3 + 1/5) * 2', '3'),
    e.roots('3^(x - 4) = 27', ['7']),
    e.roots('log_2(8 - x) = 5', ['-24']),
    e.roots('sqrt(x + 7) = 5', ['18']),
    e.roots('5x - 7 = 3x + 11', ['9']),
    e.roots('x^2 - 3x = 0', ['0', '3']),
    e.roots('(x - 5)^2 = x^2', ['5/2']),
    e.roots('2^(3 - x) = 1/16', ['7']),
    e.roots('log_5(x - 2) = 2', ['27']),
];
