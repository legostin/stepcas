// ЕГЭ профиль, задание 7: значения выражений (логарифмы, степени, корни, тригонометрия).
import { set } from '../_helpers.mjs';

const t = set('ege-profile', 'values', 'egep-val');

export default [
    t.value('log_5(60) - log_5(12)', '1'),
    t.value('log_3(25)/log_3(5)', '2'),
    t.value('36^(log_6(5))', '25'),
    t.value('log_(1/4)(8)', '-3/2'),
    t.value('5^(log_5(7) + 1)', '35'),
    t.value('7^(2log_7(5))', '25'),
    t.value('log_3(8.1) + log_3(10)', '4'),
    t.value('log_2(sqrt(8))', '3/2'),
    t.value('lg(0.001)', '-3'),
    t.value('log_2(56) - log_2(7)', '3'),
    t.value('log_4(log_3(81))', '1'),
    t.value('sqrt(45) * sqrt(5)', '15'),
    t.value('(sqrt(13) - sqrt(7))(sqrt(13) + sqrt(7))', '6'),
    t.value('2^(3sqrt(7) - 1) * 8^(1 - sqrt(7))', '4'),
    t.value('(9^(1/2) * 9^(1/3))^(6/5)', '9'),
    t.value('(2^(1/3) * 2^(1/2))^6', '32'),
    t.value('(sqrt(3))^4 * 3^(-1)', '3'),
    t.value('(0.8)^(1/7) * 5^(2/7) * 20^(6/7)', '20'),
    t.value('-18sqrt(2) sin(-135°)', '18'),
    t.value('36sqrt(6) tg(pi/6) sin(pi/4)', '36'),
    t.value('sin(7pi/6) + cos(pi/3)', '0'),
    t.value('5tg(5pi/4)', '5'),
    t.value('16cos(pi/8)^2 - 8', '4sqrt(2)'),
    t.value('sqrt(2) cos(pi/4)^2 * sqrt(2)', '1'),
    t.value('24sqrt(2) cos(-pi/3) sin(-pi/4)', '-12'),
    t.value('14sin(19pi/12) cos(19pi/12)', '-7/2'),
    t.value('(12sin(11°) cos(11°))/sin(22°)', '6'),
    t.value('5sin(98°)/(sin(49°) sin(41°))', '10'),
    t.value('(3^(5.3) * 5^(4.3))/15^(3.3)', '45'),
    t.value('((2/9)^(-1)) - 0.5', '4'),
];
