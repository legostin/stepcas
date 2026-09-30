// Первый курс: дифференциальные уравнения с начальными условиями и суммы рядов (у движка пока нет API).
import { set } from '../_helpers.mjs';

const o = set('university', 'ode', 'uni-ode');
const s = set('university', 'series', 'uni-ser');

export default [
    o.ode("y' = 2y; y(0) = 3", '3e^(2x)'),
    o.ode("y'' + y = 0; y(0) = 0; y'(0) = 1", 'sin(x)'),
    o.ode("y' + y = x; y(0) = 1", 'x - 1 + 2e^(-x)'),
    o.ode("y' = x y; y(0) = 1", 'e^(x^2/2)'),
    o.ode("y'' - 3y' + 2y = 0; y(0) = 0; y'(0) = 1", 'e^(2x) - e^x'),
    o.ode("y' = y^2; y(0) = 1", '1/(1 - x)'),
    o.ode("y'' + 4y = 0; y(0) = 1; y'(0) = 0", 'cos(2x)'),
    o.ode("x y' = y; y(1) = 2", '2x'),
    o.ode("y'' - 2y' + y = 0; y(0) = 1; y'(0) = 2", '(1 + x)e^x'),
    o.ode("y' = e^(x - y); y(0) = 0", 'x'),
    s.series('sum(1/k^2, k, 1, inf)', 'pi^2/6'),
    s.series('sum(1/2^k, k, 0, inf)', '2'),
    s.series('sum(1/(k(k + 1)), k, 1, inf)', '1'),
    s.series('sum((-1)^(k + 1)/k, k, 1, inf)', 'ln(2)'),
    s.series('sum(1/k!, k, 0, inf)', 'e'),
    s.series('sum(k^2, k, 1, 10)', '385'),
    s.series('sum(k, k, 1, 100)', '5050'),
    s.series('sum(1/4^k, k, 1, inf)', '1/3'),
    s.series('sum(k/2^k, k, 1, inf)', '2'),
    s.series('sum(1/(4k^2 - 1), k, 1, inf)', '1/2'),
];
