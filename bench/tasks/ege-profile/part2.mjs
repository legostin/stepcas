// ЕГЭ профиль, вторая часть: неравенства (№15) с заменой, переменным основанием, модулями; уравнения (№12–13)
// посложнее; задачи с параметром (№18) через графики. Ответы — вручную, затем проверены SymPy.
import { set } from '../_helpers.mjs';

const i = set('ege-profile', 'ineq-2', 'egep-i2');
const e = set('ege-profile', 'eq-2', 'egep-e2');
const t = set('ege-profile', 'trig-2', 'egep-t2');
const p = set('ege-profile', 'param-2', 'egep-p2');

export default [
    // №15: substitution, exponents
    i.ineq('4^x - 3*2^x + 2 <= 0', '[0; 1]'),
    i.ineq('9^x - 4*3^x + 3 > 0', '(-inf; 0) U (1; +inf)'),
    i.ineq('25^x - 6*5^x + 5 < 0', '(0; 1)'),
    i.ineq('3^(x + 1) + 3^(x - 1) < 30', '(-inf; 2)'),
    i.ineq('2^x + 2^(1 - x) <= 3', '[0; 1]'),
    i.ineq('(1/2)^(x^2 - 2x) >= 1/8', '[-1; 3]'),
    i.ineq('2^(x^2) <= 4*2^x', '[-1; 2]'),
    i.ineq('(2^x - 4)(x - 3) <= 0', '[2; 3]'),
    // №15: logarithms
    i.ineq('log_2(x^2 - 4x) < 5', '(-4; 0) U (4; 8)'),
    i.ineq('log_(1/3)(x - 1) >= -2', '(1; 10]'),
    i.ineq('log_2(x)^2 - 3log_2(x) + 2 >= 0', '(0; 2] U [4; +inf)'),
    i.ineq('lg(x)^2 >= lg(x) + 2', '(0; 1/10] U [100; +inf)'),
    i.ineq('log_2(x) + log_2(x - 3) <= 2', '(3; 4]'),
    i.ineq('log_(1/2)(x^2 - 3x) >= -2', '[-1; 0) U (3; 4]'),
    i.ineq('log_x(x + 2) < 2', '(0; 1) U (2; +inf)'),
    i.ineq('(x - 2)/log_2(x) > 0', '(0; 1) U (2; +inf)'),
    i.ineq('(x - 1)*log_3(x) >= 0', '(0; +inf)'),
    // №15: rational, radical, modulus
    i.ineq('(x^2 - x - 2)/(x - 3) >= 0', '[-1; 2] U (3; +inf)'),
    i.ineq('sqrt(x + 2) > x', '[-2; 2)'),
    i.ineq('|x - 1| + |x + 2| < 5', '(-3; 2)'),
    i.ineq('(x^2 - 1)/(x^2 - 4) <= 0', '(-2; -1] U [1; 2)'),
    i.ineq('x/(x - 1) + 1/(x + 1) >= 1', '(-1; 0] U (1; +inf)'),
    // №13: equations
    e.roots('log_2(x^2 - 3x) = 2', ['-1', '4']),
    e.roots('4^x - 5*2^x + 4 = 0', ['0', '2']),
    e.roots('log_2(x + 1) - log_2(x - 1) = 1', ['3']),
    e.roots('x^(log_2(x)) = 16', ['1/4', '4']),
    e.roots('log_x(16) = 2', ['4']),
    e.roots('9^x - 2*3^(x + 1) - 27 = 0', ['2']),
    e.roots('2^(x + 2) - 2^x = 96', ['5']),
    e.roots('sqrt(2x + 3) - sqrt(x + 1) = 1', ['-1', '3']),
    e.roots('|x^2 - 4x| = 3x', ['0', '1', '7']),
    e.roots('lg(x^2 - 15) = lg(2x)', ['5']),
    // №12: trigonometric equations
    t.fams('2sin(x)^2 + 3cos(x) = 0', [['2pi/3', '2pi'], ['-2pi/3', '2pi']]),
    t.fams('sin(2x) = sqrt(3)cos(x)', [['pi/2', 'pi'], ['pi/3', '2pi'], ['2pi/3', '2pi']]),
    t.fams('cos(2x) + sin(x)^2 = 1/2', [['pi/4', 'pi/2']]),
    t.fams('2cos(x)^2 - sin(x) - 1 = 0', [['pi/6', '2pi'], ['5pi/6', '2pi'], ['-pi/2', '2pi']]),
    t.onInterval('2cos(x)^2 - sin(x) - 1 = 0', ['pi', '5pi/2'], ['3pi/2', '13pi/6']),
    t.onInterval('sin(2x) = sqrt(3)cos(x)', ['-3pi/2', '0'], ['-3pi/2', '-4pi/3', '-pi/2']),
    // №18: parameters through graphs
    p.param('|x| = a x + 1', '(-inf; -1] U [1; +inf)', { param: 'a', want: 'one-root' }),
    p.param('x^2 - 4|x| + 3 = a', '(-1; 3)', { param: 'a', want: 4 }),
    p.param('sqrt(4 - x^2) = a', '[0; 2)', { param: 'a', want: 'two-roots' }),
    p.param('x^2 - 2x = a', '(-1; +inf)', { param: 'a', want: 'two-roots' }),
    p.param('e^x = a x', '(e; +inf)', { param: 'a', want: 'two-roots' }),
];
