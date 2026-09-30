// ЕНТ (Казахстан), профильная математика: уравнения, неравенства, системы, производные, первообразные и интегралы,
// тригонометрия, логарифмы, значения выражений.
import { set } from '../_helpers.mjs';

const e = set('ent', 'equations', 'ent-eq');
const tr = set('ent', 'trig', 'ent-trig');
const i = set('ent', 'inequalities', 'ent-ineq');
const s = set('ent', 'systems', 'ent-sys');
const d = set('ent', 'derivatives', 'ent-diff');
const g = set('ent', 'integrals', 'ent-int');
const v = set('ent', 'values', 'ent-val');

export default [
    e.roots('sqrt(x + 5) = x - 1', ['4']),
    e.roots('2^(x + 2) - 2^x = 12', ['2']),
    e.roots('log_2(x) + log_2(x + 2) = 3', ['2']),
    e.roots('lg(x + 6) - lg(2x - 3) = lg(4)', ['18/7']),
    e.roots('9^x - 10 * 3^x + 9 = 0', ['0', '2']),
    e.roots('x^2 - 2|x| - 3 = 0', ['-3', '3']),
    e.roots('(x^2 - x)^2 - 8(x^2 - x) + 12 = 0', ['-2', '-1', '2', '3']),
    e.roots('x^(log_3(x)) = 81', ['9', '1/9']),
    e.roots('sqrt(2x - 1) + sqrt(x - 1) = 5', ['5']),
    e.roots('3^(2x + 1) - 10 * 3^x + 3 = 0', ['-1', '1']),
    e.roots('log_3(x)^2 - log_3(x) - 2 = 0', ['1/3', '9']),
    e.roots('(x + 1)/(x - 1) - (x - 1)/(x + 1) = 8/3', ['2', '-1/2']),
    e.roots('x^3 - 2x^2 - x + 2 = 0', ['-1', '1', '2']),
    e.roots('|x^2 - 4| = 3x', ['1', '4']),
    tr.fams('sin(x)cos(x) = 1/4', [
        ['pi/12', 'pi'],
        ['5pi/12', 'pi'],
    ]),
    tr.fams('cos(2x) = -1', [['pi/2', 'pi']]),
    tr.fams('tg(x + pi/4) = 1', [['0', 'pi']]),
    tr.fams('2cos(x) - 1 = 0', [
        ['pi/3', '2pi'],
        ['-pi/3', '2pi'],
    ]),
    tr.fams('sin(x)^2 = 1/4', [
        ['pi/6', 'pi'],
        ['-pi/6', 'pi'],
    ]),
    tr.fams('cos(x)^2 - cos(x) = 0', [
        ['pi/2', 'pi'],
        ['0', '2pi'],
    ]),
    tr.fams('sin(3x) = sqrt(2)/2', [
        ['pi/12', '2pi/3'],
        ['pi/4', '2pi/3'],
    ]),
    tr.onInterval('cos(x) = 1/2', ['0', '2pi'], ['pi/3', '5pi/3']),
    i.ineq('(x - 1)/(x + 2) <= 0', '(-2; 1]'),
    i.ineq('log_(1/3)(x - 1) >= -1', '(1; 4]'),
    i.ineq('2^(x^2 - 2x) < 8', '(-1; 3)'),
    i.ineq('sqrt(x - 2) > 1', '(3; +inf)'),
    i.ineq('x^2 - 7x + 10 >= 0', '(-inf; 2] U [5; +inf)'),
    i.ineq('|x + 1| <= 2', '[-3; 1]'),
    i.ineq('(1/2)^(x - 1) > 4', '(-inf; -1)'),
    i.ineq('log_2(x^2 - 3x) < 2', '(-1; 0) U (3; 4)'),
    s.system('x + y = 5; x y = 6', [
        ['2', '3'],
        ['3', '2'],
    ]),
    s.system('2x - y = 1; x^2 + y = 7', [
        ['2', '3'],
        ['-4', '-9'],
    ]),
    s.system('3x + 4y = 18; 5x - 2y = 4', [['2', '3']]),
    s.system('x - y = 2; x^2 - y^2 = 16', [['5', '3']]),
    d.diff('x^4 - 2x^2', '4x^3 - 4x'),
    d.diff('cos(x^2)', '-2x sin(x^2)'),
    d.diff('ln(3x)', '1/x'),
    d.diff('x/(x^2 + 1)', '(1 - x^2)/(x^2 + 1)^2'),
    d.diff('e^(-x) sin(x)', 'e^(-x) (cos(x) - sin(x))'),
    d.diff('(2x + 1)^10', '20(2x + 1)^9'),
    d.diff('sqrt(x^2 + 9)', 'x/sqrt(x^2 + 9)'),
    g.integral('3x^2 + 2x', ['0', '1'], '2'),
    g.integral('cos(x)', ['0', 'pi/2'], '1'),
    g.integral('e^x', ['0', 'ln(2)'], '1'),
    g.integral('1/x', ['1', 'e'], '1'),
    g.integral('sin(2x)', ['0', 'pi/4'], '1/2'),
    g.integral('sqrt(x)', ['0', '4'], '16/3'),
    g.integral('x^3', ['-1', '1'], '0'),
    g.integral('2x - 1', ['1', '3'], '6'),
    g.integral('1/(x + 1)', ['0', 'e - 1'], '1'),
    g.integral('4/x^2', ['1', '2'], '2'),
    g.integral('x^2 - 2x', ['0', '3'], '0'),
    g.integrate('3x^2 - 4x + 5'),
    g.integrate('cos(3x)'),
    g.integrate('e^(2x)'),
    g.integrate('1/(2x + 1)'),
    g.integrate('1/cos(x)^2'),
    g.integrate('(x + 1)^5'),
    v.value('log_2(32) + log_3(1/9)', '3'),
    v.value('sin(15°) cos(15°)', '1/4'),
    v.value('cos(15°)^2 - sin(15°)^2', 'sqrt(3)/2'),
    v.value('27^(2/3) - 16^(3/4)', '1'),
    v.value('sqrt(3 + 2sqrt(2)) - sqrt(2)', '1'),
    v.value('6!/(2! 4!)', '15'),
    v.value('5!/3!', '20'),
    v.value('sin(pi/6) + cos(pi/3) + tg(pi/4)', '2'),
    v.value('log_6(2) + log_6(18)', '2'),
];
