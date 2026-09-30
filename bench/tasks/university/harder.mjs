// Первый курс посложнее: интегралы, где нужна находчивость, пределы с неопределённостями 1^∞, 0·∞, ∞ − ∞,
// определённые и несобственные интегралы с известными значениями.
import { set } from '../_helpers.mjs';

const i = set('university', 'integrals-2', 'uni-i2');
const d = set('university', 'definite-2', 'uni-d2');
const l = set('university', 'limits-2', 'uni-l2');

export default [
    // antiderivatives (checked by differentiation)
    i.integrate('sqrt(x^2 + 1)'),
    i.integrate('x^2 sqrt(1 - x^2)'),
    i.integrate('1/(x sqrt(x^2 - 1))'),
    i.integrate('e^x sin(x)'),
    i.integrate('1/cos(x)^3'),
    i.integrate('1/(1 + e^x)'),
    i.integrate('ln(x)^2'),
    i.integrate('arcsin(x)'),
    i.integrate('x arctg(x)'),
    i.integrate('1/(sin(x) + cos(x))'),
    i.integrate('x/(x^4 + 1)'),
    i.integrate('1/(x^3 + 1)'),
    i.integrate('(x + 1)/(x^2 + 2x + 5)^2'),
    i.integrate('1/(2 + cos(x))'),
    i.integrate('sin(x)^4'),
    i.integrate('tg(x)^3'),
    i.integrate('1/(x^2 - 4x + 8)'),
    i.integrate('cos(ln(x))'),
    i.integrate('x^3 e^(x^2)'),
    i.integrate('sqrt(x)/(1 + x)'),
    i.integrate('1/(x^2 (x + 1))'),
    i.integrate('sin(x)cos(3x)'),
    i.integrate('x^2/(1 + x^2)'),
    i.integrate('1/sqrt(4x - x^2)'),
    // definite and improper integrals
    d.integral('x e^x', ['0', '1'], '1'),
    d.integral('x sin(x)', ['0', 'pi'], 'pi'),
    d.integral('ln(x)', ['1', 'e'], '1'),
    d.integral('x^2 e^(-x)', ['0', 'inf'], '2'),
    d.integral('sqrt(1 - x^2)', ['0', '1'], 'pi/4'),
    d.integral('sin(x)^2', ['0', 'pi/2'], 'pi/4'),
    d.integral('1/(1 + x^2)', ['-inf', 'inf'], 'pi'),
    d.integral('1/sqrt(x)', ['0', '1'], '2'),
    d.integral('1/x^2', ['1', 'inf'], '1'),
    d.integral('ln(x)', ['0', '1'], '-1'),
    d.integral('sin(x)^3', ['0', 'pi'], '4/3'),
    d.integral('arctg(x)', ['0', '1'], 'pi/4 - ln(2)/2'),
    // limits
    l.limit('(1 + 2/x)^x', 'inf', 'e^2'),
    l.limit('(sin(x) - x)/x^3', '0', '-1/6'),
    l.limit('x^x', '0', '1'),
    l.limit('(e^x - 1 - x)/x^2', '0', '1/2'),
    l.limit('x (sqrt(x^2 + 1) - x)', 'inf', '1/2'),
    l.limit('1/x - 1/sin(x)', '0', '0'),
    l.limit('(tg(x) - sin(x))/x^3', '0', '1/2'),
    l.limit('(1 - cos(x))/x^2', '0', '1/2'),
    l.limit('x ln(x)', '0', '0'),
    l.limit('(x/(x + 1))^x', 'inf', '1/e'),
    l.limit('cos(x)^(1/x^2)', '0', 'e^(-1/2)'),
    l.limit('x (arctg(x) - pi/2)', 'inf', '-1'),
    l.limit('(2^x - 3^x)/x', '0', 'ln(2) - ln(3)'),
    l.limit('(sqrt(1 + x) - sqrt(1 - x))/x', '0', '1'),
];
