// ЕГЭ профиль, задание 12 (бывшее 13): тригонометрические уравнения — общее решение и отбор корней на отрезке.
import { set } from '../_helpers.mjs';

const t = set('ege-profile', 'trig', 'egep-trig');

export default [
    t.fams('2cos(x)^2 - 3cos(x) + 1 = 0', [
        ['0', '2pi'],
        ['pi/3', '2pi'],
        ['-pi/3', '2pi'],
    ]),
    t.onInterval('2cos(x)^2 - 3cos(x) + 1 = 0', ['-2pi', '-pi/2'], ['-2pi', '-5pi/3']),
    t.fams('2sin(x)^2 + sin(x) - 1 = 0', [
        ['pi/6', '2pi'],
        ['5pi/6', '2pi'],
        ['-pi/2', '2pi'],
    ]),
    t.onInterval('2sin(x)^2 + sin(x) - 1 = 0', ['-5pi/2', '-pi'], ['-5pi/2', '-11pi/6', '-7pi/6']),
    t.fams('cos(2x) + sin(x) = 0', [
        ['pi/2', '2pi'],
        ['-pi/6', '2pi'],
        ['-5pi/6', '2pi'],
    ]),
    t.onInterval('cos(2x) + sin(x) = 0', ['0', '2pi'], ['pi/2', '7pi/6', '11pi/6']),
    t.onInterval('sin(2x) = cos(x)', ['0', '2pi'], ['pi/6', 'pi/2', '5pi/6', '3pi/2']),
    t.onInterval('tg(x)^2 - tg(x) = 0', ['0', 'pi'], ['0', 'pi/4', 'pi']),
    t.onInterval('4sin(x)^2 = 3', ['0', 'pi'], ['pi/3', '2pi/3']),
    t.onInterval('sqrt(3)tg(x) + 1 = 0', ['0', '2pi'], ['5pi/6', '11pi/6']),
    t.onInterval('cos(x)^2 - sin(x)^2 = 1/2', ['0', 'pi'], ['pi/6', '5pi/6']),
    t.onInterval('2cos(x)^2 + sqrt(3)cos(x) = 0', ['0', '2pi'], ['pi/2', '5pi/6', '7pi/6', '3pi/2']),
    t.fams('sin(x) = 1/2', [
        ['pi/6', '2pi'],
        ['5pi/6', '2pi'],
    ]),
    t.fams('cos(x) = -sqrt(2)/2', [
        ['3pi/4', '2pi'],
        ['-3pi/4', '2pi'],
    ]),
    t.fams('tg(x) = sqrt(3)', [['pi/3', 'pi']]),
    t.fams('sin(2x) = 0', [['0', 'pi/2']]),
    t.fams('2sin(x)cos(x) + cos(x) = 0', [
        ['pi/2', 'pi'],
        ['-pi/6', '2pi'],
        ['-5pi/6', '2pi'],
    ]),
    t.fams('sin(x) + cos(x) = 1', [
        ['0', '2pi'],
        ['pi/2', '2pi'],
    ]),
    t.fams('sin(x)^2 - 3sin(x)cos(x) + 2cos(x)^2 = 0', [
        ['pi/4', 'pi'],
        ['atan(2)', 'pi'],
    ]),
    t.onInterval('2sin(x)^2 - sqrt(3)sin(2x) = 0', ['-3pi/2', '0'], ['-pi', '-2pi/3', '0']),
    t.onInterval('cos(2x) = 1 - cos(pi/2 - x)', ['-5pi/2', '-pi'], ['-2pi', '-11pi/6', '-7pi/6', '-pi']),
    t.onInterval('2^(2cos(x)) = 2', ['0', '2pi'], ['pi/3', '5pi/3']),
    t.onInterval('log_2(sin(x)) = -1', ['0', '2pi'], ['pi/6', '5pi/6']),
];
