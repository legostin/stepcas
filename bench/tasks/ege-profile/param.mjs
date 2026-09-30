// ЕГЭ профиль, задание 18: задачи с параметром (у движка пока нет API — это цель).
import { set } from '../_helpers.mjs';

const t = set('ege-profile', 'param', 'egep-param');

export default [
    t.param('x^2 - 2a x + 4 = 0', '(-inf; -2) U (2; +inf)', { param: 'a', want: 'two-roots' }),
    t.param('x^2 + 4x + a = 0', '(-inf; 4)', { param: 'a', want: 'two-roots' }),
    t.param('a x^2 + 2x + 1 = 0', '{0} U {1}', { param: 'a', want: 'one-root' }),
    t.param('|x - 2| = a', '(0; +inf)', { param: 'a', want: 'two-roots' }),
    t.param('x^2 - (a + 1)x + a = 0', '{1}', { param: 'a', want: 'one-root' }),
    t.param('sqrt(x) = a - x', '[0; +inf)', { param: 'a', want: 'has-roots' }),
    t.param('x^2 + a x + 9 = 0', '(-inf; -6) U (6; +inf)', { param: 'a', want: 'two-roots' }),
    t.param('(a - 1)x^2 + 2x - 3 = 0', '{2/3} U {1}', { param: 'a', want: 'one-root' }),
];
