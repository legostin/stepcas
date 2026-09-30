// Helpers for writing tasks compactly. Every task: {id, source, topic, op, task, answer, …}.
// Expressions use the engine's input syntax (x^2, sqrt(x), log_2(x), sin x, pi); answers are exact strings.
export function set(source, topic, prefix) {
    let n = 0;
    const id = () => `${prefix}-${String(++n).padStart(3, '0')}`;
    const base = (op, task, answer, extra = {}) => ({ id: id(), source, topic, op, task, answer, ...extra });
    return {
        roots: (task, roots, extra) => base('solve', task, { roots }, extra),
        none: (task, extra) => base('solve', task, { none: true }, extra),
        fams: (task, families, extra) => base('solve', task, { families }, extra),
        pick: (task, ask, value, extra) => base('solve', task, { value }, { ask, ...extra }),   // ЕГЭ: «в ответ запишите меньший корень»
        onInterval: (task, interval, roots, extra) => base('solve', task, { roots }, { interval, ...extra }),
        ineq: (task, setText, extra) => base('ineq', task, { set: setText }, extra),
        system: (task, solutions, extra) => base('system', task, solutions === null ? { none: true } : { solutions }, extra),
        value: (task, value, extra) => base('value', task, { value }, extra),
        diff: (task, expr, extra) => base('diff', task, { expr }, extra),
        integrate: (task, extra) => base('integrate', task, {}, extra),
        integral: (task, bounds, value, extra) => base('integral', task, { value }, { bounds, ...extra }),
        limit: (task, at, value, extra) => base('limit', task, { value }, { at, ...extra }),
        extremum: (task, kind, segment, value, extra) => base('extremum', task, { value }, { kind, segment, ...extra }),
        param: (task, setText, extra) => base('param', task, { set: setText }, extra),
        ode: (task, expr, extra) => base('ode', task, { expr }, extra),
        series: (task, value, extra) => base('series', task, { value }, extra),
        simplify: (task, expr, extra) => base('simplify', task, { expr }, extra),
        factor: (task, expr, extra) => base('factor', task, { expr }, extra),
        matrix: (op, matrix, answer, extra) => base(op, JSON.stringify(matrix), answer, { matrix, ...extra }),
        nt: (op, args, value, extra) => base(op, args.join(', '), { value }, { args, ...extra }),
    };
}
