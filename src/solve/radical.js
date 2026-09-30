// solve/radical — irrational equations (roots of the unknown).

import { containsVar, numValue, nodeSome, mul, nodeKey, div, neg, pow, num, substitute } from '../core/ast.js';
import { N0, N1, S, T, approxOf, byLang, exactZero, expd, isolated, simpOr, tex } from './common.js';
import { reject, subSolve } from './equation.js';
import { pushPart, sumNode } from './polynomial.js';
import { termsOfSum } from './rational.js';

// ---------------------------------------------------------------- radicals (irrational equations)

const isRadical = (n, v) => n.type === 'pow' && containsVar(n.base, v) && (() => {
    const e = numValue(n.exp);
    return !!e && !e.isInt();
})();

export const hasRadical = (node, v) => nodeSome(node, (n) => isRadical(n, v));

/** A term c·R with a constant c and a single radical factor R → {coef, R}. */
export function splitRadicalTerm(t, v) {
    if (isRadical(t, v)) return { coef: N1, R: t };
    if (t.type !== 'mul') return null;
    const withV = t.args.filter((a) => containsVar(a, v));
    if (withV.length !== 1 || !isRadical(withV[0], v)) return null;
    const rest = t.args.filter((a) => !containsVar(a, v));
    return { coef: rest.length === 1 ? rest[0] : mul(rest), R: withV[0] };
}

export function solveRadical(lhs, rhs, E, ctx) {
    const v = ctx.v;
    if (ctx.depth > 6) return null;
    const terms = termsOfSum(E);
    const rads = terms.filter((t) => hasRadical(t, v));
    if (!rads.length) return null;
    // prefer the radical that stands alone on a side of the original equation
    const alone = [lhs, rhs].map((s) => simpOr(s)).find((s) => isRadical(s, v));
    let pickT = alone && rads.find((t) => nodeKey(splitRadicalTerm(t, v)?.R ?? N0) === nodeKey(alone));
    pickT = pickT ?? rads.find((t) => splitRadicalTerm(t, v));
    if (!pickT) return null;
    const { coef, R } = splitRadicalTerm(pickT, v);
    const others = terms.filter((t) => t !== pickT);
    const g = simpOr(div(neg(sumNode(others)), coef));
    const e = numValue(R.exp);
    const p = e.n;
    const q = e.d;
    if (p < 0n || q > 6n || p > 6n) return null;
    const f = R.base;
    const steps = [];
    const eqRT = byLang((l) => `${tex(R, l)} = ${tex(g, l)}`);
    if (!isolated(lhs, rhs, R, g)) steps.push(S(T('Уединяем корень', 'Isolate the root'), { tex: eqRT }));
    const even = q % 2n === 0n;
    const gConst = !containsVar(g, v);
    if (even && gConst && approxOf(g) < 0 && exactZero(g) !== true) {
        steps.push(S(T('Корень чётной степени не бывает отрицательным — корней нет', 'An even root is never negative: no roots')));
        return { kind: 'none', roots: [], steps, type: 'radical' };
    }
    const qn2 = Number(q);
    const lhs2 = expd(p === 1n ? f : pow(f, num(p))) ?? f;
    const rhs2 = expd(pow(g, num(q))) ?? pow(g, num(q));
    const gNonNeg = !gConst && hasRadical(g, v) && termsOfSum(simpOr(g)).every((t) => isRadical(t, v) && numValue(t.exp).d % 2n === 0n);
    const powWord = qn2 === 2 ? T('в квадрат', 'squared') : qn2 === 3 ? T('в куб', 'cubed') : T(`в степень ${qn2}`, `to the power ${qn2}`);
    steps.push(S(T(`Возводим обе части ${powWord.ru}`, `Raise both sides: ${powWord.en}`), {
        tex: byLang((l) => `${tex(lhs2, l)} = ${tex(rhs2, l)}`),
        text: even
            ? (gConst || gNonNeg
                ? T('При возведении в чётную степень могут появиться посторонние корни — все найденные корни проверим подстановкой.', 'Raising to an even power may add extraneous roots, so we will check every root by substitution.')
                : T(`Корень чётной степени неотрицателен, поэтому нужно $${tex(g)} \\ge 0$. Возведение в квадрат может добавить посторонние корни (оно решает сразу и $${tex(R)} = ${tex(g)}$, и $${tex(R)} = -(${tex(g)})$) — их отсеем.`,
                    `An even root is non-negative, so we need $${tex(g, 'en')} \\ge 0$. Squaring may add extraneous roots (it solves both $${tex(R, 'en')} = ${tex(g, 'en')}$ and $${tex(R, 'en')} = -(${tex(g, 'en')})$), and we will weed them out.`))
            : T('Нечётная степень — преобразование равносильное, посторонних корней не появится.', 'An odd power is an equivalent transformation: no extraneous roots appear.'),
    }));
    const sub = subSolve(lhs2, rhs2, ctx);
    if (sub.kind === 'unsupported' || sub.periodic) return null;
    pushPart(steps, lhs2, rhs2, sub, v);
    if (sub.kind === 'all' || sub.kind === 'set') return null;
    let roots = sub.roots;
    if (even && !gConst) {
        const bad = [];
        const good = [];
        for (const r of roots) {
            const gv = approxOf(g, { [v]: r.approx });
            if (Number.isFinite(gv) && gv < -1e-9 && (r.approxOnly || exactZero(substitute(g, { [v]: r.node })) !== true)) bad.push(r);
            else good.push(r);
        }
        if (bad.length) {
            reject(ctx, bad, 'sign');
            steps.push(S(T(`Отбрасываем корни, при которых $${tex(g)} < 0$`, `Drop the roots where $${tex(g, 'en')} < 0$`), {
                tex: byLang((l) => bad.map((r) => `${v} = ${tex(r.node, l)}:\\ ${tex(substitute(g, { [v]: r.node }), l)} = ${tex(simpOr(substitute(g, { [v]: r.node })), l)} < 0`).join(';\\ ')),
                text: T('Это посторонние корни: корень чётной степени не может равняться отрицательному числу.', 'These are extraneous: an even root cannot equal a negative number.'),
            }));
        }
        roots = good;
    }
    return { kind: roots.length ? 'roots' : 'none', roots, steps, type: 'radical', numeric: sub.numeric };
}
