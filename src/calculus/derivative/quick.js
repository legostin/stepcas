// derivative/quick — the fast canonical derivative (quickDerivative), used for checks and by other modules.

import { num, containsVar } from '../../core/ast.js';
import { Q, MathError } from '../../core/rational.js';
import { canonContext } from '../../core/simplify.js';
import { E_, HALF, N0, N1, N2, NM1, checkExpr, isZero } from '../display.js';
import { msg } from '../../i18n/index.js';
import { asNode } from '../../core/parse.js';

// ---------------------------------------------------------------- fast canonical derivative

const lnOf = (b, C) => C.fn('ln', [b]);
const MHALF = num(new Q(-1n, 2n));

function outerCanon(name, u, C) {
    const u2 = C.pow(u, N2);
    switch (name) {
        case 'sin':
            return C.fn('cos', [u]);
        case 'cos':
            return C.mul([NM1, C.fn('sin', [u])]);
        case 'tan':
            return C.pow(C.fn('cos', [u]), num(-2));
        case 'cot':
            return C.mul([NM1, C.pow(C.fn('sin', [u]), num(-2))]);
        case 'sec':
            return C.mul([C.fn('sec', [u]), C.fn('tan', [u])]);
        case 'csc':
            return C.mul([NM1, C.fn('csc', [u]), C.fn('cot', [u])]);
        case 'asin':
            return C.pow(C.add([N1, C.mul([NM1, u2])]), MHALF);
        case 'acos':
            return C.mul([NM1, C.pow(C.add([N1, C.mul([NM1, u2])]), MHALF)]);
        case 'atan':
            return C.pow(C.add([u2, N1]), NM1);
        case 'acot':
            return C.mul([NM1, C.pow(C.add([u2, N1]), NM1)]);
        case 'sinh':
            return C.fn('cosh', [u]);
        case 'cosh':
            return C.fn('sinh', [u]);
        case 'tanh':
            return C.pow(C.fn('cosh', [u]), num(-2));
        case 'coth':
            return C.mul([NM1, C.pow(C.fn('sinh', [u]), num(-2))]);
        case 'asinh':
            return C.pow(C.add([u2, N1]), MHALF);
        case 'acosh':
            return C.pow(C.add([u2, NM1]), MHALF);
        case 'atanh':
            return C.pow(C.add([N1, C.mul([NM1, u2])]), NM1);
        case 'ln':
            return C.pow(u, NM1);
        case 'lg':
            return C.pow(C.mul([u, lnOf(num(10), C)]), NM1);
        case 'exp':
            return C.pow(E_, u);
        case 'sqrt':
            return C.mul([HALF, C.pow(u, MHALF)]);
        case 'abs':
            return C.mul([u, C.pow(C.fn('abs', [u]), NM1)]);
        case 'sign':
        case 'floor':
        case 'ceil':
            return N0;
        default:
            throw new MathError(msg('calculus.derivative.quick.cannot_differentiate', { name }), null, null, 'unsupported');
    }
}

export const FACT_ERR = () => new MathError(msg('calculus.derivative.quick.factorial_is_defined_on_whole_numbers'), null, null, 'unsupported');

function dCanon(n, v, C) {
    if (!containsVar(n, v)) return N0;
    switch (n.type) {
        case 'sym':
            return N1;
        case 'add':
            return C.add(n.args.map((a) => dCanon(a, v, C)));
        case 'mul': {
            const terms = [];
            n.args.forEach((f, i) => {
                if (!containsVar(f, v)) return;
                const df = dCanon(f, v, C);
                if (isZero(df)) return;
                terms.push(C.mul([...n.args.slice(0, i), df, ...n.args.slice(i + 1)]));
            });
            return C.add(terms);
        }
        case 'pow': {
            const b = n.base;
            const e = n.exp;
            const bv = containsVar(b, v);
            const ev = containsVar(e, v);
            if (!ev) return C.mul([e, C.pow(b, C.add([e, NM1])), dCanon(b, v, C)]);
            if (!bv) return C.mul([n, lnOf(b, C), dCanon(e, v, C)]);
            return C.mul([n, dCanon(C.mul([e, lnOf(b, C)]), v, C)]);
        }
        case 'fn': {
            if (n.name === 'log') {
                const [b, x] = n.args;
                if (containsVar(b, v)) return dCanon(C.mul([lnOf(x, C), C.pow(lnOf(b, C), NM1)]), v, C);
                return C.mul([C.pow(C.mul([x, lnOf(b, C)]), NM1), dCanon(x, v, C)]);
            }
            if (n.name === 'root') {
                const r = C.fn('root', n.args);
                if (r.type === 'fn' && r.name === 'root')
                    throw new MathError(msg('calculus.derivative.quick.cannot_differentiate_this_root'), null, null, 'unsupported');
                return dCanon(r, v, C);
            }
            if (n.name === 'fact') throw FACT_ERR();
            const u = n.args[0];
            const outer = outerCanon(n.name, u, C);
            if (isZero(outer)) return N0;
            return C.mul([outer, dCanon(u, v, C)]);
        }
        default: {
            const s = C.simplify(n);
            if (s === n) throw new MathError(msg('calculus.derivative.quick.cannot_differentiate_this_expression'), null, null, 'unsupported');
            return dCanon(s, v, C);
        }
    }
}

/** Derivative in canonical form (simplify.js), fast and without steps — for checks, higher orders, L'Hôpital. */
export function quickDerivative(node, v = 'x') {
    node = asNode(node);
    checkExpr(node);
    const C = canonContext({ budget: 2000000 });
    return dCanon(C.simplify(node), v, C);
}
