// «Холст» — engine nodes → SymPy source, for the fallback when our engine refuses (the Python worker runs it).
import * as E from '../../src/index.js';

const FN = {
    sin: 'sin', cos: 'cos', tan: 'tan', cot: 'cot', sec: 'sec', csc: 'csc',
    asin: 'asin', acos: 'acos', atan: 'atan', acot: 'acot',
    sinh: 'sinh', cosh: 'cosh', tanh: 'tanh', coth: 'coth', asinh: 'asinh', acosh: 'acosh', atanh: 'atanh',
    ln: 'log', exp: 'exp', sqrt: 'sqrt', abs: 'Abs', sign: 'sign', floor: 'floor', ceil: 'ceiling', fact: 'factorial', cbrt: 'cbrt',
};

const SYM = { pi: 'pi', e: 'E', i: 'I', inf: 'oo' };

export function toSympy(node, rename = {}) {
    const p = (n) => toSympy(n, rename);
    switch (node.type) {
        case 'num': {
            const q = node.value;
            return q.d === 1n ? `Integer(${q.n})` : `Rational(${q.n}, ${q.d})`;
        }
        case 'sym': return rename[node.name] ?? SYM[node.name] ?? (node.name === 'lambda' ? 'lamda' : node.name);
        case 'add': return `(${node.args.map(p).join(' + ')})`;
        case 'mul': return `(${node.args.map(p).join('*')})`;
        case 'div': return `((${p(node.num)})/(${p(node.den)}))`;
        case 'neg': return `(-(${p(node.arg)}))`;
        case 'pow': return `((${p(node.base)})**(${p(node.exp)}))`;
        case 'fn': {
            if (node.name === 'lg') return `log(${p(node.args[0])}, 10)`;
            if (node.name === 'log') return `log(${p(node.args[1])}, ${p(node.args[0])})`;
            if (node.name === 'root') return `root(${p(node.args[0])}, ${p(node.args[1])})`;
            return `${FN[node.name] ?? node.name}(${node.args.map(p).join(', ')})`;
        }
        case 'rel': {
            const l = p(node.lhs), r = p(node.rhs);
            if (node.op === '=') return `Eq(${l}, ${r})`;
            if (node.op === '!=') return `Ne(${l}, ${r})`;
            return `(${l} ${node.op} ${r})`;
        }
        case 'chain': {
            const parts = [];
            for (let k = 0; k < node.ops.length; k++) parts.push(`(${p(node.items[k])} ${node.ops[k]} ${p(node.items[k + 1])})`);
            return `And(${parts.join(', ')})`;
        }
        case 'list': return `[${node.items.map(p).join(', ')}]`;
        default: return '0';
    }
}

// Symbols a SymPy expression needs declared (constants excluded).
export function sympySymbols(...nodes) {
    const s = new Set();
    for (const n of nodes) if (n) for (const v of E.freeVars(n)) s.add(v);
    return [...s];
}

// A fallback request for the Python worker.
export function fallback(op, sympy, symbols = [], extra = {}) {
    return { op, sympy, symbols, ...extra };
}
