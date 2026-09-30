// ast — immutable plain-object expression nodes, constructors and tree utilities.
//
// Node shapes (all frozen):
//   {type:'num', value: Q, raw?: '2,5'}      raw = the decimal exactly as typed (parser only)
//   {type:'sym', name, var?: true}           x, y, a_1, alpha; constants pi, e, i, inf are syms too;
//                                            var: true marks a constant name declared as a variable
//   {type:'add', args}  {type:'mul', args}  {type:'div', num, den}  {type:'neg', arg}
//   {type:'pow', base, exp}  {type:'fn', name, args}
//   {type:'rel', op, lhs, rhs}               op: '=', '<', '<=', '>', '>=', '!='
//   {type:'chain', items, ops}               a < x <= b
//   {type:'list', items}

import { Q, MathError } from './rational.js';

/** Names of the built-in constants (π, Euler's e, the imaginary unit, infinity). */
export const CONSTANT_NAMES = new Set(['pi', 'e', 'i', 'inf']);

/** Canonical function names → number of arguments (log is [base, x], root is [x, n]). */
export const FUNCTION_NAMES = new Map([
    ['sin', 1], ['cos', 1], ['tan', 1], ['cot', 1], ['sec', 1], ['csc', 1],
    ['asin', 1], ['acos', 1], ['atan', 1], ['acot', 1],
    ['sinh', 1], ['cosh', 1], ['tanh', 1], ['coth', 1], ['asinh', 1], ['acosh', 1], ['atanh', 1],
    ['ln', 1], ['lg', 1], ['log', 2], ['exp', 1], ['sqrt', 1], ['root', 2],
    ['abs', 1], ['sign', 1], ['floor', 1], ['ceil', 1], ['fact', 1],
]);

const REL_OPS = new Set(['=', '<', '<=', '>', '>=', '!=']);
const REL_ALIAS = { '≤': '<=', '≥': '>=', '≠': '!=', '==': '=', '=<': '<=', '=>': '>=', '<>': '!=' };

const freeze = Object.freeze;

/** Turns a number / bigint / Q / numeric string into a num node, a name string into a sym; nodes pass. */
export function toNode(x) {
    if (x && typeof x === 'object' && typeof x.type === 'string') return x;
    if (x instanceof Q || typeof x === 'number' || typeof x === 'bigint') return num(x);
    if (typeof x === 'string') return /^[+-]?[\d.,]/.test(x.trim()) ? num(x) : sym(x);
    throw new TypeError(`not a node: ${x}`);
}

const argList = (args) => (args.length === 1 && Array.isArray(args[0]) ? args[0] : args).map(toNode);

/** Number node from Q | number | bigint | string ("3/4", "2,5"). */
export function num(x, raw) {
    const value = Q.of(x);
    return raw ? freeze({ type: 'num', value, raw: String(raw) }) : freeze({ type: 'num', value });
}

/** Symbol node. isVar = true turns a constant name (e, i, pi) into an ordinary variable. */
export function sym(name, isVar = false) {
    if (typeof name !== 'string' || !name) throw new TypeError('symbol name must be a non-empty string');
    return isVar && CONSTANT_NAMES.has(name) ? freeze({ type: 'sym', name, var: true }) : freeze({ type: 'sym', name });
}

/** n-ary sum; add(a, b, c) or add([a, b, c]); one term returns it, none returns 0. */
export function add(...args) {
    const a = argList(args);
    if (a.length === 0) return num(0);
    if (a.length === 1) return a[0];
    return freeze({ type: 'add', args: freeze(a) });
}

/** n-ary product; one factor returns it, none returns 1. */
export function mul(...args) {
    const a = argList(args);
    if (a.length === 0) return num(1);
    if (a.length === 1) return a[0];
    return freeze({ type: 'mul', args: freeze(a) });
}

export function div(n, d) {
    return freeze({ type: 'div', num: toNode(n), den: toNode(d) });
}

export function neg(a) {
    return freeze({ type: 'neg', arg: toNode(a) });
}

export function pow(base, exp) {
    return freeze({ type: 'pow', base: toNode(base), exp: toNode(exp) });
}

/** Function node: fn('sin', x), fn('log', base, x), fn('root', x, n). */
export function fn(name, ...args) {
    const a = argList(args);
    const arity = FUNCTION_NAMES.get(name);
    if (arity === undefined) throw new MathError({ ru: `Неизвестная функция «${name}»`, en: `Unknown function "${name}"` }, null, null, 'unknown-fn');
    if (a.length !== arity) throw new MathError({ ru: `У функции ${name} должно быть аргументов: ${arity}`, en: `${name} takes ${arity} argument(s)` }, null, null, 'arity');
    return freeze({ type: 'fn', name, args: freeze(a) });
}

function relOp(op) {
    const o = REL_ALIAS[op] ?? op;
    if (!REL_OPS.has(o)) throw new TypeError(`unknown relation ${op}`);
    return o;
}

/** Relation lhs op rhs (op: '=', '<', '<=', '>', '>=', '!=' or ≤ ≥ ≠). */
export function rel(op, lhs, rhs) {
    return freeze({ type: 'rel', op: relOp(op), lhs: toNode(lhs), rhs: toNode(rhs) });
}

/** Chain of relations: chain([a, x, b], ['<', '<=']) for a < x ≤ b. */
export function chain(items, ops) {
    if (items.length !== ops.length + 1) throw new TypeError('chain: items.length must be ops.length + 1');
    return freeze({ type: 'chain', items: freeze(items.map(toNode)), ops: freeze(ops.map(relOp)) });
}

export function list(...args) {
    return freeze({ type: 'list', items: freeze(argList(args)) });
}

/** True for pi, e, i, inf (unless declared as a variable). */
export function isConst(node) {
    return node?.type === 'sym' && !node.var && CONSTANT_NAMES.has(node.name);
}

/** Children of a node in a fixed order. */
export function nodeChildren(node) {
    switch (node.type) {
        case 'add':
        case 'mul':
        case 'fn':
            return node.args;
        case 'div':
            return [node.num, node.den];
        case 'neg':
            return [node.arg];
        case 'pow':
            return [node.base, node.exp];
        case 'rel':
            return [node.lhs, node.rhs];
        case 'chain':
        case 'list':
            return node.items;
        default:
            return [];
    }
}

/** Same node type with new children (in nodeChildren order). */
export function withChildren(node, kids) {
    switch (node.type) {
        case 'add':
            return freeze({ type: 'add', args: freeze(kids) });
        case 'mul':
            return freeze({ type: 'mul', args: freeze(kids) });
        case 'fn':
            return freeze({ type: 'fn', name: node.name, args: freeze(kids) });
        case 'div':
            return freeze({ type: 'div', num: kids[0], den: kids[1] });
        case 'neg':
            return freeze({ type: 'neg', arg: kids[0] });
        case 'pow':
            return freeze({ type: 'pow', base: kids[0], exp: kids[1] });
        case 'rel':
            return freeze({ type: 'rel', op: node.op, lhs: kids[0], rhs: kids[1] });
        case 'chain':
            return freeze({ type: 'chain', items: freeze(kids), ops: node.ops });
        case 'list':
            return freeze({ type: 'list', items: freeze(kids) });
        default:
            return node;
    }
}

const KEYS = new WeakMap();

/**
 * Canonical string key of a node (structural; ignores `raw`). Equal keys ⇔ nodeEquals.
 * Memoised per node object.
 */
export function nodeKey(node) {
    let k = KEYS.get(node);
    if (k !== undefined) return k;
    switch (node.type) {
        case 'num':
            k = '#' + node.value.toString();
            break;
        case 'sym':
            k = node.var ? node.name + "'" : node.name;
            break;
        case 'add':
            k = '+(' + node.args.map(nodeKey).join(',') + ')';
            break;
        case 'mul':
            k = '*(' + node.args.map(nodeKey).join(',') + ')';
            break;
        case 'div':
            k = '/(' + nodeKey(node.num) + ',' + nodeKey(node.den) + ')';
            break;
        case 'neg':
            k = '-(' + nodeKey(node.arg) + ')';
            break;
        case 'pow':
            k = '^(' + nodeKey(node.base) + ',' + nodeKey(node.exp) + ')';
            break;
        case 'fn':
            k = node.name + '(' + node.args.map(nodeKey).join(',') + ')';
            break;
        case 'rel':
            k = node.op + '(' + nodeKey(node.lhs) + ',' + nodeKey(node.rhs) + ')';
            break;
        case 'chain':
            k = 'chain(' + node.items.map(nodeKey).join(',') + ';' + node.ops.join(',') + ')';
            break;
        case 'list':
            k = '[' + node.items.map(nodeKey).join(',') + ']';
            break;
        default:
            throw new TypeError(`unknown node type ${node?.type}`);
    }
    if (Object.isFrozen(node)) KEYS.set(node, k);
    return k;
}

/** Structural equality (numbers by value; `raw` is ignored). */
export function nodeEquals(a, b) {
    if (a === b) return true;
    if (!a || !b || a.type !== b.type) return false;
    return nodeKey(a) === nodeKey(b);
}

/** Sorted names of the free variables (constants excluded). */
export function freeVars(node) {
    const out = new Set();
    const walk = (n) => {
        if (n.type === 'sym') {
            if (!isConst(n)) out.add(n.name);
            return;
        }
        for (const c of nodeChildren(n)) walk(c);
    };
    walk(node);
    return [...out].sort();
}

/** Does the node mention variable `name`? */
export function containsVar(node, name) {
    if (node.type === 'sym') return node.name === name && !isConst(node);
    for (const c of nodeChildren(node)) if (containsVar(c, name)) return true;
    return false;
}

/** Is pred true for the node or any node below it? */
export function nodeSome(node, pred) {
    if (pred(node)) return true;
    for (const c of nodeChildren(node)) if (nodeSome(c, pred)) return true;
    return false;
}

/** Post-order transform: f gets each rebuilt node and returns a replacement (or undefined to keep it). */
export function mapNode(node, f) {
    const kids = nodeChildren(node);
    let next = node;
    if (kids.length) {
        let changed = false;
        const nk = kids.map((c) => {
            const m = mapNode(c, f);
            if (m !== c) changed = true;
            return m;
        });
        if (changed) next = withChildren(node, nk);
    }
    const r = f(next);
    return r === undefined ? next : r;
}

/** Replace variables: substitute(node, {x: 2, y: node}). Constants are not touched. */
export function substitute(node, map) {
    const m = new Map();
    for (const [k, v] of Object.entries(map)) m.set(k, toNode(v));
    if (!m.size) return node;
    return mapNode(node, (n) => (n.type === 'sym' && !isConst(n) && m.has(n.name) ? m.get(n.name) : undefined));
}

/** Number of nodes in the tree. */
export function nodeSize(node) {
    let s = 1;
    for (const c of nodeChildren(node)) s += nodeSize(c);
    return s;
}

/** Exact rational value of a purely numeric literal (num, neg/div/add/mul of nums, integer powers), else null. */
export function numValue(node) {
    switch (node.type) {
        case 'num':
            return node.value;
        case 'neg': {
            const v = numValue(node.arg);
            return v && v.neg();
        }
        case 'div': {
            const a = numValue(node.num);
            const b = a && numValue(node.den);
            return b && !b.isZero() ? a.div(b) : null;
        }
        case 'add':
        case 'mul': {
            let acc = node.type === 'add' ? Q.ZERO : Q.ONE;
            for (const c of node.args) {
                const v = numValue(c);
                if (!v) return null;
                acc = node.type === 'add' ? acc.add(v) : acc.mul(v);
            }
            return acc;
        }
        case 'pow': {
            const b = numValue(node.base);
            const e = b && numValue(node.exp);
            if (!e || !e.isInt() || (b.isZero() && e.isNeg()) || e.abs().gt(4096)) return null;
            try {
                return b.pow(e.n);
            } catch {
                return null;
            }
        }
        default:
            return null;
    }
}

/** True when numValue(node) is not null (a numeric literal like 3, -2, 3/4, 2,5). */
export function isNumber(node) {
    return numValue(node) !== null;
}
