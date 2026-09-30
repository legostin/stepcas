// core/safe — total versions of the engine's operations for solver code: a stranger's input never makes them throw.
import { simplify } from './simplify.js';
import { evaluate } from './evaluate.js';

/** simplify(node), or the node unchanged when it cannot be simplified. */
export function trySimplify(node) {
    try {
        return simplify(node);
    } catch {
        return node;
    }
}

/** The real value of a node (variables from env), NaN when there is none. */
export function approx(node, env = {}) {
    try {
        const x = evaluate(node, env);
        return typeof x === 'number' ? x : NaN;
    } catch {
        return NaN;
    }
}
