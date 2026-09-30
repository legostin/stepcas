// steps — the step object that solvers return and a page renders.
//
// Step = { title, tex?, text?, rule?, data?, sub?: Step[], final? } where title and text are messages (i18n), tex is a
// TeX string or a {lang: string} object, rule a stable code of what the step does, and data the step's facts for a
// program (a row operation {op, i, j, k}, a table of rows, …). step() makes messages of plain strings (the same in
// every language) and {lang: string} objects given as title or text, and renders an AST node or a message given as
// tex per language. Nothing else is rendered here: a step stays language-neutral until someone reads it —
// step.title.ru, step.title.in('kk'), or localize(result, lang) for the whole tree. test/contract.test.cjs checks
// every step of the benchmark corpus against this shape.

import { toTex } from './print.js';
import { eachLanguage, inLanguage, perLanguage, verbatim, Msg, DEFAULT_LANGUAGE } from '../i18n/index.js';

/**
 * @typedef {object} Step
 * @property {Msg} title
 * @property {string | Record<string, string>} [tex]
 * @property {Msg} [text]
 * @property {string} [rule]  a stable code of what the step does
 * @property {Record<string, unknown>} [data]  the step's facts for a program
 * @property {Step[]} [sub]
 * @property {true} [final]
 */
/**
 * @import { Text } from '../i18n/index.js'
 * @import { Node } from './ast.js'
 */
/**
 * @typedef {object} StepInput
 * @property {Text} [title]
 * @property {Text | Node} [tex]
 * @property {Text} [text]
 * @property {string} [rule]
 * @property {Record<string, unknown>} [data]
 * @property {StepInput[]} [sub]
 * @property {boolean} [final]
 */

const isNode = (x) => x && typeof x === 'object' && typeof x.type === 'string';
const asMessage = (x) => (x instanceof Msg ? x : typeof x === 'string' ? verbatim(x) : perLanguage((lang) => inLanguage(x, lang)));

/** TeX of a node in every language: a plain string when they agree, else {lang: tex}. */
export function texBoth(node, opts = {}) {
    return eachLanguage((lang) => toTex(node, { ...opts, lang }));
}

/**
 * A step; `sub` holds nested steps (plain objects are made steps too).
 * @param {StepInput} [input]
 * @returns {Step}
 */
export function step({ title, tex, text, rule, data, sub, final } = {}) {
    const s = { title: asMessage(title ?? '') };
    if (tex !== undefined && tex !== null) s.tex = isNode(tex) ? texBoth(tex) : tex instanceof Msg ? eachLanguage((lang) => tex.in(lang)) : tex;
    if (text !== undefined && text !== null) s.text = asMessage(text);
    if (rule) s.rule = String(rule);
    if (data && Object.keys(data).length) s.data = data;
    if (Array.isArray(sub) && sub.length) s.sub = sub.map((x) => step(x));
    if (final) s.final = true;
    return s;
}

/** The text of a message, a string or a {lang: …} object in one language. */
export function pickLang(value, lang = DEFAULT_LANGUAGE) {
    return inLanguage(value, lang);
}
