// steps — the step object that solvers return and a page renders.
//
// Step = { title, tex?, text?, rule?, sub?: Step[], final? } where title and text are messages (i18n), plain strings
// (the same in every language) or {lang: string} objects, and tex is a TeX string, a {lang: string} object or an AST
// node (printed per language). Nothing is rendered here: a step stays language-neutral until someone reads it —
// step.title.ru, step.title.in('kk'), or localize(result, lang) for the whole tree.

import { toTex } from './print.js';
import { eachLanguage, inLanguage, DEFAULT_LANGUAGE } from '../i18n/index.js';

const isNode = (x) => x && typeof x === 'object' && typeof x.type === 'string';

/** TeX of a node in every language: a plain string when they agree, else {lang: tex}. */
export function texBoth(node, opts = {}) {
    return eachLanguage((lang) => toTex(node, { ...opts, lang }));
}

/** A step; `sub` holds nested steps (plain objects are made steps too). */
export function step({ title, tex, text, rule, sub, final } = {}) {
    const s = { title: title ?? '' };
    if (tex !== undefined && tex !== null) s.tex = isNode(tex) ? texBoth(tex) : tex;
    if (text !== undefined && text !== null) s.text = text;
    if (rule) s.rule = String(rule);
    if (Array.isArray(sub) && sub.length) s.sub = sub.map((x) => step(x));
    if (final) s.final = true;
    return s;
}

/** The text of a message, a string or a {lang: …} object in one language. */
export function pickLang(value, lang = DEFAULT_LANGUAGE) {
    return inLanguage(value, lang);
}
