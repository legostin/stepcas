// steps — bilingual strings and the step object that solvers return and kit/steps.js renders.
//
// Step = { title: {ru, en}, tex?: string | {ru, en}, text?: {ru, en}, rule?: string, sub?: Step[] }

import { toTex } from './print.js';
import { msg } from '../i18n/index.js';

/** Bilingual string; en defaults to ru (for formulas and names that do not change). */
export function L(ru, en = ru) {
    return { ru, en };
}

function bi(x) {
    if (x === null || x === undefined) return undefined;
    if (typeof x === 'string') return { ru: x, en: x };
    if (typeof x === 'object' && ('ru' in x || 'en' in x)) return { ru: x.ru ?? x.en ?? '', en: x.en ?? x.ru ?? '' };
    return { ru: String(x), en: String(x) };
}

const isNode = (x) => x && typeof x === 'object' && typeof x.type === 'string';

/** TeX of a node in both languages: a plain string when they agree, else {ru, en}. */
export function texBoth(node, opts = {}) {
    const ru = toTex(node, { ...opts, lang: 'ru' });
    const en = toTex(node, { ...opts, lang: 'en' });
    return ru === en ? ru : { ru, en };
}

/**
 * Normalised step. `tex` may be a TeX string, {ru, en}, or an AST node (printed for both languages);
 * `title`/`text` may be strings or {ru, en}; `sub` holds nested steps (plain objects are normalised too).
 */
export function step({ title, tex, text, rule, sub } = {}) {
    const s = { title: bi(title) ?? '' };
    if (tex !== undefined && tex !== null) {
        if (typeof tex === 'string') s.tex = tex;
        else if (isNode(tex)) s.tex = texBoth(tex);
        else {
            const t = bi(tex);
            s.tex = t.ru === t.en ? t.ru : t;
        }
    }
    const tx = bi(text);
    if (tx) s.text = tx;
    if (rule) s.rule = String(rule);
    if (Array.isArray(sub) && sub.length) s.sub = sub.map((x) => step(x));
    return s;
}

/** Pick one language from a string or {ru, en}. */
export function pickLang(value, lang = 'ru') {
    if (value === null || value === undefined) return '';
    if (typeof value === 'string') return value;
    return value[lang] ?? value.en ?? value.ru ?? '';
}
