// i18n — every word the engine says, in any number of languages.
//
// Code holds no text. It names a message by key and passes parameters:
//
//   msg('solve.quadratic.two_roots')
//   msg('solve.roots.count', { n: 3 })                       'Корней: %{n}' / '%{n} %{n|root|roots}'
//   msg('calculus.ode.mu', { mu: (lng) => tex(mu, lng) })     a parameter that depends on the language
//
// A message renders in a language on demand — msg.ru, msg.en, msg.in('kk'), `${msg}` (the default language) — so a
// result stays language-neutral until someone reads it. Templates live in i18n/<lang>/<domain>.js; each is a string
// with slots %{name}, plural slots %{name|one|few|many} (forms in the order of Intl.PluralRules categories of the
// language: ru one|few|many, en one|other), or a function (params, lang) => string for grammar a slot cannot express.
// Parameters: strings, numbers, bigints, messages, {ru, en, …} objects, arrays (joined with ', '), or functions of
// the language returning any of these.
//
// A language is registered with its catalog and, optionally, a base language whose templates fill its gaps:
//   registerLanguage('kk', kkCatalog, { base: 'ru' })
// Every message then gains a .kk getter, and everything that renders per language renders in kk too.

import ruCatalog from './ru/index.js';
import enCatalog from './en/index.js';

const catalogs = new Map(); // lang → flat Map(key → template)
const bases = new Map(); // lang → base lang
export const LANGUAGES = [];
export const DEFAULT_LANGUAGE = 'ru';
/** The notation of machine-readable plain text: ASCII names, a decimal point, ', ' between items. */
export const MACHINE = 'en';

/** Flatten nested catalog objects into dotted keys: {solve: {trig: {x: '…'}}} → 'solve.trig.x'. */
function flatten(obj, prefix = '', out = new Map()) {
    for (const [k, v] of Object.entries(obj)) {
        const key = prefix ? `${prefix}.${k}` : k;
        if (v && typeof v === 'object' && !Array.isArray(v)) flatten(v, key, out);
        else out.set(key, v);
    }
    return out;
}

/** Register (or extend) a language: its catalog of templates and the base language that fills its gaps. */
export function registerLanguage(lang, catalog, opts = {}) {
    const flat = catalogs.get(lang) ?? new Map();
    for (const [k, v] of flatten(catalog)) flat.set(k, v);
    catalogs.set(lang, flat);
    if (opts.base) bases.set(lang, opts.base);
    notations.clear();
    lookalikeCache = null;
    if (!LANGUAGES.includes(lang)) {
        LANGUAGES.push(lang);
        Object.defineProperty(Msg.prototype, lang, {
            get() {
                return this.in(lang);
            },
            configurable: true,
        });
    }
}

// the template for a key: the language, its base languages, then English, then Russian
function lookup(key, lang) {
    const seen = new Set();
    for (let l = lang; l && !seen.has(l); l = bases.get(l)) {
        seen.add(l);
        const tpl = catalogs.get(l)?.get(key);
        if (tpl !== undefined) return tpl;
    }
    for (const l of ['en', DEFAULT_LANGUAGE]) {
        const tpl = catalogs.get(l)?.get(key);
        if (tpl !== undefined) return tpl;
    }
    return undefined;
}

const notations = new Map(); // lang → merged notation record

/**
 * How a language writes mathematics: decimal and list separators, interval brackets, function names (tg or tan),
 * the identity matrix (E or I). Missing fields come from the base language, then from English.
 */
export function notation(lang = DEFAULT_LANGUAGE) {
    let n = notations.get(lang);
    if (n) return n;
    const chain = [];
    const seen = new Set();
    for (let l = lang; l && !seen.has(l); l = bases.get(l)) {
        seen.add(l);
        chain.push(l);
    }
    if (!seen.has('en')) chain.push('en');
    const read = (l) => {
        const out = {};
        for (const [k, v] of catalogs.get(l) ?? []) {
            if (!k.startsWith('notation.')) continue;
            const path = k.split('.').slice(1);
            let o = out;
            for (let i = 0; i < path.length - 1; i++) o = o[path[i]] ??= {};
            o[path[path.length - 1]] = v;
        }
        return out;
    };
    n = {};
    for (const l of chain.reverse()) {
        const r = read(l);
        for (const [k, v] of Object.entries(r)) n[k] = v && typeof v === 'object' ? { ...(n[k] ?? {}), ...v } : v;
    }
    notations.set(lang, Object.freeze(n));
    return n;
}

/** A decimal written with a point ("2.5") in a language's notation: 2{,}5 in Russian TeX, "2,5" in its plain text. */
export function decimalIn(s, lang = DEFAULT_LANGUAGE, { tex = true } = {}) {
    const n = notation(lang);
    return String(s).replace('.', tex ? n.decimalTex : n.decimalText);
}

/**
 * Words people type in answers for a notion ('none', 'all', 'or', 'infinity', 'sum'), in every registered language,
 * as a regular-expression alternation (longest first, spaces flexible).
 */
export function wordsPattern(notion) {
    const all = new Set();
    for (const l of LANGUAGES) for (const w of notation(l).words?.[notion] ?? []) all.add(w);
    return [...all]
        .sort((a, b) => b.length - a.length)
        .map((w) => w.replace(/[.*+?^${}()|[\]\\]/g, '\\$&').replace(/\s+/g, '\\s+'))
        .join('|');
}

let lookalikeCache = null;
/** Letters of other keyboard layouts that look like Latin ones ({а: 'a', …}), from every registered language. */
export function lookalikes() {
    if (lookalikeCache) return lookalikeCache;
    lookalikeCache = {};
    for (const l of LANGUAGES) Object.assign(lookalikeCache, notation(l).lookalikes ?? {});
    return lookalikeCache;
}

/** The language if it is registered, else the default one. */
export function resolveLanguage(lang) {
    return LANGUAGES.includes(lang) ? lang : DEFAULT_LANGUAGE;
}

/** A value in a language: messages render, functions of the language are called, arrays are joined. */
export function inLanguage(value, lang) {
    if (value == null) return '';
    if (value instanceof Msg) return value.in(lang);
    if (value instanceof PerLang) return inLanguage(raw(value, lang), lang);
    if (typeof value === 'function') return inLanguage(value(lang), lang);
    if (Array.isArray(value)) return value.map((v) => inLanguage(v, lang)).join(', ');
    if (typeof value === 'object') {
        if (lang in value) return inLanguage(value[lang], lang);
        const b = bases.get(lang);
        if (b && b in value) return inLanguage(value[b], lang);
        if ('en' in value) return inLanguage(value.en, lang);
        if (DEFAULT_LANGUAGE in value) return inLanguage(value[DEFAULT_LANGUAGE], lang);
    }
    return String(value);
}

const pluralRules = new Map();
function pluralForm(lang, n, forms) {
    let rules = pluralRules.get(lang);
    if (!rules) {
        try {
            rules = new Intl.PluralRules(lang);
        } catch {
            rules = new Intl.PluralRules('en');
        }
        pluralRules.set(lang, rules);
    }
    const order = rules.resolvedOptions().pluralCategories.filter((c) => ['one', 'two', 'few', 'many', 'other'].includes(c));
    const sorted = ['one', 'two', 'few', 'many', 'other'].filter((c) => order.includes(c));
    const cat = rules.select(Number(n));
    const i = sorted.indexOf(cat);
    return forms[Math.min(i < 0 ? forms.length - 1 : i, forms.length - 1)];
}

const SLOT = /%\{(\w+)(?:\|([^}]*))?\}/g;

// a parameter that depends on the language, computed for every registered language when the message is made
// (so that it sees the variables as they are now, not as they will be when someone reads the text)
class PerLang {
    constructor(fn) {
        for (const l of LANGUAGES) this[l] = fn(l);
        Object.freeze(this);
    }
}
const raw = (v, lang) => (v instanceof PerLang ? (lang in v ? v[lang] : v[bases.get(lang)] ?? v.en ?? v[DEFAULT_LANGUAGE]) : v);

/** A message: a key and its parameters, rendered per language on demand. */
export class Msg {
    constructor(key, params = null) {
        this.key = key;
        if (params) {
            const p = {};
            for (const [k, v] of Object.entries(params)) p[k] = typeof v === 'function' ? new PerLang(v) : v;
            this.params = Object.freeze(p);
        } else this.params = null;
        Object.freeze(this);
    }

    /** The text in a language. */
    in(lang = DEFAULT_LANGUAGE) {
        const tpl = lookup(this.key, lang);
        if (tpl === undefined) return this.key;
        const p = this.params ?? {};
        if (typeof tpl === 'function') {
            const resolved = {};
            for (const [k, v] of Object.entries(p)) resolved[k] = raw(v, lang);
            return tpl(resolved, lang, (v) => inLanguage(v, lang));
        }
        return tpl.replace(SLOT, (m, name, forms) => {
            const v = raw(p[name], lang);
            return forms !== undefined ? pluralForm(lang, v, forms.split('|')) : inLanguage(v, lang);
        });
    }

    toString() {
        return this.in(DEFAULT_LANGUAGE);
    }

    /** JSON: the text in every registered language. */
    toJSON() {
        return Object.fromEntries(LANGUAGES.map((l) => [l, this.in(l)]));
    }
}

/** A message by key with its parameters. */
export function msg(key, params) {
    return new Msg(key, params ?? null);
}

/** A value computed per language (TeX that differs between languages, joined messages, …) as a message. */
export function perLanguage(fn) {
    return msg('i18n.value', { value: fn });
}

/**
 * fn(lang) for every registered language: {ru: …, en: …, …}; with compact (the default) a plain value when every
 * language gives the same one. Values are computed now — for TeX that differs between languages and the like.
 */
export function eachLanguage(fn, { compact = true } = {}) {
    const values = LANGUAGES.map((l) => fn(l));
    if (compact && values.every((v) => v === values[0])) return values[0];
    return Object.fromEntries(LANGUAGES.map((l, i) => [l, values[i]]));
}

/** Messages (or strings, {lang: …} objects) joined with a separator, as one message in every language. */
export function joined(list, sep = ' ') {
    return perLanguage((lang) => list.map((x) => inLanguage(x, lang)).join(sep));
}

/** Do two texts read the same in every registered language? */
export function sameText(a, b) {
    return LANGUAGES.every((l) => inLanguage(a, l) === inLanguage(b, l));
}

/** Any bilingual value → a plain {lang: text} object for every registered language. */
export function allLanguages(value) {
    return Object.fromEntries(LANGUAGES.map((l) => [l, inLanguage(value, l)]));
}

/** Replace every message (and {ru, en, …} value) in a result tree with its text in one language. */
export function localize(value, lang = DEFAULT_LANGUAGE, seen = new WeakSet()) {
    if (value == null || typeof value !== 'object') return value;
    if (value instanceof Msg) return value.in(lang);
    if (seen.has(value)) return value;
    seen.add(value);
    if (Array.isArray(value)) return value.map((v) => localize(v, lang, seen));
    if (Object.getPrototypeOf(value) !== Object.prototype) return value; // nodes, Q, sets keep their own form
    const keys = Object.keys(value);
    if (keys.length && keys.every((k) => LANGUAGES.includes(k))) return inLanguage(value, lang);
    const out = {};
    for (const k of keys) out[k] = localize(value[k], lang, seen);
    return out;
}

registerLanguage('ru', ruCatalog);
registerLanguage('en', enCatalog);
