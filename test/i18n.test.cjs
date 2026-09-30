// i18n: complete catalogs, keys that exist, messages that are used, and a third language without code changes.
const { test, before } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

let E;
let RU;
let EN;
before(async () => {
    E = await import('../src/index.js');
    RU = (await import('../src/i18n/ru/index.js')).default;
    EN = (await import('../src/i18n/en/index.js')).default;
});

const flatten = (o, prefix = '', out = new Map()) => {
    for (const [k, v] of Object.entries(o)) {
        const key = prefix ? `${prefix}.${k}` : k;
        if (v && typeof v === 'object' && !Array.isArray(v)) flatten(v, key, out);
        else out.set(key, v);
    }
    return out;
};
const slots = (tpl) => new Set([...String(tpl).matchAll(/%\{(\w+)(?:\|[^}]*)?\}/g)].map((m) => m[1]));
const SRC = path.join(__dirname, '../src');
const sources = () => {
    const out = [];
    const walk = (d) => fs.readdirSync(d).forEach((f) => {
        const p = path.join(d, f);
        if (fs.statSync(p).isDirectory()) {
            if (f !== 'i18n') walk(p);
        } else if (p.endsWith('.js')) out.push(fs.readFileSync(p, 'utf8'));
    });
    walk(SRC);
    return out.join('\n');
};

test('every message exists in every built-in language, with the same slots', () => {
    const ru = flatten(RU);
    const en = flatten(EN);
    // notation fields may differ between languages (a missing one falls back to the base language or the default)
    const onlyRu = [...ru.keys()].filter((k) => !en.has(k) && !k.startsWith('notation.'));
    const onlyEn = [...en.keys()].filter((k) => !ru.has(k) && !k.startsWith('notation.'));
    assert.deepEqual(onlyRu, [], 'keys missing in English');
    assert.deepEqual(onlyEn, [], 'keys missing in Russian');
    for (const [k, r] of ru) {
        const e = en.get(k);
        if (typeof r !== 'string' || typeof e !== 'string' || k.startsWith('notation.')) continue;
        // a language may leave a parameter out (or add a plural slot), but two languages must not each use a
        // parameter the other lacks: that means the code passes language-specific values instead of neutral ones
        const [a, b] = [slots(r), slots(e)];
        const onlyA = [...a].filter((x) => !b.has(x));
        const onlyB = [...b].filter((x) => !a.has(x));
        assert.ok(!(onlyA.length && onlyB.length), `slots of ${k}: ${onlyA} vs ${onlyB}`);
    }
});

test('every key the code names exists, and every message is used', () => {
    const code = sources();
    const ru = flatten(RU);
    // a key is used when the code names it: msg('key', …) or a key chosen by a condition, msg(c ? 'a' : 'b')
    const used = new Set([...code.matchAll(/'((?:core|algebra|solve|calculus|linalg|numbers|generate)\.[\w.]+)'/g)].map((m) => m[1]));
    const prefixes = [...code.matchAll(/msg\(`([\w.]+)\.\$\{/g)].map((m) => `${m[1]}.`);
    const missing = [...used].filter((k) => !ru.has(k));
    assert.deepEqual(missing, [], 'keys used in the code but absent from the catalogs');
    const unused = [...ru.keys()].filter((k) => !k.startsWith('notation.') && !k.startsWith('i18n.') && !used.has(k) && !prefixes.some((p) => k.startsWith(p)));
    assert.deepEqual(unused, [], 'messages nobody uses');
});

test('no language is written into the code', () => {
    const code = sources().replace(/\/\/.*$/gm, '').replace(/\/\*[\s\S]*?\*\//g, '');
    const russianText = code.match(/['"`][^'"`\n]*[А-Яа-яЁё][^'"`\n]*['"`]/g) ?? [];
    assert.deepEqual(russianText, [], 'Russian text outside the catalogs');
    assert.ok(!/===\s*'ru'|'ru'\s*===|===\s*'en'|'en'\s*===/.test(code), 'a comparison with a language code');
});

test('plural slots follow the rules of each language', () => {
    const n = (k) => E.msg('numbers.theory.modular.solutions_modulo', { d: k, n: k, M: 7 });
    assert.deepEqual([1, 2, 5, 11, 21, 22].map((k) => n(k).ru.split(' ')[1]), ['решение', 'решения', 'решений', 'решений', 'решение', 'решения']);
    assert.deepEqual([1, 2, 21].map((k) => n(k).en.split(' ')[1]), ['solution', 'solutions', 'solutions']);
});

test('messages render lazily, stringify in the default language and serialise in every language', () => {
    const m = E.msg('solve.parameter.express_parameter');
    assert.equal(m.ru, 'Выражаем параметр');
    assert.equal(m.en, 'Express the parameter');
    assert.equal(`${m}`, 'Выражаем параметр');
    assert.deepEqual(JSON.parse(JSON.stringify(m)), { ru: 'Выражаем параметр', en: 'Express the parameter' });
    const r = E.solveEquation('x^2 = 4', 'x');
    const en = E.localize(r, 'en');
    assert.equal(typeof en.steps[0].title, 'string');
    assert.equal(en.answer.text, '-2, 2');
    assert.equal(E.localize(r, 'ru').answer.text, '-2; 2');
});

test('a third language joins with one call: its own words, the rest from its base', () => {
    E.registerLanguage('xx', {
        notation: { decimalTex: '{\\cdot}', listTex: ' \\mid ' },
        solve: { parameter: { express_parameter: 'XX: express %{a}' } },
        algebra: { values: { answer: 'XX answer' } },
    }, { base: 'ru' });
    assert.ok(E.LANGUAGES.includes('xx'));
    const m = E.msg('solve.parameter.express_parameter');
    assert.equal(m.xx, 'XX: express %{a}'.replace('%{a}', ''));
    assert.equal(E.msg('solve.parameter.problem').in('xx'), 'Задача', 'a missing message comes from the base language');
    assert.equal(E.toTex(E.parse('2,5'), { lang: 'xx' }), '2{\\cdot}5', 'its own notation');
    assert.equal(E.toTex(E.parse('tan(x)'), { lang: 'xx' }), '\\operatorname{tg} x', 'notation it does not define comes from the base');
    assert.deepEqual(E.eachLanguage((l) => l, { compact: false }), { ru: 'ru', en: 'en', xx: 'xx' });
    const r = E.evaluateSteps('2 + 3');
    assert.equal(E.localize(r, 'xx').steps.at(-1).title, 'XX answer');
    assert.equal(E.parseIntervalSet('(1; 2)', 'xx').toText('en'), '(1, 2)');
});
