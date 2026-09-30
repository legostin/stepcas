// Move every bilingual text out of the code into the catalogs src/i18n/{ru,en}/<domain>.js.
//   node scripts/i18n-extract.mjs [--dry] [files…]
//
// Finds (ru, en) pairs — the first two arguments of a call when the first is a Russian string or template
// (L, T, T_, R, P, err, fail, …), {ru: …, en: …} object literals, and lang === 'ru' ? … : … conditionals — and
// replaces each with t('<namespace>.<slug>', {params}). Template expressions of the two languages are paired by
// unification: equal code is a plain parameter; code that differs only by language ('ru'/'en', .ru/.en, a trailing
// 'en' argument) becomes a function of the language; differing phrases inside become messages of their own. Pairs
// it cannot unify are reported and kept as (lng) => (lng === 'en' ? … : …) for a hand edit.
import fs from 'node:fs';
import path from 'node:path';
import * as acorn from 'acorn';
import * as walk from 'acorn-walk';

const root = process.cwd();
const argv = process.argv.slice(2);
const DRY = argv.includes('--dry');
const CYR = /[А-Яа-яЁё]/;
const CONSTRUCTORS = new Set(['L', 'T', 'T_', 'R', 'P']);
const LANG = 'lng';

// ---------------------------------------------------------------- catalogs (loaded, extended, written back)

const catalogs = { ru: new Map(), en: new Map() }; // key → template
async function loadCatalogs() {
    for (const lang of ['ru', 'en']) {
        const dir = path.join(root, 'src/i18n', lang);
        if (!fs.existsSync(dir)) continue;
        for (const f of fs.readdirSync(dir).filter((x) => x.endsWith('.js') && x !== 'index.js')) {
            const mod = await import(path.join(dir, f) + `?t=${Date.now()}`);
            const walkObj = (o, prefix) => {
                for (const [k, v] of Object.entries(o)) {
                    const key = `${prefix}.${k}`;
                    if (v && typeof v === 'object') walkObj(v, key);
                    else catalogs[lang].set(key, v);
                }
            };
            walkObj(mod.default, f.replace(/\.js$/, ''));
        }
    }
}

function slugOf(en) {
    const s = en.replace(/%\{\w+(\|[^}]*)?\}/g, ' ').replace(/\$[^$]*\$/g, ' ').replace(/\\[a-zA-Z]+/g, ' ');
    const words = (s.toLowerCase().match(/[a-z0-9]+/g) ?? []).filter((w) => !['the', 'a', 'an'].includes(w)).slice(0, 6);
    return words.join('_') || 'formula';
}

function addMessage(ns, ru, en) {
    const base = `${ns}.${slugOf(en)}`;
    for (let i = 1; ; i++) {
        const key = i === 1 ? base : `${base}_${i}`;
        const r = catalogs.ru.get(key);
        const e = catalogs.en.get(key);
        if (r === undefined && e === undefined) {
            catalogs.ru.set(key, ru);
            catalogs.en.set(key, en);
            return key;
        }
        if (r === ru && e === en) return key;
    }
}

// ---------------------------------------------------------------- unification of the two languages' code

const isStr = (n) => n && n.type === 'Literal' && typeof n.value === 'string';
const isText = (n) => n && (isStr(n) || n.type === 'TemplateLiteral');

function combine0(ctx, node, kids) {
    const repl = [];
    let lang = false;
    for (const [child, u] of kids) {
        if (!u) return null;
        lang ||= u.lang;
        if (u.src !== ctx.text(child)) repl.push([child, u.src]);
    }
    return { src: ctx.splice(node, repl), lang };
}

class Ctx {
    constructor(src, ns) {
        this.src = src;
        this.ns = ns;
        this.manual = [];
    }

    text(n) {
        return this.src.slice(n.start, n.end);
    }

    // splice: the ru node's text with some children replaced
    splice(node, repl) {
        let out = '';
        let at = node.start;
        for (const [child, s] of repl.sort((a, b) => a[0].start - b[0].start)) {
            out += this.src.slice(at, child.start) + s;
            at = child.end;
        }
        return out + this.src.slice(at, node.end);
    }

    unify(r, e) {
        const rs = this.text(r);
        const es = this.text(e);
        if (rs === es) return { src: rs, lang: false };
        if (isStr(r) && isStr(e) && r.value === 'ru' && e.value === 'en') return { src: LANG, lang: true };
        // two templates with the same words and TeX: only the code inside differs → one function of the language
        if (r.type === 'TemplateLiteral' && e.type === 'TemplateLiteral' && r.quasis.length === e.quasis.length && r.quasis.every((q, i) => q.value.cooked === e.quasis[i].value.cooked) && !CYR.test(r.quasis.map((q) => q.value.cooked).join(''))) {
            return combine0(this, r, r.expressions.map((x, i) => [x, this.unify(x, e.expressions[i])]));
        }
        // different phrases inside code: the phrase in the current language (a message would stringify as Russian)
        if (isText(r) && isText(e)) return { src: `${this.message(r, e)}.in(${LANG})`, lang: true };
        if (r.type !== e.type) return null;
        const pair = (a, b) => (a === null && b === null ? { src: null } : a && b ? this.unify(a, b) : null);
        const combine = (node, kids) => {
            const repl = [];
            let lang = false;
            for (const [child, u] of kids) {
                if (!u) return null;
                lang ||= u.lang;
                if (u.src !== this.text(child)) repl.push([child, u.src]);
            }
            return { src: this.splice(node, repl), lang };
        };
        switch (r.type) {
            case 'Identifier':
                return null;
            case 'CallExpression': {
                const callee = this.unify(r.callee, e.callee);
                if (!callee) return null;
                const ra = r.arguments;
                const ea = e.arguments;
                const kids = [[r.callee, callee]];
                if (ea.length === ra.length + 1 && isStr(ea[ea.length - 1]) && ea[ea.length - 1].value === 'en') {
                    for (let i = 0; i < ra.length; i++) kids.push([ra[i], this.unify(ra[i], ea[i])]);
                    const res = combine(r, kids);
                    if (!res) return null;
                    // append the language argument before the closing bracket
                    const close = res.src.lastIndexOf(')');
                    const inner = res.src.slice(0, close).trimEnd();
                    return { src: `${inner}${ra.length ? ', ' : ''}${LANG})`, lang: true };
                }
                if (ra.length !== ea.length) return null;
                for (let i = 0; i < ra.length; i++) kids.push([ra[i], this.unify(ra[i], ea[i])]);
                return combine(r, kids);
            }
            case 'MemberExpression': {
                const obj = this.unify(r.object, e.object);
                if (!obj) return null;
                if (!r.computed && !e.computed && r.property.name === 'ru' && e.property.name === 'en') return { src: `${obj.src}[${LANG}]`, lang: true };
                if (this.text(r.property) !== this.text(e.property) || r.computed !== e.computed) return null;
                return combine(r, [[r.object, obj]]);
            }
            case 'ConditionalExpression':
                return combine(r, [[r.test, this.unify(r.test, e.test)], [r.consequent, this.unify(r.consequent, e.consequent)], [r.alternate, this.unify(r.alternate, e.alternate)]]);
            case 'BinaryExpression':
            case 'LogicalExpression':
                if (r.operator !== e.operator) return null;
                return combine(r, [[r.left, this.unify(r.left, e.left)], [r.right, this.unify(r.right, e.right)]]);
            case 'UnaryExpression':
                if (r.operator !== e.operator) return null;
                return combine(r, [[r.argument, this.unify(r.argument, e.argument)]]);
            case 'ArrayExpression':
                if (r.elements.length !== e.elements.length) return null;
                return combine(r, r.elements.map((x, i) => [x, pair(x, e.elements[i])]).filter(([x]) => x));
            case 'ArrowFunctionExpression':
                if (r.params.map((x) => this.text(x)).join() !== e.params.map((x) => this.text(x)).join() || r.body.type === 'BlockStatement' || e.body.type === 'BlockStatement') return null;
                return combine(r, [[r.body, this.unify(r.body, e.body)]]);
            case 'ChainExpression':
                return combine(r, [[r.expression, this.unify(r.expression, e.expression)]]);
            default:
                return null;
        }
    }

    paramName(node, used) {
        let name = null;
        if (node.type === 'Identifier') name = node.name;
        else if (node.type === 'CallExpression' && node.arguments[0]?.type === 'Identifier') name = node.arguments[0].name;
        else if (node.type === 'MemberExpression' && !node.computed && node.property.type === 'Identifier' && !['ru', 'en'].includes(node.property.name)) name = node.property.name;
        if (!name || !/^[A-Za-z_]\w*$/.test(name) || name === LANG) name = 'p';
        let n = name;
        for (let i = 2; used.has(n); i++) n = `${name}${i}`;
        used.add(n);
        return n;
    }

    // a (ru, en) pair of strings or templates → the source of t('key', {params})
    message(r, e) {
        const parts = (n) => (n.type === 'Literal' ? { quasis: [n.value], exprs: [] } : { quasis: n.quasis.map((q) => q.value.cooked), exprs: n.expressions });
        const R = parts(r);
        const E = parts(e);
        const params = []; // {name, src}
        const used = new Set();
        const byValue = new Map();
        const param = (valueSrc, node) => {
            if (byValue.has(valueSrc)) return byValue.get(valueSrc);
            const name = this.paramName(node, used);
            params.push({ name, src: valueSrc });
            byValue.set(valueSrc, name);
            return name;
        };
        const ruNames = [];
        const enNames = new Array(E.exprs.length).fill(null);
        const takenEn = new Set();
        for (const re of R.exprs) {
            let found = null;
            for (let j = 0; j < E.exprs.length && !found; j++) {
                if (takenEn.has(j)) continue;
                const u = this.unify(re, E.exprs[j]);
                if (u) found = { j, u };
            }
            if (!found) {
                // the same code may be used twice in English: allow a match with a taken one
                for (let j = 0; j < E.exprs.length && !found; j++) {
                    const u = this.unify(re, E.exprs[j]);
                    if (u) found = { j, u };
                }
            }
            if (found) {
                const src = found.u.lang ? `(${LANG}) => ${found.u.src}` : found.u.src;
                const name = param(src, re);
                ruNames.push(name);
                if (enNames[found.j] === null) enNames[found.j] = name;
                takenEn.add(found.j);
            } else {
                const src = this.text(re);
                ruNames.push(param(src, re));
                if (CYR.test(src)) this.manual.push(src.slice(0, 80));
            }
        }
        E.exprs.forEach((ee, j) => {
            if (enNames[j] === null) enNames[j] = param(this.text(ee), ee);
        });
        const tpl = (Q, names) => Q.quasis.map((q, i) => (i < names.length ? `${q}%{${names[i]}}` : q)).join('');
        const key = addMessage(this.ns, tpl(R, ruNames), tpl(E, enNames));
        if (!params.length) return `msg('${key}')`;
        const obj = params.map((p) => (p.name === p.src ? p.name : `${p.name}: ${p.src}`)).join(', ');
        return `msg('${key}', { ${obj} })`;
    }
}

// ---------------------------------------------------------------- one pass over a file

function namespaceOf(file) {
    const rel = path.relative(path.join(root, 'src'), file).replace(/\.js$/, '').split(path.sep);
    if (rel[rel.length - 1] === 'index') rel.pop();
    return rel.join('.');
}

function langTest(test) {
    // lng === 'ru' / L === 'en' / lang !== 'ru' → {id, ruFirst}
    if (test.type !== 'BinaryExpression' || !['===', '!=='].includes(test.operator)) return null;
    const [a, b] = [test.left, test.right];
    const id = a.type === 'Identifier' ? a : b.type === 'Identifier' ? b : null;
    const lit = isStr(a) ? a : isStr(b) ? b : null;
    if (!id || !lit || !['ru', 'en'].includes(lit.value)) return null;
    const eqRu = lit.value === 'ru';
    return { id: id.name, ruFirst: test.operator === '===' ? eqRu : !eqRu };
}

function pass(file) {
    const src = fs.readFileSync(file, 'utf8');
    const ast = acorn.parse(src, { ecmaVersion: 'latest', sourceType: 'module' });
    const ctx = new Ctx(src, namespaceOf(file));
    const edits = [];
    const inside = (n) => edits.some((e) => n.start >= e.start && n.end <= e.end);
    const failed = [];
    walk.full(ast, () => {});
    // outermost first: walk in source order, skip nodes inside an edit
    const targets = [];
    walk.fullAncestor(ast, (n) => {
        if (n.type === 'CallExpression' && n.arguments.length >= 2 && isText(n.arguments[0]) && isText(n.arguments[1]) && CYR.test(ctx.text(n.arguments[0]))) targets.push({ kind: 'call', n });
        else if (n.type === 'ObjectExpression' && n.properties.length === 2 && n.properties.every((p) => p.type === 'Property' && !p.computed && isText(p.value)) && new Set(n.properties.map((p) => p.key.name ?? p.key.value)).size === 2 && n.properties.every((p) => ['ru', 'en'].includes(p.key.name ?? p.key.value))) targets.push({ kind: 'obj', n });
        else if (n.type === 'ConditionalExpression' && langTest(n.test) && isText(n.consequent) && isText(n.alternate)) targets.push({ kind: 'cond', n });
    });
    targets.sort((a, b) => a.n.start - b.n.start || b.n.end - a.n.end);
    for (const { kind, n } of targets) {
        if (inside(n)) continue;
        if (kind === 'call') {
            const [r, e] = n.arguments;
            const msg = ctx.message(r, e);
            const name = n.callee.type === 'Identifier' ? n.callee.name : null;
            if (CONSTRUCTORS.has(name) && n.arguments.length === 2) edits.push({ start: n.start, end: n.end, text: msg });
            else edits.push({ start: r.start, end: e.end, text: msg });
        } else if (kind === 'obj') {
            const get = (k) => n.properties.find((p) => (p.key.name ?? p.key.value) === k).value;
            edits.push({ start: n.start, end: n.end, text: ctx.message(get('ru'), get('en')) });
        } else {
            const lt = langTest(n.test);
            const [r, e] = lt.ruFirst ? [n.consequent, n.alternate] : [n.alternate, n.consequent];
            edits.push({ start: n.start, end: n.end, text: `${ctx.message(r, e)}.in(${lt.id})` });
        }
    }
    if (!edits.length) return { changed: false, manual: ctx.manual, failed };
    let out = src;
    for (const e of edits.sort((a, b) => b.start - a.start)) out = out.slice(0, e.start) + e.text + out.slice(e.end);
    // import t
    if (!/import \{[^}]*\bmsg\b[^}]*\} from '[^']*i18n\/index\.js'/.test(out)) {
        let rel = path.relative(path.dirname(file), path.join(root, 'src/i18n/index.js')).split(path.sep).join('/');
        if (!rel.startsWith('.')) rel = `./${rel}`;
        const lines = out.split('\n');
        const last = lines.reduce((acc, l, i) => (l.startsWith('import ') ? i : acc), -1);
        lines.splice(last + 1, 0, `import { msg } from '${rel}';`);
        out = lines.join('\n');
    }
    if (!DRY) fs.writeFileSync(file, out);
    return { changed: true, manual: ctx.manual, edits: edits.length };
}

// ---------------------------------------------------------------- catalogs out

function writeCatalogs() {
    for (const lang of ['ru', 'en']) {
        const byDomain = new Map();
        for (const [key, v] of catalogs[lang]) {
            const [domain, ...rest] = key.split('.');
            if (!byDomain.has(domain)) byDomain.set(domain, {});
            let o = byDomain.get(domain);
            for (let i = 0; i < rest.length - 1; i++) o = o[rest[i]] ??= {};
            o[rest[rest.length - 1]] = v;
        }
        const dir = path.join(root, 'src/i18n', lang);
        fs.mkdirSync(dir, { recursive: true });
        const quoteKey = (k) => (/^[A-Za-z_$][\w$]*$/.test(k) ? k : JSON.stringify(k));
        const emit = (o, ind) => {
            const pad = ' '.repeat(ind);
            return Object.entries(o)
                .map(([k, v]) => (typeof v === 'object' ? `${pad}${quoteKey(k)}: {\n${emit(v, ind + 4)}\n${pad}},` : `${pad}${quoteKey(k)}: ${JSON.stringify(v)},`))
                .join('\n');
        };
        const LANG_NAME = { ru: 'Russian', en: 'English' };
        for (const [domain, o] of byDomain) {
            if (domain === 'i18n') continue;
            fs.writeFileSync(path.join(dir, `${domain}.js`), `// ${LANG_NAME[lang]} messages of ${domain}/ (keys ${domain}.<module>.<message>).\nexport default {\n${emit(o, 4)}\n};\n`);
        }
        const domains = [...byDomain.keys()].filter((d) => d !== 'i18n').sort();
        const idx = `// ${LANG_NAME[lang]}: every message of the engine, by domain.\n${domains.map((d) => `import ${d} from './${d}.js';`).join('\n')}\n\nexport default {\n    i18n: { value: '%{value}' },\n${domains.map((d) => `    ${d},`).join('\n')}\n};\n`;
        fs.writeFileSync(path.join(dir, 'index.js'), idx);
    }
}

await loadCatalogs();
const files = [];
const w = (d) => fs.readdirSync(d).forEach((f) => {
    const p = path.join(d, f);
    if (fs.statSync(p).isDirectory()) {
        if (f !== 'i18n') w(p);
    } else if (p.endsWith('.js')) files.push(p);
});
const only = argv.filter((a) => !a.startsWith('--')).map((a) => path.resolve(root, a));
if (only.length) files.push(...only);
else w(path.join(root, 'src'));

const manual = [];
let total = 0;
for (const f of files) {
    for (let round = 0; round < 6; round++) {
        const r = pass(f);
        manual.push(...r.manual.map((m) => `${path.relative(root, f)}: ${m}`));
        if (!r.changed || DRY) break;
        total += r.edits;
    }
}
if (!DRY) writeCatalogs();
console.log(`${total} replacements; catalogs: ${catalogs.ru.size} messages`);
if (manual.length) {
    console.log(`${manual.length} Russian expressions kept as functions of the language (edit by hand):`);
    for (const m of manual) console.log('  ', m);
}
