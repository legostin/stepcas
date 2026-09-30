// Survey the bilingual constructs in src (for the i18n codemod).
import fs from 'node:fs';
import path from 'node:path';
import * as acorn from 'acorn';
import * as walk from 'acorn-walk';

const CYR = /[А-Яа-яЁё]/;
const files = [];
const w = (d) =>
    fs.readdirSync(d).forEach((f) => {
        const p = path.join(d, f);
        fs.statSync(p).isDirectory() ? w(p) : p.endsWith('.js') && files.push(p);
    });
w('src');
const isLit = (n) => n && ((n.type === 'Literal' && typeof n.value === 'string') || n.type === 'TemplateLiteral');
const litText = (n) => (n.type === 'Literal' ? n.value : n.quasis.map((q) => q.value.cooked).join('${}'));
const stats = { call: {}, obj: 0, cond: 0, other: 0 };
const otherByFile = {};
for (const f of files) {
    const src = fs.readFileSync(f, 'utf8');
    const ast = acorn.parse(src, { ecmaVersion: 'latest', sourceType: 'module' });
    const covered = new Set();
    const mark = (n) => walk.full(n, (x) => covered.add(x));
    walk.full(ast, (n) => {
        if (n.type === 'CallExpression' && n.arguments.length >= 2 && isLit(n.arguments[0]) && isLit(n.arguments[1]) && CYR.test(litText(n.arguments[0]))) {
            const name =
                n.callee.type === 'Identifier' ? n.callee.name : n.callee.type === 'MemberExpression' ? '.' + (n.callee.property.name ?? '?') : n.callee.type;
            stats.call[name] = (stats.call[name] ?? 0) + 1;
            mark(n.arguments[0]);
            mark(n.arguments[1]);
        } else if (n.type === 'ObjectExpression' && n.properties.some((p) => p.key?.name === 'ru') && n.properties.some((p) => p.key?.name === 'en')) {
            stats.obj++;
            n.properties.forEach((p) => mark(p.value));
        } else if (
            n.type === 'ConditionalExpression' &&
            ((isLit(n.consequent) && CYR.test(litText(n.consequent))) || (isLit(n.alternate) && CYR.test(litText(n.alternate))))
        ) {
            stats.cond++;
            mark(n.consequent);
            mark(n.alternate);
        }
    });
    walk.full(ast, (n) => {
        if (isLit(n) && CYR.test(litText(n)) && !covered.has(n)) {
            stats.other++;
            (otherByFile[f] ??= []).push(src.slice(n.start, Math.min(n.end, n.start + 70)).replace(/\n/g, ' '));
        }
    });
}
console.log(JSON.stringify(stats, null, 1));
for (const [f, xs] of Object.entries(otherByFile)) {
    console.log(`== ${f} ${xs.length}`);
    xs.slice(0, 6).forEach((x) => console.log('   ', x));
}
