// Remove imported names that ESLint reports as unused (after a refactoring moved code around), then merge the named
// imports a file takes from one module into one declaration.
//   node scripts/prune-imports.mjs [paths…]
import fs from 'node:fs';
import { execFileSync } from 'node:child_process';
import * as acorn from 'acorn';

const paths = process.argv.slice(2).length ? process.argv.slice(2) : ['src'];
let out;
try {
    out = execFileSync('npx', ['eslint', ...paths, '--format', 'json'], { encoding: 'utf8' });
} catch (e) {
    out = e.stdout;
}
let removed = 0;
for (const f of JSON.parse(out)) {
    const unused = new Set(f.messages.filter((m) => m.ruleId === 'no-unused-vars').map((m) => m.message.match(/'([^']+)'/)?.[1]));
    if (!unused.size) continue;
    let text = fs.readFileSync(f.filePath, 'utf8');
    const ast = acorn.parse(text, { ecmaVersion: 'latest', sourceType: 'module' });
    const edits = [];
    for (const st of ast.body) {
        if (st.type !== 'ImportDeclaration' || st.specifiers.some((sp) => sp.type !== 'ImportSpecifier')) continue;
        const keep = st.specifiers.filter((sp) => !unused.has(sp.local.name));
        if (keep.length === st.specifiers.length) continue;
        removed += st.specifiers.length - keep.length;
        const names = keep.map((sp) => (sp.imported.name === sp.local.name ? sp.local.name : `${sp.imported.name} as ${sp.local.name}`));
        edits.push([st.start, st.end + (keep.length ? 0 : 1), keep.length ? `import { ${names.join(', ')} } from '${st.source.value}';` : '']);
    }
    for (const [a, b, t] of edits.reverse()) text = text.slice(0, a) + t + text.slice(b);
    fs.writeFileSync(f.filePath, text);
}

// one declaration per module: import { a } from './x.js'; import { b } from './x.js' → import { a, b } from './x.js'
let merged = 0;
const files = [];
const walk = (p) => (fs.statSync(p).isDirectory() ? fs.readdirSync(p).forEach((f) => walk(`${p}/${f}`)) : p.endsWith('.js') && files.push(p));
paths.forEach(walk);
for (const f of files) {
    const lines = fs.readFileSync(f, 'utf8').split('\n');
    const first = new Map();
    let changed = false;
    lines.forEach((ln, i) => {
        const m = ln.match(/^import \{([^}]*)\} from '([^']+)';$/);
        if (!m) return;
        if (!first.has(m[2])) return first.set(m[2], i);
        const j = first.get(m[2]);
        const a = lines[j].match(/^import \{([^}]*)\} from/)[1];
        const names = [...new Set([...a.split(','), ...m[1].split(',')].map((s) => s.trim()).filter(Boolean))];
        lines[j] = `import { ${names.join(', ')} } from '${m[2]}';`;
        lines[i] = null;
        changed = true;
        merged++;
    });
    if (changed) fs.writeFileSync(f, lines.filter((l) => l !== null).join('\n'));
}
console.log(`removed ${removed} unused imports, merged ${merged} declarations`);
