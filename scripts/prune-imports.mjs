// Remove imported names that ESLint reports as unused (after a refactoring moved code around), then merge the named
// imports a file takes from one module into one declaration.
//   node scripts/prune-imports.mjs [paths…]
import fs from 'node:fs';
import { execFileSync } from 'node:child_process';

const paths = process.argv.slice(2).length ? process.argv.slice(2) : ['src'];
let out;
try {
    out = execFileSync('npx', ['eslint', ...paths, '--format', 'json'], { encoding: 'utf8' });
} catch (e) {
    out = e.stdout;
}
let removed = 0;
for (const f of JSON.parse(out)) {
    const lines = fs.readFileSync(f.filePath, 'utf8').split('\n');
    let changed = false;
    for (const m of f.messages) {
        if (m.ruleId !== 'no-unused-vars') continue;
        const name = m.message.match(/'([^']+)'/)?.[1];
        const i = m.line - 1;
        const mm = lines[i]?.match(/^import \{([^}]*)\} from (.*)$/);
        if (!name || !mm) continue;
        const keep = mm[1]
            .split(',')
            .map((s) => s.trim())
            .filter((s) => s && s.split(' as ').pop().trim() !== name);
        lines[i] = keep.length ? `import { ${keep.join(', ')} } from ${mm[2]}` : null;
        changed = true;
        removed++;
    }
    if (changed) fs.writeFileSync(f.filePath, lines.filter((l) => l !== null).join('\n'));
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
