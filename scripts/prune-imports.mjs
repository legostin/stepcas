// Remove imported names that ESLint reports as unused (after a refactoring moved code around).
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
console.log(`removed ${removed} unused imports`);
