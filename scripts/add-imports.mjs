// Import the names ESLint reports as undefined from the modules that own them (after a refactoring moved code around).
//   node scripts/add-imports.mjs '{"isZero": "src/calculus/display.js", "num": "src/core/ast.js"}' [paths…]
// Names missing from the map are listed and left alone; run prune-imports (which merges declarations) and prettier
// after.
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';

const homes = JSON.parse(process.argv[2]);
const paths = process.argv.slice(3).length ? process.argv.slice(3) : ['src'];
let out;
try {
    out = execFileSync('npx', ['eslint', ...paths, '--format', 'json'], { encoding: 'utf8' });
} catch (e) {
    out = e.stdout;
}
let added = 0;
const unknown = new Set();
for (const f of JSON.parse(out)) {
    const names = new Set(f.messages.filter((m) => m.ruleId === 'no-undef').map((m) => m.message.match(/'([^']+)'/)?.[1]));
    if (!names.size) continue;
    const bySource = new Map();
    for (const n of names) {
        if (!homes[n]) {
            unknown.add(n);
            continue;
        }
        let r = path.relative(path.dirname(f.filePath), path.resolve(homes[n])).split(path.sep).join('/');
        if (!r.startsWith('.')) r = `./${r}`;
        if (!bySource.has(r)) bySource.set(r, []);
        bySource.get(r).push(n);
    }
    if (!bySource.size) continue;
    const lines = fs.readFileSync(f.filePath, 'utf8').split('\n');
    let last = -1;
    lines.forEach((l, i) => {
        if (/^import\b/.test(l) || /^\} from '/.test(l)) last = i;
    });
    lines.splice(last + 1, 0, ...[...bySource].map(([src, ns]) => `import { ${ns.sort().join(', ')} } from '${src}';`));
    fs.writeFileSync(f.filePath, lines.join('\n'));
    added += [...bySource.values()].flat().length;
}
console.log(`added ${added} imports${unknown.size ? `; no home for ${[...unknown].join(', ')}` : ''}`);
