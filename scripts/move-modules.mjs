// Move source modules to new paths and rewrite every relative import that points at them.
//   node scripts/move-modules.mjs '{"src/diff.js": "src/calculus/derivative.js", …}'
// Files are moved with `git mv`; imports are rewritten in src/, test/, bench/ and scripts/.
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';

const root = process.cwd();
const map = JSON.parse(process.argv[2]);
const abs = (p) => path.resolve(root, p);
const moves = new Map(Object.entries(map).map(([a, b]) => [abs(a), abs(b)]));

const files = [];
const walk = (d) => {
    for (const f of fs.readdirSync(d)) {
        const p = path.join(d, f);
        if (f === 'node_modules' || f.startsWith('.')) continue;
        if (fs.statSync(p).isDirectory()) walk(p);
        else if (/\.(m?js|cjs)$/.test(f)) files.push(p);
    }
};
for (const d of ['src', 'test', 'bench', 'scripts']) if (fs.existsSync(abs(d))) walk(abs(d));

const where = (p) => moves.get(p) ?? p;
const rel = (from, to) => {
    const r = path.relative(path.dirname(from), to).split(path.sep).join('/');
    return r.startsWith('.') ? r : `./${r}`;
};
for (const f of files) {
    const src = fs.readFileSync(f, 'utf8');
    const out = src.replace(/(\bfrom\s+|\bimport\s*\(\s*|\brequire\s*\(\s*)(['"])(\.{1,2}\/[^'"]+)\2/g, (m, pre, q, spec) => {
        const target = path.resolve(path.dirname(f), spec);
        if (!moves.has(target) && !moves.has(f)) return m;
        return `${pre}${q}${rel(where(f), where(target))}${q}`;
    });
    if (out !== src) fs.writeFileSync(f, out);
}
for (const [a, b] of moves) {
    fs.mkdirSync(path.dirname(b), { recursive: true });
    execFileSync('git', ['mv', a, b], { cwd: root });
}
console.log(`moved ${moves.size} files`);
