// Build the generated part of the corpus: bench/gen/generated.json from fixed seeds (so it is reproducible).
//   node bench/gen.mjs [--per 12]
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { TASK_KINDS, generateSet } from '../src/generate.js';

const here = path.dirname(fileURLToPath(import.meta.url));
const argv = process.argv.slice(2);
const per = +(argv[argv.indexOf('--per') + 1] || 12);
const out = [];
for (const kind of TASK_KINDS) {
    for (const level of [1, 2, 3]) {
        const set = generateSet(kind, { count: per, seed: 1000 * (TASK_KINDS.indexOf(kind) + 1) + 100 * level, level });
        set.forEach((t, i) => {
            const { family: k, level: lv, seed, prompt, ...rest } = t;
            out.push({ id: `gen-${k}-${lv}-${String(i + 1).padStart(2, '0')}`, source: 'generated', topic: k, level: lv, seed, ...rest });
        });
    }
}
fs.mkdirSync(path.join(here, 'gen'), { recursive: true });
fs.writeFileSync(path.join(here, 'gen', 'generated.json'), JSON.stringify(out, null, 1));
console.log(`${out.length} tasks from ${TASK_KINDS.length} kinds`);
