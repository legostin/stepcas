// Compare two snapshots in one language only: node scripts/snapshot-lang.mjs a.json b.json ru
import fs from 'node:fs';
const [a, b, lang] = process.argv.slice(2);
const pick = (x) => {
    if (Array.isArray(x)) return x.map(pick);
    if (x && typeof x === 'object') {
        if ('ru' in x && 'en' in x && Object.keys(x).every((k) => ['ru', 'en'].includes(k))) return x[lang];
        return Object.fromEntries(Object.entries(x).map(([k, v]) => [k, pick(v)]));
    }
    return x;
};
const A = JSON.parse(fs.readFileSync(a, 'utf8'));
const B = JSON.parse(fs.readFileSync(b, 'utf8'));
let n = 0;
for (const k of Object.keys(A))
    if (JSON.stringify(pick(A[k])) !== JSON.stringify(pick(B[k]))) {
        n++;
        if (n < 5) console.log('differs:', k);
    }
console.log(`${n} tasks differ in ${lang}`);
