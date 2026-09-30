// stepcas bench: turn every task into SymPy source (through the engine's parser) for bench/verify.py,
// which recomputes the answers independently.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import * as E from '../src/index.js';
import { toSympy } from './lib/sympy-src.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const tasks = [];
const walk = async (dir) => {
    for (const f of fs.readdirSync(dir).sort()) {
        const p = path.join(dir, f);
        if (fs.statSync(p).isDirectory()) await walk(p);
        else if (f.endsWith('.mjs') && !f.startsWith('_')) tasks.push(...(await import(p)).default);
        else if (f.endsWith('.json')) tasks.push(...JSON.parse(fs.readFileSync(p, 'utf8')));
    }
};
await walk(path.join(here, 'tasks'));
if (fs.existsSync(path.join(here, 'gen'))) for (const f of fs.readdirSync(path.join(here, 'gen')).filter((x) => x.endsWith('.json'))) tasks.push(...JSON.parse(fs.readFileSync(path.join(here, 'gen', f), 'utf8')));

const sp = (s) => {
    const node = E.parse(String(s), { lang: 'en', vars: ['a'] });
    return { src: toSympy(node), syms: E.freeVars(node) };
};
const out = [];
for (const t of tasks) {
    try {
        const o = { id: t.id, op: t.op, v: t.v || 'x', answer: {}, ask: t.ask };
        if (['solve', 'ineq', 'value', 'simplify', 'factor', 'diff', 'integrate', 'integral', 'limit', 'extremum', 'param', 'ode', 'series'].includes(t.op)) {
            if (t.op === 'system') continue;
            const x = sp(t.task);
            o.task = x.src; o.syms = x.syms;
        }
        if (t.op === 'system') { o.task = t.task.split(';').map((s) => sp(s.trim()).src); o.vars = t.vars || ['x', 'y']; }
        if (t.interval) o.interval = t.interval.map((s) => sp(s).src);
        if (t.segment) o.segment = t.segment.map((s) => sp(s).src);
        if (t.bounds) o.bounds = t.bounds.map((b) => (/inf/.test(String(b)) ? (String(b).startsWith('-') ? '-oo' : 'oo') : sp(b).src));
        if (t.at !== undefined) o.at = /inf/.test(String(t.at)) ? (String(t.at).startsWith('-') ? '-oo' : 'oo') : sp(t.at).src;
        if (t.side) o.side = t.side;
        if (t.kind) o.kind = t.kind;
        if (t.want) o.want = t.want;
        if (t.param) o.param = t.param;
        if (t.matrix) o.matrix = t.matrix;
        if (t.b) o.b = t.b;
        if (t.args) o.args = t.args;
        const a = t.answer || {};
        if (a.roots) o.answer.roots = a.roots.map((r) => sp(r).src);
        if (a.value !== undefined) o.answer.value = typeof a.value === 'number' ? String(a.value) : /^(inf|-inf|dne)$/.test(String(a.value)) ? String(a.value) : sp(a.value).src;
        if (a.expr) o.answer.expr = sp(a.expr).src;
        if (a.families) o.answer.families = a.families.map(([b, p]) => [sp(b).src, sp(p).src]);
        if (a.set) o.answer.set = a.set;
        if (a.none) o.answer.none = true;
        if (a.solutions) o.answer.solutions = a.solutions.map((s) => s.map((x) => sp(x).src));
        if (a.matrix) o.answer.matrix = a.matrix.map((r) => r.map((x) => sp(x).src));
        if (a.values) o.answer.values = a.values.map((x) => sp(x).src);
        if (a.x) o.answer.x = a.x.map((x) => sp(x).src);
        if (a.diverges) o.answer.diverges = true;
        out.push(o);
    } catch (e) {
        out.push({ id: t.id, op: t.op, error: String(e.message || e) });
    }
}
fs.mkdirSync(path.join(here, 'out'), { recursive: true });
fs.writeFileSync(path.join(here, 'out/verify.json'), JSON.stringify(out));
console.log(`prepared ${out.length} tasks for SymPy`);
