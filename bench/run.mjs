// stepcas bench: run the task corpus through the engine and report by source and topic.
//   node bench/run.mjs [--source ege-profile] [--topic log-eq] [--id ege-p-001] [--wrong] [--timeout 8000] [--strict]
// --strict exits with 1 when any answer is wrong or any task errs or times out (for CI).
// Writes bench/out/results.json and bench/REPORT.md (the report is committed: it is the engine's scoreboard).
import fs from 'node:fs';
import path from 'node:path';
import { Worker } from 'node:worker_threads';
import { fileURLToPath } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const argv = process.argv.slice(2);
const opt = (k, d = null) => {
    const i = argv.indexOf(`--${k}`);
    return i >= 0 ? argv[i + 1] : d;
};
const flag = (k) => argv.includes(`--${k}`);
const TIMEOUT = +opt('timeout', 8000);

async function loadTasks() {
    const out = [];
    const walk = async (dir) => {
        for (const f of fs.readdirSync(dir).sort()) {
            const p = path.join(dir, f);
            if (fs.statSync(p).isDirectory()) await walk(p);
            else if (f.endsWith('.json')) for (const t of JSON.parse(fs.readFileSync(p, 'utf8'))) out.push({ ...t, file: path.relative(here, p) });
            else if (f.endsWith('.mjs') && !f.startsWith('_')) for (const t of (await import(p)).default) out.push({ ...t, file: path.relative(here, p) });
        }
    };
    await walk(path.join(here, 'tasks'));
    // generated sets
    const gen = path.join(here, 'gen');
    if (fs.existsSync(gen))
        for (const f of fs.readdirSync(gen).filter((x) => x.endsWith('.json')))
            for (const t of JSON.parse(fs.readFileSync(path.join(gen, f), 'utf8'))) out.push({ ...t, file: `gen/${f}` });
    const ids = new Set();
    for (const t of out) {
        if (ids.has(t.id)) throw new Error(`duplicate task id ${t.id}`);
        ids.add(t.id);
    }
    return out;
}

let tasks = await loadTasks();
if (opt('source')) tasks = tasks.filter((t) => t.source === opt('source'));
if (opt('topic')) tasks = tasks.filter((t) => t.topic === opt('topic'));
if (opt('id')) tasks = tasks.filter((t) => t.id === opt('id'));

function makeWorker() {
    return new Worker(new URL('./lib/worker.mjs', import.meta.url));
}

async function runAll(list) {
    const results = [];
    let w = makeWorker();
    for (const t of list) {
        const res = await new Promise((resolve) => {
            const timer = setTimeout(() => {
                w.terminate();
                w = makeWorker();
                resolve({ id: t.id, status: 'timeout', ms: TIMEOUT });
            }, TIMEOUT);
            const onMsg = (m) => {
                if (m.id !== t.id) return;
                clearTimeout(timer);
                w.off('message', onMsg);
                resolve(m);
            };
            w.on('message', onMsg);
            w.postMessage(t);
        });
        results.push({ ...t, result: res });
        if (!flag('quiet'))
            process.stdout.write(
                res.status === 'correct'
                    ? '.'
                    : res.status === 'wrong'
                      ? 'W'
                      : res.status === 'timeout'
                        ? 'T'
                        : res.status === 'noapi'
                          ? '_'
                          : res.status === 'error'
                            ? 'E'
                            : 'r',
            );
    }
    await w.terminate();
    process.stdout.write('\n');
    return results;
}

const results = await runAll(tasks);

/* ------------------------------------------------------------------ report */

const STATUSES = ['correct', 'wrong', 'refused', 'noapi', 'error', 'timeout'];
const group = (key) => {
    const m = new Map();
    for (const r of results) {
        const k = key(r);
        if (!m.has(k)) m.set(k, { total: 0, steps: 0, ms: 0, ...Object.fromEntries(STATUSES.map((s) => [s, 0])) });
        const g = m.get(k);
        g.total++;
        g[r.result.status]++;
        if (r.result.status === 'correct' && r.result.steps > 0) g.steps++;
        g.ms += r.result.ms || 0;
    }
    return m;
};
const pct = (a, b) => (b ? `${Math.round((100 * a) / b)}%` : '—');
const row = (name, g) =>
    `| ${name} | ${g.total} | **${pct(g.correct, g.total)}** | ${g.wrong || ''} | ${g.refused || ''} | ${g.noapi || ''} | ${(g.error || 0) + (g.timeout || 0) || ''} | ${pct(g.steps, g.correct)} | ${Math.round(g.ms / g.total)} |`;
const head = '| | tasks | solved | wrong | refused | no API | error/timeout | with steps | ms/task |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|';

const all = group(() => 'all').get('all');
const bySource = group((r) => r.source);
const byTopic = group((r) => `${r.source} · ${r.topic}`);
const wrong = results.filter((r) => r.result.status === 'wrong' || r.result.status === 'error');

const SOURCE_NAMES = {
    'ege-profile': 'ЕГЭ, профиль',
    'ege-base': 'ЕГЭ, база',
    oge: 'ОГЭ',
    ent: 'ЕНТ (Казахстан)',
    university: 'Первый курс',
    generated: 'Сгенерированные',
};
let md = `# stepcas bench\n\nThe engine against ${all.total} tasks with checked answers. Generated by \`node bench/run.mjs\`.\n\n`;
md += `**Solved: ${pct(all.correct, all.total)}** · wrong: ${all.wrong} · refused: ${all.refused} · no API yet: ${all.noapi} · errors/timeouts: ${all.error + all.timeout}\n\n`;
md += `## By source\n\n${head}\n${[...bySource]
    .sort()
    .map(([k, g]) => row(SOURCE_NAMES[k] || k, g))
    .join('\n')}\n\n`;
md += `## By topic\n\n${head}\n${[...byTopic]
    .sort()
    .map(([k, g]) => row(k, g))
    .join('\n')}\n\n`;
if (wrong.length) {
    md += `## Wrong answers and errors (${wrong.length})\n\nThe most important list: a wrong answer costs more than a refusal.\n\n| id | task | expected | got | note |\n|---|---|---|---|---|\n`;
    md += wrong
        .map(
            (r) =>
                `| ${r.id} | \`${String(r.task).replace(/\|/g, '\\|')}\` | ${JSON.stringify(r.answer).replace(/\|/g, '\\|')} | ${String(r.result.got ?? '')
                    .replace(/\|/g, '\\|')
                    .slice(0, 80)} | ${String(r.result.note ?? '')
                    .replace(/\|/g, '\\|')
                    .slice(0, 80)} |`,
        )
        .join('\n');
    md += '\n';
}
fs.mkdirSync(path.join(here, 'out'), { recursive: true });
fs.writeFileSync(
    path.join(here, 'out/results.json'),
    JSON.stringify(
        results.map((r) => ({ id: r.id, source: r.source, topic: r.topic, task: r.task, ...r.result })),
        null,
        1,
    ),
);
if (!opt('source') && !opt('topic') && !opt('id')) fs.writeFileSync(path.join(here, 'REPORT.md'), md);
console.log(
    `solved ${all.correct}/${all.total} (${pct(all.correct, all.total)}) · wrong ${all.wrong} · refused ${all.refused} · no API ${all.noapi} · errors ${all.error} · timeouts ${all.timeout}`,
);
if (flag('wrong')) for (const r of wrong) console.log(`  ${r.id}: ${r.task} → ${r.result.got ?? ''} ${r.result.note ?? ''} (want ${JSON.stringify(r.answer)})`);
if (flag('strict') && all.wrong + all.error + all.timeout > 0) process.exit(1);
