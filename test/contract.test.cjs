// contract: every result of the solvers and every step has the documented shape — over the whole benchmark corpus.
//
//   result = {ok, kind, answer: {tex, text} when ok, reason when not, steps: Step[], …}
//   Step   = {title: Msg, tex?: string | {lang: string}, text?: Msg, rule?: string, data?: object, sub?: Step[],
//             final?: true}
const { test, before } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

let E;
let runTask;
let lastResult;
const tasks = [];
before(async () => {
    E = await import('../src/index.js');
    ({ runTask, lastResult } = await import('../bench/lib/runner.mjs'));
    const walk = async (dir) => {
        for (const f of fs.readdirSync(dir).sort()) {
            const p = path.join(dir, f);
            if (fs.statSync(p).isDirectory()) await walk(p);
            else if (f.endsWith('.mjs') && !f.startsWith('_')) tasks.push(...(await import(p)).default);
        }
    };
    await walk(path.join(__dirname, '../bench/tasks'));
    const gen = path.join(__dirname, '../bench/gen');
    for (const f of fs.readdirSync(gen).filter((x) => x.endsWith('.json'))) tasks.push(...JSON.parse(fs.readFileSync(path.join(gen, f), 'utf8')));
});

const STEP_KEYS = new Set(['title', 'tex', 'text', 'rule', 'data', 'sub', 'final']);
const isPlain = (x) => x && typeof x === 'object' && Object.getPrototypeOf(x) === Object.prototype;
const perLanguage = (x) => typeof x === 'string' || (isPlain(x) && E.LANGUAGES.every((l) => typeof x[l] === 'string'));
const readable = (x) => x instanceof E.Msg || perLanguage(x);

function checkStep(s, where, problems) {
    const bad = (what) => problems.push(`${where}: ${what}`);
    if (!isPlain(s)) return bad('not a plain object');
    for (const k of Object.keys(s)) if (!STEP_KEYS.has(k)) bad(`unknown field ${k}`);
    if (!(s.title instanceof E.Msg)) bad('title is not a message');
    if ('text' in s && !(s.text instanceof E.Msg)) bad('text is not a message');
    if ('tex' in s && !perLanguage(s.tex)) bad('tex is neither a string nor {lang: string}');
    if ('rule' in s && (typeof s.rule !== 'string' || !s.rule)) bad('rule is not a code');
    if ('data' in s && !isPlain(s.data)) bad('data is not a plain object');
    if ('final' in s && s.final !== true) bad('final is not true');
    if (!E.stepType(s)) bad(`no type: neither a rule nor a title message with a key (${s.title.in('en').slice(0, 50)})`);
    if ('sub' in s) {
        if (!Array.isArray(s.sub) || !s.sub.length) bad('sub is not a non-empty array');
        else s.sub.forEach((x, i) => checkStep(x, `${where}.sub[${i}]`, problems));
    }
}

test('every step of every corpus task has the documented shape', () => {
    const problems = [];
    let steps = 0;
    for (const t of tasks) {
        try {
            runTask(t);
        } catch {
            continue;
        }
        const r = lastResult();
        if (!Array.isArray(r?.steps)) continue;
        r.steps.forEach((s, i) => checkStep(s, `${t.id}.steps[${i}]`, problems));
        steps += r.steps.length;
    }
    assert.ok(steps > 3000, `the corpus produced only ${steps} steps`);
    assert.deepEqual(problems.slice(0, 60), []);
});

test('every solver result follows the contract: ok, kind, answer or reason, steps', () => {
    const problems = [];
    let n = 0;
    for (const t of tasks) {
        try {
            runTask(t);
        } catch {
            continue;
        }
        const r = lastResult();
        if (!r || typeof r.ok !== 'boolean') continue; // calculators keep their own convention
        n++;
        const bad = (what) => problems.push(`${t.id}: ${what}`);
        if (typeof r.kind !== 'string' || !r.kind) bad('no kind');
        if (!Array.isArray(r.steps)) bad('no steps array');
        if (r.ok) {
            if (!r.answer || !readable(r.answer.tex) || !readable(r.answer.text)) bad('an ok result without a readable answer');
            if (r.kind === 'invalid' || r.kind === 'unsupported') bad(`ok with kind ${r.kind}`);
        } else {
            if (!['invalid', 'unsupported'].includes(r.kind)) bad(`a failure of kind ${r.kind}`);
            if (!readable(r.reason)) bad('a failure without a reason');
            if ('answer' in r) bad('a failure with an answer');
        }
    }
    assert.ok(n > 1000, `only ${n} contract results in the corpus`);
    assert.deepEqual(problems.slice(0, 20), []);
});
