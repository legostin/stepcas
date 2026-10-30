// The demo page: the form for each mode, examples, the worker that solves, and the solution drawn with KaTeX.
import katex from 'https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.mjs';
import { MODES, MODE } from './modes.js';
import { EXAMPLES } from './examples.js';

const $ = (sel) => document.querySelector(sel);
const TIMEOUT_MS = 8000;

const state = {
    mode: 'equation',
    lang: 'en',
    fields: {}, // mode → the values typed in it, kept when switching tabs
};

// ---------------------------------------------------------------- maths on the page

const escape = (s) => String(s).replace(/[&<>"]/g, (c) => `&#${c.charCodeAt(0)};`);
const tex = (s, displayMode) => katex.renderToString(s, { displayMode, throwOnError: false, strict: false, output: 'html' });
// "text with $inline$ maths": the odd pieces are TeX
const inline = (s) =>
    String(s ?? '')
        .split(/\$([^$]+)\$/)
        .map((p, i) => (i % 2 ? tex(p, false) : escape(p)))
        .join('');

// ---------------------------------------------------------------- the worker

let worker = null;
let ready = null;
let nextId = 1;
const pending = new Map();

function startWorker() {
    worker = new Worker(new URL('./worker.js', import.meta.url), { type: 'module' });
    ready = new Promise((resolve) => {
        worker.onmessage = ({ data }) => {
            if (data.ready) return resolve();
            const p = pending.get(data.id);
            if (!p) return;
            pending.delete(data.id);
            clearTimeout(p.timer);
            p.resolve(data);
        };
    });
    worker.onerror = (e) => {
        status(`The engine failed to load: ${e.message ?? 'unknown error'}`);
    };
}

function ask(message) {
    const id = nextId++;
    return ready.then(
        () =>
            new Promise((resolve) => {
                const timer = setTimeout(() => {
                    // a task that runs away: stop the worker, answer for it, start a fresh one
                    pending.delete(id);
                    worker.terminate();
                    for (const p of pending.values()) {
                        clearTimeout(p.timer);
                        p.resolve({ timeout: true });
                    }
                    pending.clear();
                    startWorker();
                    resolve({ timeout: true });
                }, TIMEOUT_MS);
                pending.set(id, { resolve, timer });
                worker.postMessage({ id, ...message });
            }),
    );
}

// ---------------------------------------------------------------- the form

const mode = () => MODE[state.mode];
const values = () => (state.fields[state.mode] ??= {});

function renderTabs() {
    $('#tabs').innerHTML = MODES.map(
        (m) => `<button type="button" role="tab" data-mode="${m.id}" aria-selected="${m.id === state.mode}">${escape(m.label)}</button>`,
    ).join('');
}

function fieldHtml(fd, v) {
    const id = `f-${fd.key}`;
    const val = v[fd.key] ?? '';
    if (fd.type === 'check')
        return `<label class="field check" data-key="${fd.key}"><input type="checkbox" id="${id}" name="${fd.key}" ${val ? 'checked' : ''}> ${escape(fd.label)}</label>`;
    if (fd.type === 'select') {
        const opts = fd.options.map(([k, label]) => `<option value="${escape(k)}" ${String(val) === k ? 'selected' : ''}>${escape(label)}</option>`).join('');
        return `<label class="field select" data-key="${fd.key}"><span>${escape(fd.label)}</span><select id="${id}" name="${fd.key}">${opts}</select></label>`;
    }
    const placeholder = escape((fd.main && mode().hint?.(v)) || fd.placeholder || '');
    const input = fd.lines
        ? `<textarea id="${id}" name="${fd.key}" rows="${fd.lines}" placeholder="${placeholder}">${escape(val)}</textarea>`
        : `<input id="${id}" name="${fd.key}" value="${escape(val)}" placeholder="${placeholder}" autocapitalize="off" autocorrect="off">`;
    return `<label class="field ${fd.main ? 'main' : fd.size || ''}" data-key="${fd.key}"><span>${escape(fd.label)}</span>${input}</label>`;
}

function renderForm() {
    const m = mode();
    const v = values();
    $('#form').innerHTML = m.fields.map((fd) => fieldHtml(fd, v)).join('') + '<div class="field-error" id="field-error" hidden></div>';
    syncVisibility();
    $('#note').hidden = !m.note;
    $('#note').textContent = m.note ?? '';
    $('#random').hidden = !m.families;
    renderExamples();
}

// fields shown only for some choices (b for Ax = b), and the hint of the chosen operation
function syncVisibility() {
    const m = mode();
    const v = values();
    for (const fd of m.fields) {
        const el = $(`#form [data-key="${fd.key}"]`);
        if (el && fd.when) el.hidden = !fd.when(v);
    }
    const main = m.fields.find((fd) => fd.main);
    const input = $(`#f-${main.key}`);
    if (input) input.placeholder = (m.hint?.(v) ?? main.placeholder ?? '').replace(/^[^:]*:\s*/, '');
}

function readForm() {
    const v = {};
    for (const fd of mode().fields) {
        const el = $(`#f-${fd.key}`);
        if (!el) continue;
        if (fd.type === 'check') {
            if (el.checked) v[fd.key] = true;
        } else if (el.value !== '') v[fd.key] = el.value;
    }
    state.fields[state.mode] = v;
    return v;
}

function fill(fields) {
    state.fields[state.mode] = { ...fields };
    renderForm();
}

// ---------------------------------------------------------------- examples

function exampleSuffix(m, f) {
    const parts = [];
    for (const fd of m.fields) {
        const val = f[fd.key];
        if (fd.main || val == null || val === '' || fd.key === 'v') continue;
        if (fd.type === 'check') parts.push(fd.label.toLowerCase());
        else if (fd.type === 'select') {
            if (fd.key === 'op' && m.id !== 'matrices' && m.id !== 'numbers' && m.id !== 'algebra') continue;
            parts.push(fd.options.find(([k]) => k === String(val))?.[1] ?? val);
        } else parts.push(`${fd.label.toLowerCase()} ${val}`);
    }
    return parts.join(' · ');
}

function renderExamples() {
    const m = mode();
    const list = EXAMPLES[m.id] ?? [];
    $('#examples').innerHTML = list
        .map((ex, i) => {
            const q = String(ex.f.q).replace(/\n/g, '; ');
            const suffix = exampleSuffix(m, ex.f);
            const tag = suffix.toLowerCase().includes(ex.tag.toLowerCase()) ? '' : ex.tag;
            return `<button type="button" class="chip" data-example="${i}"><span class="chip-q">${escape(q)}</span>${suffix ? `<span class="chip-x">${escape(suffix)}</span>` : ''}${tag ? `<span class="chip-tag">${escape(tag)}</span>` : ''}</button>`;
        })
        .join('');
}

// ---------------------------------------------------------------- solving

let latest = 0;
let debounce = null;

function status(text) {
    $('#status').textContent = text ?? '';
}

async function solve({ scroll = false } = {}) {
    clearTimeout(debounce);
    const fields = readForm();
    const main = mode().fields.find((fd) => fd.main);
    saveHash();
    if (!fields[main.key]?.trim()) {
        $('#result').innerHTML = '<p class="muted">Type a task or pick an example.</p>';
        $('#read').hidden = true;
        return;
    }
    const ticket = ++latest;
    const slow = setTimeout(() => ticket === latest && status('Solving…'), 150);
    const res = await ask({ type: 'solve', mode: state.mode, fields, lang: state.lang });
    clearTimeout(slow);
    if (ticket !== latest) return;
    status('');
    renderResult(res, fields);
    if (scroll && window.matchMedia('(max-width: 979px)').matches) $('#output').scrollIntoView({ behavior: 'smooth', block: 'start' });
}

function later() {
    clearTimeout(debounce);
    debounce = setTimeout(() => solve(), 600);
}

function stepsHtml(steps) {
    return `<ol class="steps">${steps
        .map(
            (s) => `<li class="${s.final ? 'final' : ''}">
                <div class="step-title">${inline(s.title)}${s.rule && s.rule !== 'answer' ? `<span class="rule">${escape(s.rule)}</span>` : ''}</div>
                ${s.tex ? `<div class="step-tex">${tex(s.tex, true)}</div>` : ''}
                ${s.text ? `<p class="step-text">${inline(s.text)}</p>` : ''}
                ${s.sub ? `<details class="sub"><summary>${s.sub.length === 1 ? 'Detail' : `${s.sub.length} details`}</summary>${stepsHtml(s.sub)}</details>` : ''}
            </li>`,
        )
        .join('')}</ol>`;
}

function renderResult(res, fields) {
    const out = $('#result');
    const read = $('#read');
    if (res.timeout) {
        read.hidden = true;
        out.innerHTML = `<div class="card bad"><p>This task took longer than ${TIMEOUT_MS / 1000} seconds, so it was stopped.</p></div>`;
        return;
    }
    const v = res.view;
    read.hidden = !v.read;
    if (v.read) $('#read-tex').innerHTML = tex(`\\displaystyle ${v.read}`, false);
    markError(v, fields);

    if (!v.ok) {
        // a parse error points into the input; anything else is a task the engine cannot solve
        const unsupported = v.kind === 'unsupported' && v.pos == null;
        out.innerHTML = `<div class="card ${unsupported ? 'warn' : 'bad'}">
            <div class="card-label">${unsupported ? 'No answer' : 'Can’t read this'}</div>
            <p>${inline(v.reason)}</p>
            ${unsupported ? '<p class="muted small">The engine says so rather than guess. Try another form of the task.</p>' : ''}
        </div>${v.steps.length ? stepsHtml(v.steps) : ''}`;
        return;
    }
    const meta = [v.method && `<span class="chip-meta">${escape(v.method)}</span>`, `<span class="ms">${v.ms < 1 ? '<1' : Math.round(v.ms)} ms</span>`]
        .filter(Boolean)
        .join('');
    out.innerHTML = `<div class="card answer">
            <div class="card-label">Answer ${meta}</div>
            <div class="answer-tex">${v.answerTex ? tex(v.answerTex, true) : escape(v.answerText ?? '')}</div>
            ${v.extras.map((x) => `<div class="extra"><span>${escape(x.label)}</span>${tex(x.tex, false)}</div>`).join('')}
            ${v.answerText ? `<div class="plain"><code>${escape(v.answerText)}</code><button type="button" class="copy small" data-text="${escape(v.answerText)}">Copy</button></div>` : ''}
        </div>
        ${stepsHtml(v.steps)}`;
}

// underline where the engine stopped reading
function markError(v, fields) {
    const box = $('#field-error');
    if (!box) return;
    const main = mode().fields.find((fd) => fd.main);
    const text = fields[main.key] ?? '';
    if (v.ok || v.pos == null || v.pos > text.length) {
        box.hidden = true;
        return;
    }
    const end = Math.min(text.length, v.pos + Math.max(1, v.len ?? 1));
    const at =
        v.pos >= text.length
            ? `${escape(text)}<mark class="caret"> </mark>`
            : `${escape(text.slice(0, v.pos))}<mark>${escape(text.slice(v.pos, end))}</mark>${escape(text.slice(end))}`;
    box.innerHTML = `<code>${at}</code>`;
    box.hidden = false;
}

// ---------------------------------------------------------------- the address keeps the task, so it can be shared

function saveHash() {
    const p = new URLSearchParams({ m: state.mode });
    for (const [k, val] of Object.entries(values())) p.set(k, val === true ? '1' : val);
    if (state.lang !== 'en') p.set('lang', state.lang);
    history.replaceState(null, '', `#${p}`);
}

function loadHash() {
    const p = new URLSearchParams(location.hash.slice(1));
    const m = p.get('m');
    if (p.get('lang') === 'ru') state.lang = 'ru';
    if (!MODE[m]) return false;
    state.mode = m;
    const f = {};
    for (const fd of MODE[m].fields) if (p.has(fd.key)) f[fd.key] = fd.type === 'check' ? true : p.get(fd.key);
    state.fields[m] = f;
    return true;
}

// ---------------------------------------------------------------- wiring

function switchMode(id) {
    readForm();
    state.mode = id;
    if (!state.fields[id]) state.fields[id] = { ...(EXAMPLES[id]?.[0]?.f ?? {}) };
    renderTabs();
    renderForm();
    solve();
}

function setLang(lang) {
    state.lang = lang;
    for (const b of document.querySelectorAll('.lang button')) b.setAttribute('aria-pressed', String(b.dataset.lang === lang));
    solve();
}

async function copy(text, button) {
    try {
        await navigator.clipboard.writeText(text);
        const was = button.textContent;
        button.textContent = 'Copied';
        setTimeout(() => (button.textContent = was), 1200);
    } catch {}
}

function wire() {
    $('#tabs').addEventListener('click', (e) => {
        const b = e.target.closest('[data-mode]');
        if (b && b.dataset.mode !== state.mode) switchMode(b.dataset.mode);
    });
    $('#form').addEventListener('submit', (e) => {
        e.preventDefault();
        solve({ scroll: true });
    });
    $('#form').addEventListener('input', (e) => {
        if (e.target.matches('select, input[type=checkbox]')) return;
        later();
    });
    $('#form').addEventListener('change', (e) => {
        if (!e.target.matches('select, input[type=checkbox]')) return;
        readForm();
        syncVisibility();
        solve();
    });
    $('#form').addEventListener('keydown', (e) => {
        if (e.key === 'Enter' && (e.metaKey || e.ctrlKey)) {
            e.preventDefault();
            solve({ scroll: true });
        }
    });
    $('#examples').addEventListener('click', (e) => {
        const b = e.target.closest('[data-example]');
        if (!b) return;
        fill(EXAMPLES[state.mode][Number(b.dataset.example)].f);
        solve({ scroll: true });
    });
    $('#random').addEventListener('click', async () => {
        const res = await ask({ type: 'random', mode: state.mode, seed: Math.floor(Math.random() * 1e9) });
        if (!res.task) return;
        fill(res.task.fields);
        solve({ scroll: true });
        status(`Generated: ${res.task.prompt}`);
    });
    document.querySelector('.lang').addEventListener('click', (e) => {
        const b = e.target.closest('[data-lang]');
        if (b && b.dataset.lang !== state.lang) setLang(b.dataset.lang);
    });
    document.addEventListener('click', (e) => {
        const b = e.target.closest('.copy');
        if (!b) return;
        copy(b.dataset.text ?? document.querySelector(b.dataset.copy)?.textContent ?? '', b);
    });
}

function main() {
    if (!loadHash()) state.fields.equation = { ...EXAMPLES.equation[0].f };
    for (const b of document.querySelectorAll('.lang button')) b.setAttribute('aria-pressed', String(b.dataset.lang === state.lang));
    startWorker();
    renderTabs();
    renderForm();
    wire();
    solve();
}

main();
