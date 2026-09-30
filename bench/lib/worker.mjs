// stepcas bench — the worker that runs tasks (the main thread kills it on a timeout).
import { parentPort } from 'node:worker_threads';
import { runTask } from './runner.mjs';

parentPort.on('message', (t) => {
    const t0 = performance.now();
    let res;
    try {
        res = runTask(t);
    } catch (e) {
        res = { status: e && e.msg ? 'refused' : 'error', note: String((e && (e.msg?.en || e.message)) || e).slice(0, 200) };
    }
    res.ms = Math.round(performance.now() - t0);
    if (typeof res.got !== 'string' && res.got !== undefined) res.got = String(res.got);
    parentPort.postMessage({ id: t.id, ...res });
});
