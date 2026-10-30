// Solves off the main thread, so a slow task never freezes the page; the page restarts the worker if it takes too long.
import { run, randomTask } from './run.js';

self.onmessage = ({ data }) => {
    const { id, type, mode, fields, lang, seed } = data;
    if (type === 'random') self.postMessage({ id, task: randomTask(mode, seed) });
    else self.postMessage({ id, view: run(mode, fields, lang) });
};

self.postMessage({ ready: true });
