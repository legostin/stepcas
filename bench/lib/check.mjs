// stepcas bench — comparing the engine's answers with the expected ones.
// Expected answers are plain strings (read with the engine's parser, which is not what is being measured);
// comparisons are numeric with a tolerance, so equal forms of one answer (1/√2 and √2/2) both count.
import * as E from '../../src/index.js';

const TOL = 1e-8;

export function num(x) {
    if (typeof x === 'number') return x;
    if (x == null) return NaN;
    if (typeof x === 'object' && x.type) {
        try { const v = E.evaluate(x, {}); return typeof v === 'number' ? v : NaN; } catch { return NaN; }
    }
    const s = String(x).trim();
    if (/^[+]?(inf|∞|oo)$/i.test(s)) return Infinity;
    if (/^[-−](inf|∞|oo)$/i.test(s)) return -Infinity;
    try { const v = E.evaluate(E.parse(s, { lang: 'en' }), {}); return typeof v === 'number' ? v : NaN; } catch { return NaN; }
}

export const close = (a, b) => (a === b) || (Number.isFinite(a) && Number.isFinite(b) && Math.abs(a - b) <= TOL * Math.max(1, Math.abs(a), Math.abs(b)));

export function sameNumbers(got, want) {
    const g = [...new Set(got.map((x) => +x.toPrecision(12)))].sort((a, b) => a - b);
    const w = [...new Set(want.map((x) => +x.toPrecision(12)))].sort((a, b) => a - b);
    return g.length === w.length && g.every((x, i) => close(x, w[i]));
}

// Roots of periodic families base + period·n inside [lo, hi].
export function familyRoots(fams, lo = -20, hi = 20) {
    const out = [];
    for (const [b, p] of fams) {
        const base = num(b), per = num(p);
        if (!Number.isFinite(base)) continue;
        if (!Number.isFinite(per) || per === 0) { if (base >= lo && base <= hi) out.push(base); continue; }
        for (let n = Math.ceil((lo - base) / per); base + n * per <= hi; n++) out.push(base + n * per);
    }
    return out;
}

// Functions agree at sample points (where both are defined; enough such points required).
export function sameFunction(a, b, vars = ['x']) {
    let fa, fb;
    try {
        fa = E.compile(typeof a === 'string' ? E.parse(a, { lang: 'en' }) : a, vars);
        fb = E.compile(typeof b === 'string' ? E.parse(b, { lang: 'en' }) : b, vars);
    } catch { return false; }
    let good = 0;
    for (let i = 0; i < 40; i++) {
        const pt = vars.map((_, k) => -3.7 + ((i * 0.731 + k * 1.37) % 7.3));
        let x, y;
        try { x = fa(...pt); y = fb(...pt); } catch { continue; }
        if (!Number.isFinite(x) || !Number.isFinite(y)) continue;
        if (Math.abs(x - y) > 1e-6 * Math.max(1, Math.abs(x), Math.abs(y))) return false;
        good++;
    }
    return good >= 8;
}

// F′ = f at sample points (indefinite integrals: any antiderivative counts).
export function isAntiderivative(F, f, v = 'x') {
    let g, h;
    try { g = E.compile(F, [v]); h = E.compile(typeof f === 'string' ? E.parse(f, { lang: 'en' }) : f, [v]); } catch { return false; }
    let good = 0;
    for (let i = 0; i < 40; i++) {
        const x = -3.3 + ((i * 0.617) % 6.9);
        let d, y;
        try { d = E.numDerivative(g, x); y = h(x); } catch { continue; }
        if (!Number.isFinite(d) || !Number.isFinite(y)) continue;
        if (Math.abs(d - y) > 1e-5 * Math.max(1, Math.abs(y))) return false;
        good++;
    }
    return good >= 8;
}

export function sameInterval(gotSet, wantText) {
    try { return E.intervalEquals(gotSet, wantText, 'ru'); } catch { return false; }
}
