// random — deterministic seeded generator (mulberry32) for trainers and sampling.

function hashString(s) {
    // xmur3-style string hash → 32-bit seed
    let h = 1779033703 ^ s.length;
    for (let i = 0; i < s.length; i++) {
        h = Math.imul(h ^ s.charCodeAt(i), 3432918353);
        h = (h << 13) | (h >>> 19);
    }
    h = Math.imul(h ^ (h >>> 16), 2246822507);
    h = Math.imul(h ^ (h >>> 13), 3266489909);
    return (h ^ (h >>> 16)) >>> 0;
}

/**
 * rng(seed) → { seed, next() in [0, 1), int(a, b) inclusive, real(a, b), pick(arr), shuffle(arr) (a new array),
 * sign() ±1, nonZero(a, b) integer ≠ 0, chance(p), sample(arr, k) }. Same seed → same sequence.
 * Seeds may be numbers or strings.
 */
export function rng(seed = 1) {
    let a = typeof seed === 'number' && Number.isFinite(seed) ? Math.floor(seed) >>> 0 : hashString(String(seed));
    const next = () => {
        a = (a + 0x6d2b79f5) >>> 0;
        let t = a;
        t = Math.imul(t ^ (t >>> 15), t | 1);
        t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
    const int = (lo, hi) => {
        lo = Math.ceil(lo);
        hi = Math.floor(hi);
        if (hi < lo) [lo, hi] = [hi, lo];
        return lo + Math.floor(next() * (hi - lo + 1));
    };
    const r = {
        seed,
        next,
        int,
        real: (lo, hi) => lo + next() * (hi - lo),
        pick: (arr) => {
            if (!arr.length) throw new RangeError('pick from an empty array');
            return arr[Math.floor(next() * arr.length)];
        },
        shuffle: (arr) => {
            const out = [...arr];
            for (let i = out.length - 1; i > 0; i--) {
                const j = Math.floor(next() * (i + 1));
                [out[i], out[j]] = [out[j], out[i]];
            }
            return out;
        },
        sign: () => (next() < 0.5 ? -1 : 1),
        nonZero: (lo, hi) => {
            lo = Math.ceil(lo);
            hi = Math.floor(hi);
            if (hi < lo) [lo, hi] = [hi, lo];
            const size = hi - lo + 1 - (lo <= 0 && hi >= 0 ? 1 : 0);
            if (size <= 0) throw new RangeError('nonZero: the range holds only 0');
            let k = Math.floor(next() * size);
            let v = lo + k;
            if (lo <= 0 && v >= 0) v++;
            return v;
        },
        chance: (p) => next() < p,
        sample: (arr, k) => r.shuffle(arr).slice(0, k),
    };
    return r;
}
