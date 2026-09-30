// English grammar the templates need.

/** 1 → first, 2 → second, 3 → third, else 4th, 21st, 22nd, … */
export function ordinal(n) {
    const words = ['first', 'second', 'third'];
    if (n >= 1 && n <= 3) return words[n - 1];
    const k = n % 100;
    const suffix = k >= 11 && k <= 13 ? 'th' : ['th', 'st', 'nd', 'rd'][n % 10] ?? 'th';
    return `${n}${suffix}`;
}
