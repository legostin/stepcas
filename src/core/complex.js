// complex — complex numbers on doubles (principal branches everywhere).

import { Q } from './rational.js';
import { DEFAULT_LANGUAGE, notation, MACHINE } from '../i18n/index.js';

const fmt = (x, digits, comma) => {
    if (Number.isNaN(x)) return 'NaN';
    if (!Number.isFinite(x)) return x > 0 ? '∞' : '-∞';
    let s = x.toFixed(digits);
    if (s.includes('.')) s = s.replace(/\.?0+$/, '');
    if (s === '-0') s = '0';
    return comma ? s.replace('.', comma) : s;
};

export class Complex {
    constructor(re = 0, im = 0) {
        // no signed zeros: arg(−1 − 0i) would be −π and break principal branches
        this.re = re === 0 ? 0 : re;
        this.im = im === 0 ? 0 : im;
    }

    /** From Complex, number, bigint, Q, or {re, im}. */
    static of(x) {
        if (x instanceof Complex) return x;
        if (typeof x === 'number') return new Complex(x, 0);
        if (typeof x === 'bigint') return new Complex(Number(x), 0);
        if (x instanceof Q) return new Complex(x.toNumber(), 0);
        if (x && typeof x === 'object' && 're' in x) return new Complex(Number(x.re), Number(x.im ?? 0));
        return new Complex(NaN, NaN);
    }

    static fromPolar(r, theta) {
        return new Complex(r * Math.cos(theta), r * Math.sin(theta));
    }

    add(b) {
        b = Complex.of(b);
        return new Complex(this.re + b.re, this.im + b.im);
    }

    sub(b) {
        b = Complex.of(b);
        return new Complex(this.re - b.re, this.im - b.im);
    }

    mul(b) {
        b = Complex.of(b);
        if (this.im === 0 && b.im === 0) return new Complex(this.re * b.re, 0);
        return new Complex(this.re * b.re - this.im * b.im, this.re * b.im + this.im * b.re);
    }

    div(b) {
        b = Complex.of(b);
        if (b.im === 0) {
            if (b.re === 0) return new Complex(NaN, NaN);
            return new Complex(this.re / b.re, this.im / b.re);
        }
        // Smith's algorithm (avoids overflow)
        if (Math.abs(b.re) >= Math.abs(b.im)) {
            const r = b.im / b.re;
            const d = b.re + b.im * r;
            return new Complex((this.re + this.im * r) / d, (this.im - this.re * r) / d);
        }
        const r = b.re / b.im;
        const d = b.re * r + b.im;
        return new Complex((this.re * r + this.im) / d, (this.im * r - this.re) / d);
    }

    neg() {
        return new Complex(-this.re, -this.im);
    }

    conj() {
        return new Complex(this.re, -this.im);
    }

    inv() {
        return Complex.ONE.div(this);
    }

    abs() {
        return Math.hypot(this.re, this.im);
    }

    arg() {
        return Math.atan2(this.im, this.re);
    }

    isZero(eps = 0) {
        return Math.abs(this.re) <= eps && Math.abs(this.im) <= eps;
    }

    isReal(eps = 1e-12) {
        return Math.abs(this.im) <= eps * Math.max(1, Math.abs(this.re));
    }

    isFinite() {
        return Number.isFinite(this.re) && Number.isFinite(this.im);
    }

    isNaN() {
        return Number.isNaN(this.re) || Number.isNaN(this.im);
    }

    equals(b, eps = 1e-12) {
        b = Complex.of(b);
        const scale = Math.max(1, this.abs(), b.abs());
        return Math.abs(this.re - b.re) <= eps * scale && Math.abs(this.im - b.im) <= eps * scale;
    }

    exp() {
        const r = Math.exp(this.re);
        if (this.im === 0) return new Complex(r, 0);
        return new Complex(r * Math.cos(this.im), r * Math.sin(this.im));
    }

    /** Principal logarithm; log 0 = −∞. */
    log() {
        if (this.im === 0 && this.re > 0) return new Complex(Math.log(this.re), 0);
        return new Complex(Math.log(this.abs()), this.arg());
    }

    /** Principal power z^w (integer w by repeated squaring). */
    pow(w) {
        w = Complex.of(w);
        if (w.im === 0 && Number.isInteger(w.re) && Math.abs(w.re) <= 1024) {
            let n = Math.abs(w.re);
            let result = Complex.ONE;
            let base = this;
            while (n > 0) {
                if (n & 1) result = result.mul(base);
                base = base.mul(base);
                n = Math.floor(n / 2);
            }
            return w.re < 0 ? Complex.ONE.div(result) : result;
        }
        if (this.isZero()) {
            if (w.re > 0) return Complex.ZERO;
            return new Complex(NaN, NaN);
        }
        if (this.im === 0 && this.re > 0 && w.im === 0) return new Complex(Math.pow(this.re, w.re), 0);
        return w.mul(this.log()).exp();
    }

    /** Principal square root (Re ≥ 0). */
    sqrt() {
        if (this.im === 0) return this.re >= 0 ? new Complex(Math.sqrt(this.re), 0) : new Complex(0, Math.sqrt(-this.re));
        const r = this.abs();
        const re = Math.sqrt((r + this.re) / 2);
        const im = Math.sqrt((r - this.re) / 2);
        return new Complex(re, this.im < 0 ? -im : im);
    }

    sin() {
        return new Complex(Math.sin(this.re) * Math.cosh(this.im), Math.cos(this.re) * Math.sinh(this.im));
    }

    cos() {
        return new Complex(Math.cos(this.re) * Math.cosh(this.im), -Math.sin(this.re) * Math.sinh(this.im));
    }

    tan() {
        return this.sin().div(this.cos());
    }

    cot() {
        return this.cos().div(this.sin());
    }

    sec() {
        return Complex.ONE.div(this.cos());
    }

    csc() {
        return Complex.ONE.div(this.sin());
    }

    sinh() {
        return new Complex(Math.sinh(this.re) * Math.cos(this.im), Math.cosh(this.re) * Math.sin(this.im));
    }

    cosh() {
        return new Complex(Math.cosh(this.re) * Math.cos(this.im), Math.sinh(this.re) * Math.sin(this.im));
    }

    tanh() {
        return this.sinh().div(this.cosh());
    }

    coth() {
        return this.cosh().div(this.sinh());
    }

    /** asin z = −i·log(iz + √(1 − z²)) */
    asin() {
        const iz = new Complex(-this.im, this.re);
        const w = iz.add(Complex.ONE.sub(this.mul(this)).sqrt()).log();
        return new Complex(w.im, -w.re);
    }

    acos() {
        return new Complex(Math.PI / 2, 0).sub(this.asin());
    }

    /** atan z = (i/2)·(log(1 − iz) − log(1 + iz)) */
    atan() {
        const iz = new Complex(-this.im, this.re);
        const d = Complex.ONE.sub(iz).log().sub(Complex.ONE.add(iz).log());
        return new Complex(-d.im / 2, d.re / 2);
    }

    acot() {
        if (this.isZero()) return new Complex(Math.PI / 2, 0);
        return Complex.ONE.div(this).atan();
    }

    asinh() {
        return this.add(this.mul(this).add(Complex.ONE).sqrt()).log();
    }

    acosh() {
        return this.add(this.add(Complex.ONE).sqrt().mul(this.sub(Complex.ONE).sqrt())).log();
    }

    atanh() {
        return Complex.ONE.add(this).log().sub(Complex.ONE.sub(this).log()).mul(0.5);
    }

    /** "3 + 2i", "-i", "2.5 - 1.5i" — in a language's notation ("2,5 - 1,5i" in Russian); digits = max fractional digits. */
    toString(lang = MACHINE, digits = 6) {
        const sep = notation(lang).decimalText;
        return this._fmt(lang, digits, sep === '.' ? null : sep, 'i');
    }

    /** TeX: "3 + 2i", with the language's decimal separator (2{,}5 in Russian). */
    toTex(lang = DEFAULT_LANGUAGE, digits = 6) {
        const sep = notation(lang).decimalTex;
        return this._fmt(lang, digits, sep === '.' ? null : sep, 'i');
    }

    _fmt(lang, digits, comma, unit) {
        const re = fmt(this.re, digits, comma);
        const imAbs = fmt(Math.abs(this.im), digits, comma);
        const imZero = imAbs === '0';
        const reZero = re === '0';
        if (imZero) return re;
        const imPart = (imAbs === '1' ? '' : imAbs) + unit;
        const neg = this.im < 0;
        if (reZero) return (neg ? '-' : '') + imPart;
        return `${re} ${neg ? '-' : '+'} ${imPart}`;
    }
}

Complex.ZERO = new Complex(0, 0);
Complex.ONE = new Complex(1, 0);
Complex.I = new Complex(0, 1);
