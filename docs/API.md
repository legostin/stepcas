# Math engine (`resources/js/math/engine`)

Pure ES modules, zero dependencies, no DOM; runs in browsers and in node 24.
`import * as E from '../engine/index.js'`. Every exported name is unique across all modules (star
re-exports drop collisions silently — `tests/Js/math-engine-core.test.cjs` checks it). Tests:
`node --test tests/Js/math-engine-core.test.cjs`.

## Conventions for every module

- **Errors** are `MathError` (from rational.js): `.msg = {ru, en}`, `.message` = English text,
  `.pos`/`.len` (position in the parsed string, when there is one), `.code` (`syntax`, `brackets`,
  `empty`, `no-arg`, `arity`, `unknown-fn`, `unsupported`, `div0`, `too-big`, `unbound`, `nan`,
  `not-expr`, …). Anything a stranger can type ends in a node or a `MathError`, never another
  exception.
- **Nodes are immutable** frozen plain objects (ast.js). Never mutate; build new ones.
- **Exact numbers** are `Q` (BigInt rationals); floats appear only in evaluate/compile/Complex.
- **Canonical form** is what `simplify()` returns (see simplify.js); `canon*` constructors keep it.
- **Languages**: RU is the default everywhere (`lang: 'ru' | 'en'`). RU: tg, ctg, arctg, arcctg,
  sh/ch/th, lg, decimal comma (`2{,}5` in TeX), list separator `;`. EN: tan, cot, arctan, sinh,
  `\log_{10}`, `2.5`, `,`.
- **Steps** (steps.js): `{title: {ru, en}, tex?: string | {ru, en}, text?: {ru, en}, rule?: string,
  sub?: Step[]}` — rendered by kit/steps.js.

## rational.js

- `class MathError extends Error` — `new MathError({ru, en}, pos?, len?, code?)` or
  `new MathError(msg, {pos, len, code})`; `.text(lang)`.
- `class Q` — `new Q(n, d = 1n)` (bigint or integer number; reduced, d > 0; d = 0 → MathError
  `div0`). `Q.of(x)`: Q | bigint | number (integers, finite decimals through the shortest decimal
  string: `0.1` → 1/10) | string (`"3/4"`, `"-2.5"`, `"2,5"`, `"1e-3"`, `"0.(3)"` periodic,
  `"1.5/2"`, spaces and `−` allowed). `Q.ZERO ONE MINUS_ONE TWO HALF`, `Q.max`, `Q.min`.
  Fields `n`, `d`; getters `num`, `den`. Methods (arguments go through `Q.of`): `add sub mul div neg
  inv pow(int) exactRoot(k) cmp eq lt gt le ge isZero isOne isInt isNeg isPos sign abs floor ceil
  trunc round` (half away from zero: 2.5 → 3, −2.5 → −3) `toNumber` (works for huge values)
  `toString` ("3/4") `toJSON isFiniteDecimal toDecimalString(digits = 10, lang = 'en')`
  (rounded, trailing zeros dropped) `toPeriodic(maxDigits)` → `{sign, int, pre, period}`
  `toPeriodicString(lang)` ("0,1(6)") `toTex(lang)` ("\frac{3}{4}", "-\frac{1}{2}", "2").
  `pow` refuses results over ~400 000 bits (MathError `too-big`).
- BigInt helpers: `bigGcd`, `bigLcm`, `bigAbs`, `bigBitLength`, `bigIsqrt(n)` (floor),
  `bigIroot(n, k)` (floor; odd k keeps the sign), `rootExtract(n, k)` → `{out, in}` with
  n = out^k · in, `in` free of k-th powers (trial division to 10⁵ plus an exact perfect-power test of
  the rest — for gigantic n with two big equal primes `in` may keep a square).

## ast.js

Node shapes (all frozen):

| type | fields | notes |
|---|---|---|
| `num` | `value: Q`, `raw?` | `raw` = decimal as typed (`'2,5'`, `'0.(3)'`), parser only |
| `sym` | `name`, `var?: true` | `x`, `a_1`, `alpha`, `x_12`; constants `pi e i inf`; `var` marks a constant name declared as a variable |
| `add`, `mul` | `args` | n-ary |
| `div` | `num`, `den` | kept by the parser; canonical form uses negative powers instead |
| `neg` | `arg` | |
| `pow` | `base`, `exp` | |
| `fn` | `name`, `args` | `sin cos tan cot sec csc asin acos atan acot sinh cosh tanh coth asinh acosh atanh ln lg exp sqrt abs sign floor ceil fact` (1 arg), `log` `[base, x]`, `root` `[x, n]` |
| `rel` | `op`, `lhs`, `rhs` | `= < <= > >= !=` |
| `chain` | `items`, `ops` | `a < x <= b` |
| `list` | `items` | systems, root lists |

Constructors: `num(q | number | string, raw?)`, `sym(name, isVar = false)`, `add(...args | [args])`
(one argument returns it, none → 0), `mul(...)` (none → 1), `div(a, b)`, `neg(a)`, `pow(b, e)`,
`fn(name, ...args)` (checks the name and arity), `rel(op, a, b)` (also `≤ ≥ ≠ ==`), `chain(items,
ops)`, `list(...)`. Arguments may be nodes, numbers, Q, or strings (`'x'` → sym, `'3/4'` → num):
`toNode(x)`.

Utilities: `CONSTANT_NAMES` (Set), `FUNCTION_NAMES` (Map name → arity), `isConst(node)`,
`nodeKey(node)` (canonical string, memoised; equal keys ⇔ structurally equal), `nodeEquals(a, b)`
(numbers by value, `raw` ignored), `freeVars(node)` (sorted, constants excluded), `containsVar(node,
name)`, `nodeSome(node, pred)`, `nodeChildren(node)`, `withChildren(node, kids)`, `mapNode(node, f)`
(post-order; `f` returns a replacement or undefined), `substitute(node, {x: 2, y: node})` (variables
only), `nodeSize(node)`, `numValue(node)` (exact Q of a numeric literal: nums with + − · / and integer
powers, else null), `isNumber(node)`.

## parse.js

`parse(text, opts?)` → node (throws MathError with a bilingual message and `pos`/`len`);
`tryParse(text, opts?)` → `{ok: true, node}` | `{ok: false, error}`.
Options: `vars: ['i', 'speed', 'x1']` (extra variable names; constants listed here become ordinary
variables), `foldCase: true` (X → x), `lang: 'en'` (a comma before exactly three digits is a
thousands separator: `1,000` = 1000), `maxLength` (default 2000 characters).

What it reads:

- **Numbers:** `12`, `3.5`, `3,5` (a comma between digits with no space is a decimal comma), `.5`,
  `0,(3)` (periodic), `1 000 000` / `12 345,5` / `1,000,000` (thousands). `3, 5`, `3;5` and
  `1,2,3` are lists. Two bare numbers in a row (`2 3`) are an error rather than a guess.
  **No scientific notation in expressions:** `2e3` is 2·e·3 (use `2*10^3`).
- **Operators:** `+ - * / ^ **`, `· × ⋅ ∙ ÷ −`, `:` (division), superscripts `x² x⁻¹ xⁿ`,
  subscripts `x₁`, `√x`, `√(x+1)`, `∛x`, `∜x`, `!` (factorial), `%` (= /100), `°` (= ·π/180),
  `π`, `∞`, `≤ ≥ ≠`, `<= >= != == =< => <>`. Unary `+`/`−` anywhere an operand may start
  (`2++3` = 5, `2*-3`). Brackets `() [] {}` group; `|x|`, `||x|-1|`, `2|x|`, `ln|x|` are moduli.
- **Precedence:** `^` is right-associative and binds tightest (`2^3^2` = 2⁹); a leading minus covers
  the product/power after it (`-x^2` = −(x²), `-2^2` = −4, `-2x` = −(2x)); implicit multiplication
  binds like `*` and `/`, left to right: **`1/2x` = (1/2)·x**, `6/2(1+2)` = 9, `x/2y` = (x/2)·y.
  The exponent takes one factor: `e^2x` = e²·x (write `e^(2x)`).
- **Implicit multiplication:** `2x`, `2(x+1)`, `(x+1)(x-1)`, `x(x+1)` (single letters are never
  functions — `f(x)` reads as f·x), `2sin x`, `x y`, `2π`, `3√2`. Letter runs split into known words
  and single letters: `xy` = x·y, `pix` = π·x, `sinx` = sin x, `arcsinx`; a declared variable (opts.vars)
  wins. A 3+ letter run before `(` that is close to a function name is an error with a suggestion
  (`sqr(x)`, `abc(x)` → "did you mean abs?"); `max min gcd lim sum int det mod …` are "not supported".
  Cyrillic look-alikes (х, у, а, с, е, о, р, к…) are read as Latin letters.
- **Functions** with or without brackets: `sin x`, `sin 2x` = sin(2x) — a bracket-less argument is one
  implicit product and stops at `+ − * /`, a relation, or the next function name: `sin x cos x` =
  sin x·cos x, `sin x/2` = (sin x)/2, `sin x^2` = sin(x²). Powers: `sin^2 x`, `sin^2(x)`, `sin²x` =
  (sin x)²; `sin^-1 x`, `sin^(-1)(x)`, `sin⁻¹x` = arcsin (trig and hyperbolic only). Names: `sin cos
  tg/tan ctg/cot sec cosec/csc arcsin/asin arccos arctg/arctan/atan arcctg/arccot/acot sh/sinh ch/cosh
  th/tanh cth/coth arsh arch arth ln lg log exp sqrt cbrt root abs sign/sgn floor ceil` (+ sine,
  cosine…; `Sin`, `LN` accepted). `log x` and `log(x)` are **log base 10** (like lg); `log_2 x`,
  `log_2(x)`, `log_{10}(x)`, `log_(a+1)(x)`, `log2(x)`, `log10 x`, `log(b, x)` (base first) have a base.
  `root(x, 3)` / `root(x; 3)` (inside root/log brackets a comma separates arguments unless the call
  uses `;`, so `root(2,5; 3)` is the cube root of 2.5).
- **Names:** greek `alpha beta gamma delta epsilon zeta theta iota kappa lambda mu rho sigma tau
  upsilon phi psi omega` (+ capitals, `varphi`…), unicode `α β γ δ ε θ λ μ π φ ψ ω …`; `eta nu xi chi`
  only as unicode or `\eta`. Subscripts `x_1`, `a_{12}`, `x_n`, `x₁` become part of the name (`a_12`).
- **Relations and lists:** `x^2-5x+6=0`, `2x+1 > 3`, `-1 < x <= 2` (chain); `x+y=3; x-y=1`, one item
  per line, `{…}` around a system is fine.
- **A bit of LaTeX:** `\frac{a}{b}`, `\sqrt{x}`, `\sqrt[3]{x}`, `\cdot \times \div \le \ge \ne \pi
  \infty \alpha…`, `\sin…`, `\operatorname{tg}`, `\left( \right)`, `\,`.
- **Kept as typed** (for steps): `div` stays `div`, `neg` stays `neg`, `sqrt` stays `sqrt`, decimals
  remember `raw`.
- **± in answers:** a list item with one `±` (also `∓`, `\pm`, `\mp`, `+/-`) is two items, the sign read
  in place (∓: minus first): `±2` → `2; -2`, `x = 1 ± √2` → `x = 1 + √2; x = 1 - √2`, `(1 ± √5)/2` →
  two fractions, `1 ± 2 + 3` → `1 + 2 + 3; 1 - 2 + 3`. Items are split at separators outside brackets (and
  inside brackets that wrap the whole input: `{1 ± 1; 7}`). Two ± in one item → MathError `unsupported`.
  `+-` is not ± here (it stays `a + (−b)`); kit/check.js reads `+-` as ± too and splits answers the same way.

Not read (clear errors): primes `f'(x)`, intervals `[1; 2)` as intervals (brackets must match),
`d/dx`, sums/limits/integrals notation.

`parseFunctionInput(text, opts?)` — a function as people type it for a solver or a plot → `{name, v, body,
vars, lhs, params}`: `f(x) = x^2 - 1` → name `'f'`, v `'x'`; `g(t)=t^3`, `s(t) := 5t^2`, `f(φ) = cos φ`,
`f(speed) = 2 speed` (a word in the brackets is declared as a variable), `f(x, y) = xy` (vars `['x', 'y']`,
v = the first); `y = sin x` → name null, lhs `'y'`; a bare expression → name null. Without brackets v is
the body's letter: `opts.v`, then x, t, y, z, u, v, w, s, n, k, else the first alphabetically (default
`opts.v` or `'x'`); params — the other letters (`f(x) = ax^2 + b` → `['a', 'b']`). Parse errors point into
the whole text; an equation that defines no function (`x^2 + y^2 = 1`, `x = 3`, `y = x + y`), an
inequality or a list → MathError `not-expr`.

## print.js

- `toTex(node, {lang = 'ru', mulDot = false, decimals = false, roots = false})` — KaTeX-ready TeX.
  Minimal brackets by precedence; `a + (−b)` and `a + (−2)·b` print as `a - b`, `a - 2b`. Implicit
  multiplication where it reads well (`2x`, `2\sqrt{3}`, `x(x + 1)`, `3\sin x`, `2\pi r`); `\cdot`
  before a factor starting with a digit or a fraction, between numbers, after a bracket-less function
  (`\sin x \cdot y`); negative factors bracketed (`2 \cdot (-3)`). Canonical products with negative
  powers print as one `\frac`; the rational coefficient goes into the fraction when the rest is
  "simple" — letters, their powers, numeric radicals, π (`\frac{3x}{4}`, `\frac{\sqrt{2}}{2}`,
  `\frac{\pi}{6}`) — otherwise it stays in front (`\frac{3}{4}(x + 1)`, `\frac{1}{2}\sin x`,
  `-\frac{1}{2}i`) and takes only the leading positive constants along (radicals, π, e, √(2π)):
  `\frac{\sqrt{3}}{3}\operatorname{arctg} x`, `\frac{2\sqrt{3}}{3}(x + 1)`, `\frac{\pi}{4}\sin x`,
  `\frac{\sqrt{2}}{2}x\sin x`. `x^{1/2}` → `\sqrt{x}`, `x^{1/n}` → `\sqrt[n]{x}`, `x^{-1}` → `\frac{1}{x}`,
  `x^{-1/2}` → `\frac{1}{\sqrt{x}}`; other rational exponents as `x^{\frac{2}{3}}`, or with **`roots: true`**
  the textbook way — the whole part out of the root for a letter or a number, the power under the root
  otherwise: `x^{3/2}` → `x\sqrt{x}`, `x^{5/2}` → `x^{2}\sqrt{x}`, `x^{2/3}` → `\sqrt[3]{x^{2}}`,
  `x^{7/3}` → `x^{2}\sqrt[3]{x}`, `x^{-3/2}` → `\frac{1}{x\sqrt{x}}`, `(x + 1)^{3/2}` → `\sqrt{(x + 1)^{3}}`,
  `(\sin x)^{3/2}` → `\sqrt{\sin^{3} x}` (calcTex prints this way). Parser nodes keep
  their shape (`x^(-1)` prints `x^{-1}`, `1/2x` prints `\frac{1}{2}x`).
  Functions: RU `\operatorname{tg}`, `\operatorname{ctg}`, `\operatorname{arctg}`, `\operatorname{arcctg}`,
  `\operatorname{sh/ch/th/cth}`, `\operatorname{arsh…}`, `\lg`, `\operatorname{cosec}`; EN `\tan \cot
  \arctan \operatorname{arccot} \sinh \cosh \tanh \coth \log_{10} \csc`; `\log_{a}`, `\operatorname{sgn}`,
  `\left|x\right|`, `\lfloor\rfloor`, `n!`, `(n + 1)!`. Bracket-less arguments only for a letter or a
  plain number (`\sin x`, `\ln 2`, `\sin \pi`) and for moduli (`\ln\left|x\right|`); otherwise
  `\sin(2x)`, `\sin\left(\frac{x}{2}\right)`. Powers of functions: `\sin^{2} x`, `\log_{2}^{2} x`.
  Numbers: rationals as `\frac`, `raw` decimals in the language (`2{,}5` / `2.5`), `decimals: true`
  prints finite decimals as decimals. `pi` → `\pi`, `inf` → `\infty`, `epsilon` → `\varepsilon`,
  `phi` → `\varphi`, `x_1` → `x_{1}`, multi-letter names → `\mathrm{…}`. Relations `\le \ge \ne`;
  lists joined by `;\ ` (RU) or `,\ ` (EN).
- `toText(node, {lang = 'ru'})` — plain text that `parse` reads back: `x^2 - 5x + 6`, `3x/4`,
  `sqrt(x)`, `root(x; 3)`, `log_2(x)`, `abs(x)`, `tg(x)` / `tan(x)`, `2,5` / `2.5`, lists `; ` / `, `.
  Guarantees (tested on corpora and fuzz): `parse(toText(n))` equals `n` for parser output, and
  `simplify(parse(toText(s)))` equals `s` for canonical `s`.
- `texNumber(value, lang = 'ru', {digits = 6, group = false, decimal = false})` — for widgets: Q prints
  exactly (`\frac{3}{4}`, or `0{,}75` with `decimal`), JS numbers are rounded to `digits` fractional
  digits with trailing zeros dropped, huge/tiny ones as `1{,}5 \cdot 10^{-7}`; `group` adds `\,`
  thousands; NaN → `\text{—}`, Infinity → `\infty`, −Infinity → `-\infty`.

## simplify.js

`simplify(node, {complex = false, mainVar})` → canonical node. Idempotent (tested on fuzz), never
expands products of sums, has a work budget (runaway input → MathError `too-big`); explicit division
by zero → MathError `div0`. Relations, chains and lists are simplified side by side (nothing is moved
across `=`).

Canonical form:

- `num` values are exact Q (negative allowed, no `raw`); no `div`, `neg`, `sqrt`, `root`, `exp`, `cbrt`:
  a/b → a·b⁻¹, −a → (−1)·a, √x → x^(1/2), `exp x` → e^x, `log_{10}` → `lg`, `log_e` → `ln`.
- `add`/`mul` are flat and n-ary; a `mul` has at most one number, first; like terms and like bases are
  merged (`3x + 2x` → 5x, `x·x` → x², `x²·x⁻¹` → x, `2^x·2^x` → 2^(2x)).
- A number times a single sum is distributed (`2(x+1)` → 2x + 2, so `x+1-(x+1)` → 0); a sum that
  shares a product with other factors, or is raised to an integer power, gives up its numeric content
  and sign: `x(2x+2)` → 2x(x + 1), `(2x+2)²` → 4(x + 1)², `(−x−1)²` → (x + 1)², `1/(6x+3)` → `\frac{1}{3(2x + 1)}`.
- Numeric radicals are `m^(1/q)` with an integer m ≥ 2 free of q-th powers: √12 → 2√3, 2^(2/3) → ∛4,
  4^(1/4) → √2, √8/2 → √2; denominators rationalised (1/√2 → √2/2); √2·√3 → √6, √2·√2 → 2, √2·∜2 → ∜8;
  radicals of positive constants (integers, π, e) with the same exponent ±1/q merge into one:
  √2·√π → √(2π) = `(2π)^(1/2)` (a pow of a product), √π·√e → √(πe), √8π → 2√(2π), 1/√(2π) stays whole
  (a numeric √m joins a √… in the denominator when m divides the coefficient's denominator: √2/(2√π) →
  1/√(2π)), √(2π)·√2 → 2√π;
  (4/9)^(1/2) → 2/3; real odd roots of negatives: (−8)^(1/3) → −2; `x^0` → 1 (also 0⁰), `1^x` → 1,
  0·anything → 0, x/x → 1 (removable points are not tracked). Integer powers of numbers are exact up
  to ~20 000 bits (bigger ones stay as powers: `2^{100000}`).
- `(x^a)^b` → x^(ab) when b is an integer; for rational a, b: `(x²)^(1/2)` → |x|, `(x⁴)^(1/2)` → x²,
  `(x³)^(1/3)` → x, `(√x)²` → x (valid where the left side is defined); symbolic exponents combine
  only over a positive base (`(e^x)^(1/2)` → e^(x/2)). `(ab)^n` distributes for integer n; for
  fractional n only positive factors come out (`(4x)^(1/2)` → 2√x).
- Known values: trig of kπ/n for n ∈ {1, 2, 3, 4, 6} (sin, cos, tan, cot, sec, csc, any multiple:
  sin(13π/6) = 1/2), undefined ones stay (`tg(π/2)`); other multiples of π are reduced into (0, π/2)
  by the reduction formulas (sin(9π/7) → −sin(2π/7)); arguments shifted by a multiple of π/2 too
  (sin(x + 2π) → sin x, cos(π/2 − x) → sin x, sin(π − x) → sin x, tg(x + π) → tg x, cos(x + π/2) → −sin x,
  tg(x + π/2) → −ctg x, sec/cosec alike), other shifts lose whole periods (sin(x + 7π/3) → sin(x + π/3),
  tg(x + 4π/3) → tg(x + π/3)); parity (sin(−x) → −sin x, cos(−x) → cos x);
  sin(arcsin x) → x; arcsin/arccos/arctg/arcctg of 0, 1/2, √2/2, √3/2, 1, √3/3, √3 and negatives
  (arccos(−1/2) → 2π/3); ln 1, ln e, ln(e^x) → x, e^(ln x) → x, e^(k ln x) → x^k, log_a a, log_a(a^k),
  exact rational logs (lg 100 → 2, log_4 8 → 3/2, log_{1/2} 4 → −2), a^(log_a x) → x, and in a sum
  a^(k·log_a y + …) → y^k·a^(…) (2^(log_2 3 + log_2 5) → 15, e^(2 ln x + 1) → e·x²); |−3|, |x²| →
  x², |2x| → 2|x|, |1 − √2| → √2 − 1 (constants by sign), |3+4i| → 5; sign, floor, ceil of numbers and
  real constants (floor(π) → 3); n! up to 1000; sinh/cosh/tanh at 0 and parity; sin²u + cos²u → 1
  (equal coefficients).
- The imaginary unit: i² = −1 always (i³ → −i, 1/i → −i); with `{complex: true}` also √−4 → 2i,
  (1+2i)(3−i) → 5+5i, 1/(1+i) → `\frac{1}{2} - \frac{1}{2}i`, (1+i)⁸ → 16, e^(iπ) → −1 (table angles), square
  roots of Gaussian rationals when they are Gaussian rationals (principal: √(3+4i) → 2+i, √(−2i) → 1−i; √(1+i)
  stays). Real-variable
  rules (|x|² = x², odd roots) are not applied to expressions that contain i.
- Term order (display): by degree in the main variable (`mainVar`, else x, y, z, t, else the first
  name), then total degree, then alphabetical; constants last — rational, radicals, π/e, i terms
  (`x² − 5x + 6`, `ax² + bx + c`, `x² + 2xy + y²`, `3 + 2i`, and `√2 − 1` rather than `−1 + √2`).
  Factor order: number, radicals, π, i, letters (natural order: x_2 before x_10), e^…, functions
  (sin before cos before tan…), sums. `toTex` starts a sum of constants with a positive term (ln 3 − ln 2)
  only for simplify output: a sum with parser shapes or unfolded numbers (a substitution: −x² + 4x − 4 at
  x = 2 prints `-2^{2} + 4 \cdot 2 - 4`) keeps its term order.

Canonical constructors for other modules (arguments must already be canonical):
`canonAdd(terms, opts)`, `canonMul(factors, opts)`, `canonPow(base, exp, opts)`,
`canonFn(name, args, opts)`; `canonContext(opts)` → `{add, mul, pow, fn, simplify}` sharing one work
budget (use it in loops); `splitCoeff(term)` → `{coef: Q, rest: node | null}`;
`compareTerms(a, b, mainVar)` (display order of two terms).

Not done by simplify (on purpose): expanding, factoring, cancelling rational functions (use
`combineFractions`), log rules like ln(xy) = ln x + ln y, trig identities beyond sin² + cos² and the
reduction formulas.

## expand.js

- `expand(node, {complex})` — simplify, then distribute products over sums and expand positive
  integer powers of sums (binomial formula for two terms, repeated multiplication otherwise),
  collecting like terms as it goes; function arguments are expanded too; negative and fractional
  powers of sums stay atoms (`(x+1)^2/x` → x + 1/x + 2). More than 1000 terms (predicted or produced)
  → MathError `too-big`: `(x+1)^200` is fine (~1 ms), `(x+y+z)^20` (231 terms, ~20 ms) is fine,
  `(x+y+z)^60` (1891 terms) is refused.
- `collectTerms(node, varName = 'x')` → `Map(degree → coefficient node)` in descending degree (degrees
  are numbers; 0.5 for √x, −1 for 1/x; coefficients may contain other letters); a relation is taken
  as lhs − rhs; null when the variable occurs non-polynomially (sin x). E.g. `(x+a)^2 = 2x` →
  {2: 1, 1: 2a − 2, 0: a²}.
- `combineFractions(node, {cancel = true})` (alias `rationalize`) — one fraction over the common
  denominator as a `div` node (a plain node when the denominator is 1): numerator expanded,
  denominator factored; with one variable and several different denominators the common denominator is the
  least one built from their factors over Q (`1/x + 1/(x²−x) − 2` → over x(x − 1), also with
  `{cancel: false}`); common numeric factors and polynomial factors of the denominator that divide
  the numerator (one variable) are cancelled: `1/x + 1/(x+1)` → (2x + 1)/(x(x + 1)),
  `(x²−1)/(x−1)` → x + 1. Relations/lists side by side.
- `numDen(node)` → `{num, den}` (canonical nodes; den = 1 without a fraction).

## poly.js

`class Poly` — univariate, coefficients `c[k]` of x^k (Q), immutable.

- Build: `new Poly([a0, a1, …])`, `Poly.fromCoeffs([a0, a1, …])` (lowest degree first),
  `Poly.fromDescending([an, …, a0])`, `Poly.monomial(c, k)`, `Poly.fromRoots([r…])`,
  `Poly.fromNode(node, varName = 'x')` → Poly | null (null for other letters, π, √2, x⁻¹, sin x…;
  `lhs = rhs` gives lhs − rhs; other relations → null; tries the node, then its expansion).
- Read: `degree` (−1 for 0), `lead`, `coeff(k)`, `descending()`, `isZero()`, `equals(p)`,
  `toNode(varName)` (canonical), `toTex(varName, lang)`, `toString(varName)` (`x^2 - 5x + 6`,
  `(1/2)x + 1/3`), `evalAt(q)` (exact), `evalNumber(x)` (double).
- Arithmetic: `add sub mul neg scale(q) pow(n) derivative() monic() divmod(p)` → `{q, r}`
  (MathError `div0` for the zero divisor), `gcd(p)` (monic), `content()` (with the sign of the
  leading coefficient) / `primitive()` (coprime integers, positive lead).
- Steps data: `longDivision(p)` → `{quotient, remainder, steps: [{dividend, term, product,
  remainder}]}` (деление уголком); `horner(a)` → `{top, row, value, quotient}` (row has the same
  length as top, its last entry is p(a)).
- Roots and factors: `rootCandidates()` (±p/q of the rational root theorem, sorted),
  `rationalRoots()` → `[{root: Q, mult}]` ascending, the array also carries `.candidates` (built lazily,
  on first read); with many candidates (|divisors(a₀)|·|divisors(aₙ)| > 4000: 735134400x⁵ − x − 735134400
  has ~74 000) the real roots are located numerically with rigorous inclusion discs and only the candidates
  inside them are tried — exactly, so nothing is missed (Wilkinson's (x−1)…(x−20) included), ms instead of seconds;
  `squareFree()` (Yun) → `[{poly (monic), mult}]`; `factor()` → `{constant: Q, factors: [{poly,
  mult}]}` over Q with primitive integer factors — linear ones from rational roots, quartics split
  into two quadratics when possible (x⁴ + 4, x⁴ + x² + 1), the rest left whole (irreducible for
  degree ≤ 3; higher-degree leftovers may still factor into cubics etc.); `discriminant()` for degree
  2 and 3 (null otherwise).
- `linearForm(node, vars = ['x'])` → `{coeffs: {x: Q, y: Q, …} (all listed variables, zeros
  included), constant: Q}` with node = Σ coeffs·var + constant (for a relation: of lhs − rhs), or null
  if not linear with rational coefficients (other letters → null).

## equiv.js

- `equivalent(a, b, {vars, complex, tol = 1e-9, seed})` — nodes or strings (parsed with the same
  options). 1) exact: `expand(simplify(a − b))` is 0 → true; a nonzero polynomial with rational
  coefficients → false. Canonical simplification may widen domains ((√x)² = x, x/x = 1) and such
  pairs count as equivalent. 2) numeric: 24 seeded non-integer points in several ranges (small,
  negative, medium, up to ±40); where both are finite they must agree to 1e-9 (relative; absolute
  near 0); a point with |x| ≤ 10 where one side is defined and the other is NaN means the domains
  differ on an interval → false (so `√(x²)` ≢ `x`, `ln(x²)` ≢ `2 ln x`), while removable points like
  x = 1 in `(x²−1)/(x−1)` ≡ `x+1` are never hit; ≥ 5 usable points required. 3) too few real points
  (`√(x−100)`, √ of negatives) → the same at complex points with principal branches. Expressions with
  i are compared in complex mode from the start. Equations: equivalent when lhs − rhs are
  proportional (`x+y=3` ≡ `2x+2y=6`, `x = 2` ≡ `2 = x`); inequalities need a positive factor after
  turning > into < (`x > 2` ≡ `-x < -2`); chains compare item-wise with equal operators; lists compare
  in order (use `sameSet` for unordered answers).
- `sameValue(a, b, {tol = 1e-9})` — numbers, Q, strings or nodes: exact when a − b simplifies to a
  number, else numeric (complex when i appears); `sameValue('pi', '3.14159', {tol: 1e-5})` for
  rounded answers.
- `sameSet(listA, listB, {multiset = false})` — arrays of values or list nodes / `"1; 2"` strings,
  order-free, duplicates ignored unless `multiset`; items with variables go through `equivalent`.

## evaluate.js, complex.js

- `evaluate(node, env = {}, {complex = false})` — env values: numbers, Q, bigint (Complex in complex
  mode). Real mode returns a number and **NaN for anything undefined** (√−1, ln 0, 1/0, 0⁻¹,
  arcsin 2, ctg 0, (−2)^x); `inf` → Infinity; the constant i → NaN. Literal rational exponents keep
  real odd roots (`(−8)^(1/3)` = −2, `root(x, 3)`, `∛x`); `fact` of a non-integer is Γ(x+1).
  Complex mode returns `Complex` with principal branches (there `(−8)^(1/3)` = 1 + 1.732i).
  Relations return booleans (1e-9 tolerance for =), lists arrays. Radians only. A variable missing
  from env → MathError `unbound`. `exactNumber(node)` = `numValue`.
- `compile(node, vars = ['x'])` → `(x) => number` (or `(x, y, …) =>`) — closures, no eval; constant
  subtrees folded; same real semantics; unknown variables → MathError at compile time; relations and
  lists → MathError `not-expr`.
- `class Complex(re, im)` (no signed zeros) — `Complex.of(x)`, `Complex.fromPolar(r, θ)`,
  `Complex.ZERO ONE I`; `add sub mul div neg conj inv abs arg exp log pow sqrt sin cos tan cot sec
  csc sinh cosh tanh coth asin acos atan acot asinh acosh atanh isZero(eps) isReal(eps) isFinite
  isNaN equals(b, eps)`; `toString(lang = 'en', digits = 6)` → `3 + 2i`, `-i`, `2,5 - 1,5i`;
  `toTex(lang = 'ru', digits = 6)` → `2{,}5 + i`.

## random.js, steps.js

- `rng(seed)` (number or string) → `{seed, next() ∈ [0, 1), int(a, b) (inclusive), real(a, b),
  pick(arr), shuffle(arr) (a copy), sign(), nonZero(a, b), chance(p), sample(arr, k)}` — mulberry32,
  same seed → same sequence.
- `L(ru, en = ru)` → `{ru, en}`; `step({title, tex, text, rule, sub})` → normalised step (`title`/`text`
  strings become `{ru, en}`; `tex` may be a string, `{ru, en}` or an AST node, printed for both
  languages and collapsed to one string when they agree; empty `sub` dropped); `texBoth(node, opts)`
  → string | `{ru, en}`; `pickLang(value, lang)`.

## Examples

```js
import * as E from '../engine/index.js';
const n = E.parse('x²−5x+6=0');                  // rel(=, x^2 - 5x + 6, 0)
E.toTex(n);                                       // 'x^{2} - 5x + 6 = 0'
E.Poly.fromNode(n).rationalRoots();               // [{root: 2, mult: 1}, {root: 3, mult: 1}]
E.toTex(E.simplify(E.parse('sqrt(8)/2 + sin(pi/6)')));   // '\frac{1}{2} + \sqrt{2}'
E.toTex(E.expand(E.parse('(2x-3)^2')));           // '4x^{2} - 12x + 9'
E.equivalent('ln(x^2)', '2ln|x|');                // true
E.toTex(E.parse('tg x'), { lang: 'en' });         // '\tan x'
const f = E.compile(E.parse('x^3 - x'));          // f(2) === 6
E.tryParse('sqr(x)').error.msg.ru;                // 'Функция «sqr» здесь не поддерживается'
```

## Known limits of the core

- `f(x)` inside expressions reads as f·x (only `parseFunctionInput` reads a definition `f(x) = …`); ± only
  as two list items; no derivatives/integrals/limits notation, no intervals, no scientific notation in
  expressions (see parse.js).
- simplify is not a normal form for rational functions or trig identities; use `combineFractions`,
  `expand`, `equivalent`.
- `(−8)^(1/3)` is −2 (real root) in simplify and in real evaluation, but the principal value in
  complex evaluation; expressions mixing i with odd roots of negatives follow the real-root rule in
  simplify.
- Factoring over Q finds rational roots, square-free parts and quartic splits; degree ≥ 5 leftovers
  can still hide factors. The rational root theorem needs divisors of the end coefficients: exact up
  to ~10¹², beyond that the candidate list may miss divisors of huge prime-like cofactors.
- `equivalent` is exact for polynomials and probabilistic (24 points, 1e-9) otherwise; functions that
  differ only on tiny sets or beyond |x| = 40 can pass.

<!-- Sections below: numtheory.js, numeric.js, matrix.js (written by the numbers/matrices agent). -->

## Conventions of numtheory.js, numeric.js, matrix.js

- **Steps:** a function returns its bare value; with `{steps: true}` it returns `{value, steps, …}`.
  Functions whose natural result is already an object (`ntEgcd`, `ntCrt`, `matSolve`, `matEigen`, …)
  just gain a `steps` field. Step = `{title: {ru, en}, tex?: string | {ru, en}, text?: {ru, en},
  rule?, sub?}` (the shape of steps.js); every step has a TeX line where there is something to show,
  and the text says what we do and why. Empty `sub` is omitted.
- **Numbers in TeX:** integers from five digits on are grouped with `\,` (`600\,851\,475\,143`);
  in plain text with a narrow no-break space. RU decimals use `{,}` in TeX and `,` in text.
- **Errors:** invalid input throws `MathError` with `.msg = {ru, en}` and a `.code`
  (`not-int`, `modulus`, `base`, `digit`, `shape`, `singular`, `no-sign-change`, `domain`, `too-big`, …).
- **Indices:** 0-based in data (`i`, `j`, `index`), 1-based in explanations (R₁, x₁, M₁₂).

## numtheory.js — number theory on BigInt

Inputs: BigInt, integer numbers, digit strings (`'600 851 475 143'`), Q; where a fraction makes
sense also `'1/3'`, `'0,1'`, `'0.(3)'`, numbers like `0.1` (read by their decimal form). Outputs: BigInt.

| Function | Returns (bare) | With `{steps: true}` |
|---|---|---|
| `ntGcd(a, b)` | gcd ≥ 0 | `{value, rows: [{a, b, q, r}], steps}` — the Euclid table |
| `ntLcm(a, b)` | lcm ≥ 0 (0 with a zero) | `{value, steps}` — via gcd, check by factorisation |
| `ntGcdMany(list \| ...args, opts?)`, `ntLcmMany` | BigInt | chained, sub-steps per pair |
| `ntEgcd(a, b)` | `{g, x, y}`, a·x + b·y = g | + `rows`, back-substitution steps |
| `ntDiophantine(a, b, c)` | `{solvable, g, x0, y0, dx, dy}`: x = x0 + dx·k, y = y0 + dy·k (x0 smallest ≥ 0) | + steps |
| `ntIsPrime(n)` | boolean | — |
| `ntMillerRabin(n, {bases?})` | `{prime, certain, witness, d, s, rounds: [{a, seq, pass}]}` | + steps (561 is exposed by a = 2) |
| `ntIsCarmichael(n)` | boolean (Korselt) | — |
| `ntFactor(n)` | `[{p: BigInt, e: number}]` ascending (of \|n\|; 1 → []) | `{value, tex, ladder: [{n, p}], steps}` |
| `ntFactorTex(factors)` | `2^{3} \cdot 3 \cdot 5^{2}` | — |
| `ntDivisors(n)`, `ntTau(n)`, `ntSigma(n, k = 1)`, `ntMobius(n)` | BigInt[] / BigInt / number | — |
| `ntPhi(n)` | φ(n) | formula, multiplicativity, listing for n ≤ 100 |
| `ntPrimesUpTo(n)` | number[] (n ≤ 10⁸) | — |
| `ntSieve(n)` | `{primes, isPrime: Uint8Array, spf: Int32Array}` (n ≤ 2·10⁷) | — |
| `ntPrimePi(n)` | number (Lucy_Hedgehog; 10¹⁰ in ~30 ms, n ≤ 10¹¹) | — |
| `ntNextPrime(n)`, `ntPrevPrime(n)` | BigInt / null | — |
| `ntIsPerfectSquare(n)`, `ntDigitSum(n, base = 10)` | boolean / BigInt | — |
| `ntModPow(a, e, m)` | a^e mod m in [0, m); e < 0 via the inverse (null if none) | `{value, rows: [{k, power, value, bit}], steps}` — square-and-multiply table + a Fermat/Euler check |
| `ntModInv(a, m)` | inverse in [0, m) or null | via extended Euclid |
| `ntSolveCongruence(a, b, m)` | `{solvable, d, x0, m0, solutions}` (x ≡ x0 mod m0; `solutions` mod m when d ≤ 1000) | + steps |
| `ntCrt(residues, moduli)` | `{solvable: true, x, m}` (m = lcm) or `{solvable: false, conflict: i}`; non-coprime moduli handled | + substitution steps (small moduli solved by trying values) |
| `ntOrder(a, m)`, `ntPrimitiveRoot(m)` | BigInt / null | — |
| `ntRsaKey(p, q, {e?})` | `{n, phi, e, d}` (e = 65537 or the smallest valid odd e) | + steps |
| `ntToBase(x, base)` | string: `'-ABC'`, `'0.0(0011)'` (period in brackets, `…` when cut at `maxDigits`, 60) | `{value, int, pre, period, truncated, negative, tex: {ru, en}, steps}` |
| `ntFromBase(str, base)` | BigInt, or Q for fractions (`'1A.8'`, `'0.(3)'`, comma allowed) | place-value sum, Horner, period rule |
| `ntContinuedFraction(x)` | `{terms: BigInt[], exact, tex}`; `{sqrt: n}` → `+ {a0, period, periodic}`; a double → terms of its exact binary value until the convergent reproduces it (`exact: false`) | Euclid-style steps (rationals), √n steps |
| `ntConvergents(terms \| cf, {count?})` | `[{p, q}]` (count unrolls a period) | — |
| `ntBestApprox(x, maxDen)` | `{p, q}` (semiconvergents included: π, 1000 → 355/113) | — |
| `ntEgyptian(x)` | BigInt[] denominators, greedy, 0 < x ≤ 1 | + steps |
| `ntDivisibilityRule(n, d)` | `{divides, remainder, steps}` for d ∈ {2, 3, 4, 5, 8, 9, 10, 11, 25} and 6, 12, 15, 18, 20, 36, 45, 75, 100 | (always) |

Limits: primality is deterministic below 3.3·10²⁴ (bases 2…41), probabilistic above (24 extra
bases, error < 4⁻³⁷ — stated in the steps). Factoring: trial division to 10⁴, then Pollard–Brent ρ
with a budget of ~4·10⁶ iterations (≈1 s): numbers whose second-largest prime factor is below
~10¹² factor quickly (two 13-digit primes: ~0.3 s); harder ones throw `MathError` code `too-big`
(2¹²⁸ + 1 does).

## numeric.js — floating-point methods

- Roots: `numBisect(f, a, b, {tol = 1e-12, maxIter, trace})` → `{root, iterations, converged,
  trace?: [{a, b, m, fa, fb, fm}]}` (throws `no-sign-change`); `numBrent(f, a, b, {tol})`;
  `numNewton(f, df | null, x0, {tol, maxIter, trace})` → `+ reason: 'flat' | 'domain' | 'diverged' |
  'max-iter'`; `numFindRoots(f, a, b, {samples = 1000})` → `[{x, kind: 'cross' | 'touch',
  multiplicity}]` (sign changes refined by Brent, poles and jumps rejected; touching roots from
  near-zero minima of |f|; multiplicity is an estimate with the right parity; a stretch where f is
  exactly 0 comes as `{x, kind: 'interval', from, to}`).
- Optimisation: `numGoldenMin(f, a, b, {tol, trace})` → `{x, fx, iterations}`; `numExtrema(f, a, b,
  {samples = 400})` → `[{x, y, kind: 'min' | 'max'}]` (interior, kinks included).
- Calculus: `numDerivative(f, x, {order = 1..4, h, info})` (central differences + Ridders–Richardson;
  shrinks the step near a domain edge); `numIntegrate(f, a, b, {tol = 1e-10, maxIntervals, info})`
  — adaptive Gauss–Kronrod 7–15; a singular end (`1/√x`, `ln x`, `x^−0.9` on [0, 1]) goes to
  tanh-sinh first; ±Infinity limits by substitution; `info` → `{value, error, method, evaluations,
  intervals}`. Accuracy near a singular end is limited by how f is written: `1/√(1 − x²)` near ±1
  loses ~1e-8 because `1 − x·x` cancels. **The bare number is never checked for divergence**
  (∫₁^∞ dx/x gives ≈ 37): use `numIntegrateInfo(f, a, b, opts)` (= `numIntegrate` with `{info: true,
  check: true}`) → `{value, error, ok, divergent, reason, msg: {ru, en}, at?, estimate, method, evaluations,
  intervals}`. `reason` (null when ok): `'tail'` (an infinite limit and f decays too slowly or oscillates
  without decaying: ∫₁^∞ dx/x, ∫₀^∞ sin x dx), `'pole'` (non-integrable blow-up at `at`: ∫₀² dx/(x² − 1),
  ∫₀¹ dx/x, tg on [0, 3]), `'domain'` (f undefined on part of the interval: √(1 − x) on [0, 2]),
  `'oscillating'` (a tail that may converge only conditionally: ∫₀^∞ sin x/x — the number is unreliable),
  `'inaccurate'` (the error estimate is over max(1000·tol, 1e-6·|value|)), `'nan'`. For divergent integrals
  `value` is ±Infinity when the sign is clear, else NaN; `estimate` keeps the raw quadrature number. An
  integrable singularity inside (1/√|x − 1| on [0, 2]) is split off and integrated from both sides. How:
  |f| (after the substitution for infinite limits) is scanned on 1024 points, peaks are located, and the
  growth |f(c ± δ)| ~ δ^(−p) is measured for δ = 10⁻⁴…10⁻¹² of the interval (p ≥ 1 is not integrable; an
  oscillating envelope needs p ≥ 2 at a mapped infinite end); ~3000 extra evaluations. `numRiemann(f, a, b, n, 'left' | 'right' | 'mid' |
  'trapezoid' | 'simpson')` → `{value, n, method, pieces: [{x0, x1, h, …}]}` (trapezoids add y0, y1;
  Simpson pieces add xm, y0, ym, y1; odd n is raised by one for Simpson).
- ODEs (y a number or an array): `numEuler(f, t0, y0, h, n)`, `numRk4(f, t0, y0, h, n)` →
  `{t: [], y: []}`; `numOdeAdaptive(f, t0, y0, t1, {rtol = 1e-6, atol = 1e-9, h, hMax, maxSteps,
  samples})` — Dormand–Prince 5(4), either direction; `samples` → evenly spaced output (cubic
  Hermite) → `{t, y, steps, rejected, ok}`. Model right-hand sides: `odeSir(β, γ)` ([S, I, R]
  fractions), `odeLotkaVolterra(α, β, δ, γ)`, `odePendulum(g = 9.81, L = 1, damping = 0)` ([θ, ω]),
  `odeLorenz(σ = 10, ρ = 28, β = 8/3)`.
- Plots: `sampleFunction(f, x0, x1, {n = 400, yRange, maxDepth = 8, tol = 1e-3, maxPoints})` →
  array of polylines `[[x, y], …]`, refined where the curve bends, split at jumps (bisection probe:
  a jump survives refinement, a steep continuous piece does not), poles, domain edges (walked to
  ~1e-12) and NaN/±∞/exceptions. With `yRange` the y values are clamped to two view heights
  around the view and invisible pieces are not refined.
- Signals: `numDft(re, im?, {inverse})` (O(N²), exact length), `numFft(re, im?, {inverse})`
  (radix 2, zero-padded), `numIfft(re, im)` → `{re, im}` Float64Arrays;
  `numFourierCoefficients(f, N, period = 2π, {from = −T/2, samples})` → `{a: [a0…aN], b: [0, b1…bN],
  period, mean}` with f ≈ a0/2 + Σ(aₖcos kωx + bₖ sin kωx); `numFourierEval(coefs, x, n?)`.
- Statistics: `statMean, statMedian, statMode` (all modes ascending; `[]` when every value is
  equally frequent), `statVariance(xs, 'population' | 'sample')` (population ÷ n by default; also
  `{sample: true}`), `statStd`, `statQuantile(xs, p)` (R type 7 / Excel PERCENTILE.INC),
  `statCorrelation(xs, ys)`, `statLinearRegression(points)` → `{a, b, r, r2, slope, intercept}` for
  y = a·x + b, `statPolyFit(points, degree)` → `{coefs (ascending), r2}` (QR on scaled x). Points:
  `[[x, y]]` or `[{x, y}]`.
- Probability: `probErf, probErfc` (series / continued fraction, ~1e-16, accurate tails),
  `probNormalPdf, probNormalCdf(x, μ = 0, σ = 1), probNormalInv(p, μ, σ)` (Acklam + 2 Halley steps),
  `probChoose(n, k), probFactorial(n), probArrangements(n, k)` (exact BigInt),
  `probBinomialPmf(k, n, p), probBinomialCdf` (exact for n ≤ 60, Loader's saddle point above;
  CDF by summation to n = 1000, incomplete beta above), `probPoissonPmf, probPoissonCdf`,
  `probGeometricPmf(k, p), probGeometricCdf` (k = number of the trial with the first success, k ≥ 1),
  `probStudentTCdf(t, df), probStudentTInv(p, df)` (critical values for confidence intervals),
  `probChiSquareCdf(x, k)`, `probBetaRegularized(x, a, b)`, `probGammaRegularized(a, x)`,
  `numGamma(x)`, `numLogGamma(x)`.
- Interpolation and polynomials: `numLinspace(a, b, n)`, `numLagrange(points)` → `{fn, coefs}`
  (barycentric evaluation, monomial coefficients ascending), `numPolyRoots(coefs ascending)` →
  `[{re, im}]` (Aberth–Ehrlich, multiple roots polished as clusters, sorted by re then im).

## matrix.js — exact matrices over Q (+ a float toolkit)

`class Matrix` (entries are Q): `Matrix.from([[1, 2], ['1/2', 3]])` (numbers, strings, BigInt, Q;
a flat array is a column), `Matrix.identity(n)`, `Matrix.zeros(r, c)`, `Matrix.fromColumns(cols)`,
`Matrix.diag(values)`; fields `rows, cols`; `get(i, j)`, `set(i, j, v)` (returns a new matrix — all
methods are immutable), `row(i)`, `col(j)`, `add, sub, mul` (matrix, vector → Q[], or scalar),
`scale, neg, transpose, equals, isSquare, isZero, isSymmetric, trace, pow(n), augment(B), minor(i, j),
toArray()` (Q[][]), `toNumbers(), toStrings(), toString(),
toTex({augmented: k, env: 'pmatrix' | 'vmatrix' | 'bmatrix', boxed: [[i, j]]})` — `augmented`
draws `\left(\begin{array}{cc|c} … \end{array}\right)`.

- `matRref(A, {steps, augmented: k})` → `{matrix, pivots, rank, ops: [{op, i, j, k, phase}], steps?}`.
  One step per elementary operation: `{op: 'swap' | 'scale' | 'add', i, j, k (Q), phase:
  'forward' | 'backward', opTex: 'R_{2} \to R_{2} - 3\,R_{1}', matrixTex (after), tex:
  '\xrightarrow{R_{2} - 3\,R_{1}} …', text}` («Обнуляем элемент под ведущим: из второй строки
  вычитаем первую, умноженную на 3»). Pivot strategy: 1, then −1, then an entry that divides its
  whole row, else the smallest |entry|; ties keep the current row. Pivots are made 1, then
  forward elimination, then backward.
- `matRank(A)`, `matNullspace(A, {integer = true})` → Q[][] (primitive integer vectors).
- `matDet(A, {steps, method: 'gauss' | 'cofactor' | 'sarrus'})` — default: 2×2 formula, 3×3 Sarrus,
  4×4+ Gauss (swaps flip the sign); cofactor expansion along the line with most zeros, minors as
  sub-steps (up to 6×6).
- `matInverse(A, {steps})` → Matrix or null (Gauss–Jordan on [A | E]; the 2×2 formula shown too;
  singular → explained, rank < n).
- `matSolve(A, b, {steps, vars})` → `{kind: 'unique' | 'none' | 'infinite', x, params: [{name, index}],
  basis, rank, rankAug, tex, vectorTex?}`; every solution is x + Σ paramₖ·basisₖ (parameters t, s, u…).
  `matSolveCramer(A, b, {steps})` (n ≤ 3 with steps) → `{kind: 'unique' | 'singular', x, dets}`.
- `matCharPoly(A, {steps})` → Poly of det(A − λE) (RU convention; −λ³ + … for 3×3). Steps write out
  the determinant for 2×2 and 3×3 (first-row expansion), Faddeev–LeVerrier beyond; `{steps}` also
  returns `coefs` (Q[], ascending) and `tex`.
- `matEigen(A, {steps})` → `{charPoly, coefs, values}`; each value has `re, im, multiplicity, tex,
  approx` and `kind`: `'rational'` (`value: Q, vectors` — exact eigenspace basis, `geometric`),
  `'quadratic'` (`exact: {p, q, s, sign}` = p ± q√s, s < 0 complex; `tex` like
  `\frac{1 + \sqrt{5}}{2}`, `1 - \sqrt{2}\,i`; `vectorsApprox` for real simple ones) — quadratic
  factors of higher-degree remainders are found over Z — or `'approx'` (numeric roots of an
  irreducible factor of degree ≥ 3, `tex` = `{ru: '\approx 1{,}259921', en: …}`).
- `matDiagonalize(A, {steps})` → `{diagonalizable: true, P, D, Pinv}` or `{diagonalizable: false,
  reason: 'defective' | 'irrational', overReals?, overComplex?}` (exact over Q only).
- `matPower(A, n)` (square-and-multiply; n < 0 via the inverse), `matGramSchmidt(vectors, {steps})`
  → `{orthogonal (exact, unnormalised), normalized (floats), dropped}`, `matProjection(v, u | [u…])`
  → Q[], `matLeastSquares(A, b, {steps})` → normal equations AᵀA·x = Aᵀb solved exactly, + `residual`.
- Float toolkit (number[][]): `fmatMul(A, B | v)`, `fmatTranspose`, `fmatSolve(A, b)` (null if
  singular), `fmatInv`, `fmatEigSym(S)` → `{values (descending), vectors}` (Jacobi),
  `fmatSvd(A)` → `{U, S, V}` thin (one-sided Jacobi; 200×200 ≈ 0.2 s), `fmatSvdTruncated(A, k,
  {oversample = 10, powerIters = 2, seed})` (randomised; top-20 of 200×200 ≈ 15 ms — for image
  compression), `fmatLowRank(svd, k)` → U·diag(S)·Vᵀ, `fmatQr(A)` → `{Q, R}` thin Householder.

## solve.js — equations, inequalities, systems

Tests: `node --test tests/Js/math-engine-solve.test.cjs`. Everything returns school-style steps in
the steps.js shape (RU default, EN alongside); the last step is `{title: 'Ответ', final: true}`.
`opts.steps: false` returns `steps: []`. Input is text (read by `parse`) or a node.

**`solveEquation(input, v = 'x', {steps, domain: 'real' | 'complex', interval, lang})`** — an
expression means `= 0`; if `v` is absent and there is exactly one letter, that letter is used.
Result `{kind, roots, steps, check, answer: {tex, text}, type, odz?, extraneous?, v, …}`:

- `kind`: `'roots'` · `'none'` · `'all'` (identity; `set` = where it holds, ОДЗ applied) · `'set'`
  (whole intervals, e.g. `|x−1| + |x+2| = 3` → `[−2; 1]`) · `'unsupported'` (+ `reason: {ru, en}`).
- `roots: [{node, approx, mult, approxOnly?, family?}]` ascending, distinct; `approx` is a number
  (or `{re, im}` in the complex domain); `approxOnly` marks numeric roots (TeX `x \approx 1{,}1673`); their
  `node` is a short decimal (`num` with `raw`, prints `2{,}09455`), and checks substitute 4-decimal values
  (`(2{,}0946)^{3} - 2 \cdot 2{,}0946 - 5 \approx 0\ \checkmark`), never 16-digit fractions.
- `check: [{root, ok, reason, tex, text}]` — every candidate is substituted into the *original*
  equation (exactly when simplify/expand can, else to 1e-8 relative to the size of the terms, plus the
  rounding spread of the sides near the root — tg(arctg 10¹⁰) passes) and tested against the ОДЗ.
  `extraneous: [{node, approx, reason: 'odz' | 'undefined' | 'mismatch' | 'sign' | 'pole'}]` lists
  what was dropped (`sign`: e.g. √f = g with g < 0; `pole`: a zero of a denominator).
- `odz: {tex, text, set, conditions}` — from denominators, even roots, logarithms (argument > 0,
  base > 0, ≠ 1), tg/ctg (cos/sin ≠ 0), arcsin/arccos, powers with a variable exponent; `set` is an
  IntervalSet when all conditions are rational, `null` otherwise.
- `type`: `linear` · `quadratic` · `polynomial` · `rational` · `product` · `abs` · `radical` ·
  `exponential` · `logarithmic` · `trig` · `identity` · `numeric`.
- Real domain: `complexRoots` holds the non-real roots of polynomial equations as an aside
  (quadratics exact: `-1 \pm 2i`); `domain: 'complex'` makes them roots. Complex coefficients (with i) are
  solved in the complex domain for linear and quadratic equations: (1+i)z = 3−i → 1 − 2i, z² = 3+4i →
  ±(2 + i) (√D exactly when it is a Gaussian rational); in the real domain such a linear root is reported
  in `complexRoots` with `kind: 'none'`.
- Numeric fallback: `numeric: true, range: [a, b], rangeTex` ([−10; 10], widened to [−100; 100]
  when nothing is found; [−2π; 2π] for trigonometric ones); if no root is found the result is
  `unsupported` (never a false "no roots").

Classes and methods (steps say what we do and why):
- linear: clear fractions (LCD shown), expand, move terms, divide; `0·x = b` cases;
- quadratic: coefficients, D = b² − 4ac written out, simplified surds (`(3 ± √13)/2`, √D reduced,
  fraction cancelled), incomplete forms without D, Vieta check for rational roots, complex aside;
- degree ≥ 3: xᵏ out of brackets, xⁿ = c, trinomials t = xᵐ (biquadratic), reciprocal quartics
  (t = x + 1/x), grouping, rational root theorem (candidate list) + Horner tables, factoring into
  quadratics, then numeric roots with a note on Cardano / Ferrari / Abel–Ruffini; multiplicities;
- product = 0: each factor, the rest checked against the ОДЗ;
- rational: common denominator (true LCD, factored), numerator = 0, pole roots dropped;
- absolute value: |f| = c, |f| = g(x) (g ≥ 0 and f = ±g), |f| = |g|, several moduli by intervals;
- radical: isolate, raise to the power (condition g ≥ 0 for even roots, explained), repeat for two
  radicals, odd roots are equivalent; every root checked;
- exponential: a^f = a^g, a^f = b (exact power or log_a b), common base (4ˣ = 8 ⇒ 2^{2x} = 2³),
  aᶠ·bᶠ = (ab)ᶠ, substitution t = aᵐˣ (t > 0) for polynomials in aˣ, a^f = b^g by logarithms, a common
  exponential factor divided out (x²·2ˣ = 4·2ˣ ⇒ 2ˣ(x² − 4) = 0, 2ˣ > 0);
- logarithmic: log_a f = b, log_a f = log_a g, sums/differences/multiples combined (bases a^k
  converted), t = log_a u for polynomials in log, variable base log_f g = c; ОДЗ check; the unknown in both
  the base and the exponent: take the logarithm of both sides (x^(lg x) = 100x ⇒ lg²x = lg x + 2 ⇒ 1/10, 100;
  lg by default, ln / log_a when the equation uses them);
- trigonometric (`solveTrig` = the same, trig only): arguments shifted by a multiple of π/2 are reduced
  first, in a step of their own (`rule: 'reduction'`: `\sin\left(x + \frac{\pi}{2}\right) = \cos x`);
  sin/cos/tg/ctg of kx + b = a (table values
  exact, arcsin/arccos/arctg/arcctg otherwise, |a| > 1 → none, special cases 0, ±1), polynomial in
  one function (|t| ≤ 1 filter), sin² ↔ 1 − cos², homogeneous of degree 1–2 (÷ cosᵈ, common factors
  first), a·sin + b·cos = c (auxiliary angle), tg/ctg mixes, trig denominators (× cosᵏ), double
  angles (u and 2u), sum-to-product for sin a ± sin b, cos a ± cos b, equal functions of different
  arguments (tg A = ±tg B ⇒ A = ±B + πn; sin A = ±cos B ⇒ A = π/2 ∓ B + 2πn or …; tg A = ctg B ⇒
  A = π/2 − B + πn: tg 3x = tg x → πn after the ОДЗ, sin 3x = cos x → π/8 + πn/2, π/4 + πn), fractions with
  trig in the denominator (sin x/(1 − cos x) = 0: numerator = 0, the ОДЗ drops the rest → π + 2πn); a
  table-angle guess for arctg a etc. is kept only if F of it really is a (arctg 10¹⁰ is not π/2). Roots are families
  `{base, period, param: 'n'}` in `families`, `roots[k].family`; `answer.tex` RU:
  `x = (-1)^{n}\frac{\pi}{6} + \pi n,\ n \in \mathbb{Z}`, `x = \pm\frac{3\pi}{4} + 2\pi n`;
  EN: `x = \frac{\pi}{6} + 2\pi n,\quad x = \frac{5\pi}{6} + 2\pi n`. Families are merged (πn and
  π/2 + πn → πn/2), checked for n = −2…2 and filtered by the ОДЗ (split into sub-series when needed).
  `interval: '[0; 2pi]' | [a, b] | IntervalSet` → `inInterval` (exact roots in it, ЕГЭ part 2 style).

**`solveInequality(input, v = 'x', {steps})`** → `{set: IntervalSet | null, steps, signChart,
answer, type, odz?, approx?, reason?}`; a chain `a < f ≤ b` is split and intersected, `f ≠ g` is the
complement of the roots. Linear (sign flip when dividing by a negative), quadratic (parabola
reasoning), polynomial and rational by the method of intervals (factored; multiplicities — the sign
does not change at even ones; poles always excluded; isolated points: `(x−1)²(x+2) ≤ 0` →
`(-\infty;\,-2] \cup \{1\}`), |f| ≶ c and several moduli by intervals, a^f ≶ b / t = aˣ (base < 1
flips), log_a f ≶ c and log_a f ≶ log_a g with the ОДЗ, √f ≶ c. Denominators that cancel still
exclude their zeros. Irrational numeric bounds are decimals with `approx: true`.
`signChart = {points: [{x, tex, kind: 'zero' | 'pole', included, mult, approx}], signs: ['+', '-', …]}`
(signs.length = points.length + 1) — what the «метод интервалов» widget draws.

**Sets.** `class IntervalSet` — a union of intervals with open/closed ends, ±∞ and isolated points;
parts `{lo, hi, loC, hiC}` with ends `{node, x, q}` (exact node, double, Q or null) or null for ∞.
`IntervalSet.empty() / all() / interval(a, b, loClosed, hiClosed) / point(a) / points([…]) /
below(a, closed) / above(a, closed)`; `union, intersect, complement, minus, contains(x), equals,
isEmpty, isAll, isFinite, pointList, toTex(lang), toText(lang), toJSON()`.
`intervalTex(set, lang)` → `(-\infty;\,2] \cup (3;\,+\infty)` (RU `;`), `(-\infty,\ 2] \cup …` (EN),
`\{1;\,2\}`, `\varnothing`. `intervalText(set, lang)` → `(-∞; 2] ∪ (3; +∞)`.
`parseIntervalSet(text, lang = 'ru', v = 'x')` reads answers: `(-∞; 2] ∪ (3; +∞)`, `(-inf; 2] U …`,
`[1, 3)` (EN comma), `(1,5; 3]` (RU decimal comma), `{1; 2}`, `x < 2`, `-1 < x <= 3`,
`x < 2 или x > 3`, `x ≠ 1`, `∅`, `нет решений`, `R`, TeX with `\infty`, `\cup`; throws
`MathError('interval')`. `intervalEquals(a, b, lang)` compares sets or texts (false on bad input).

**`checkRoot(rel, v, value, {complex})`** → `{ok, defined, exact, reason, lhs, rhs, lhsApprox,
rhsApprox, tex, text, steps}`; works for inequalities too (`ok` = holds). TeX:
`\sqrt{-1 + 2} = 1 \,\ne\, -1`, `2^{2} = 4\ \checkmark`.

**Systems.** `solveLinearSystem(rels, vars?, {steps, method: 'substitution' | 'addition' |
'cramer' | 'gauss'})` — rels: array of texts/nodes or one text with `;`; vars default to the letters
(x, y, z, t, u, v, w first). Default: 2×2 → substitution when a coefficient is ±1, else addition;
otherwise Gauss via `matSolve` (every row operation also shows the system as equations). Cramer via
`matSolveCramer` (≤ 3×3; Δ = 0 → Gauss). → `{kind: 'unique' | 'none' | 'infinite' | 'unsupported',
solution?: {x: node}, general?: {x: node in params}, params?: ['t'] (2×2: the free unknown itself),
method, vars, steps, check, answer}`; answers `\left(x;\ y\right) = \left(2;\ 1\right)` (one unknown: `x = 2`);
`answer.text` is always `{ru, en}`.
`solveSystem2(rels, vars?)` — a linear and a non-linear equation: express an unknown from the linear
one, substitute, solve with `solveEquation`, back-substitute, check → `{kind: 'solutions' | 'none' |
'unsupported', solutions: [{x, y}] (sorted), steps, check, answer}`.

**Refusals** (`kind: 'unsupported'` with a reason): letters besides the unknown (parameters),
inequalities passed to `solveEquation` and vice versa, systems passed to `solveEquation`,
trigonometric equations with unrelated arguments or other structures (cubic in sin with mixed terms,
sin 3x + sin x + cos x = 0) and mixed algebraic–transcendental equations (they go to the
numeric fallback), trigonometric/radical inequalities other than √f ≶ c, non-linear systems other
than linear + one non-linear equation, `solveSystem2` whose one-variable equation has no exact roots.

<!-- Sections below: diff.js, integrate.js, limit.js (written by the calculus agent). -->

## Calculus: diff.js, integrate.js, limit.js

Tests: `node --test tests/Js/math-engine-calculus.test.cjs` (173 derivatives against central
differences, 205 antiderivatives differentiated back numerically, 29 definite integrals, 153 limits,
Taylor coefficients, step shapes). Inputs are nodes or strings (parsed); results are display nodes
(print them with `calcTex`), answers carry `tex` (string or `{ru, en}`), steps have the steps.js shape;
the final step has `rule: 'answer'` and `final: true`. Every result is checked numerically before it
is returned; nothing unchecked is ever shown as exact.

### diff.js — derivatives

- **`derivative(f, v = 'x', {steps, simplify = true, partial})`** → `{result, steps, verified, tex}`
  (`tex` = `f'(x) = …`). Rules: constant, variable, sum/difference, constant factor, n-ary product,
  quotient (and `c/v` → `−c·v′/v²`, `c/xᵏ` rewritten as `c·x⁻ᵏ`), power `xⁿ` for any rational or
  symbolic n, roots (`√`, `ⁿ√` as powers), `aᵘ`, `eᵘ`, `uᵛ` (logarithmic differentiation), ln, lg,
  logₐ (a variable base → change of base), sin … arcctg, sh/ch/th/cth and their inverses, sec/cosec,
  `|u|` (`u/|u|·u′`, u ≠ 0), sgn/floor/ceil (0 away from the jumps), other letters are constants.
  The chain rule names the inner function (`u = 3x + 1`). The step tree mirrors the expression as it
  was typed: every node shows `(…)' = rule form = assembled = clean`. `simplify: false` returns the
  assembled derivative. Throws `MathError` for relations/lists (`not-expr`) and `x!` (`unsupported`).
- **Clean form** (`niceForm(node, v, {fnFractions})`, also used for integrals and limits): canonical
  simplification plus candidates — expanded, one fraction (numerator expanded / common factor out /
  collected by functions / factored), rational function reduced by `Poly.gcd`, inner fractions
  combined (`arctg((1+x)/(1−x))′ = 1/(x²+1)`), polynomial factors absorbed into radicals
  (`(2−2x²)/√(1−x²) = 2√(1−x²)`), `x²/|x| = |x|`, the minus moved into a bracket, sin/cos → tg/ctg,
  logarithms of numbers merged (`½ln2 + ½ln3 − ½ln4 = ½ln(3/2)`); the shortest TeX wins and each
  candidate is checked at sample points. `prettyForm` is the display layer: `1 − x²` not `−x² + 1`,
  `x√x`, `∛(x²)`, `√((x²+1)³)`, `(x + 1)ln(x + 1)`, `ln|x|`, `(x+1)/2` in function arguments,
  `√3/3·arctg …`. `calcTex(node, lang)` / `calcTexBoth(node)` print through it with `toTex(…, {roots:
  true})`. The radical shapes and `\frac{\sqrt{3}}{3}\operatorname{arctg}` are now print.js's own (any
  canonical node prints them); prettyForm still builds them as nodes because its output also feeds the
  plain-text step lines (`toText`: `x*sqrt(x)`, `(2sqrt(3)/3)*arctg(x)`).
- `quickDerivative(node, v)` — canonical derivative without steps (fast; used for checks, L'Hôpital,
  Taylor). `ratFunctionOf(node, v)` → `{num: Poly, den: Poly}` reduced, or null.
- `partialDerivative(f, v)` (∂ notation), `derivativeN(f, v, n)` → `{result, list, steps, tex}`
  (`f'''(x)`, `f^{(4)}(x)`), `gradientOf(f, vars?)` → `{result: list, components, tex}`,
  `tangentLine(f, v, a)` → `{k, b, point, line, tex: 'y = 2x - 1', steps}` (throws `undefined` /
  `no-derivative`).

### integrate.js — integrals

- **`integrate(f, v = 'x', {steps})`** → `{result | null, method, steps, verified, reason?, tex}`
  (`tex` ends with `+ C`). The cascade on the canonical form, every step saying why it applies:
  constant → table (xⁿ, 1/x, aˣ, trig, 1/cos², sh/ch, 1/(1+x²), 1/√(1−x²), 1/√(x²±1), |x|, sec…) →
  linearity (constants out, sums split) → linear substitution `∫f(kx+b)dx = F(kx+b)/k` →
  `c·h′·hᵏ` (derivative of the denominator on top: `ln|h|`) → rational functions (division, factoring
  over Q, partial fractions by undetermined coefficients, linear and repeated linear factors,
  irreducible quadratics → ln + arctg with the square completed, `1/(x²−2)` over the reals,
  `(Bx+C)/(q)ᵏ` by the reduction formula) → cyclic parts `eᵃˣ·sin/cos bx` → trigonometric forms
  (odd power → t = cos/sin, even powers → double angle, non-positive even sum → t = tg, product to
  sum) → expand → u-substitution (candidates: function arguments, bases, exponents, denominators,
  roots; the ratio f/u′ must be a function of u, with back-substitution for u = a·xᵏ + b) →
  quadratics under a root (arcsin, «long logarithm», √(a²−x²), √(x²±a²)) → Pₙ(x)/√Q by undetermined
  coefficients (`∫Pₙ/√Q = Rₙ₋₁√Q + λ∫dx/√Q`) → t = ⁿ√(ax+b) → P(x)·eᵏˣ, P(x)·sin/cos kx of degree ≥ 3
  by parts n times (tabular) → by parts (LIATE: ln, inverse trig, then a polynomial next to eˣ,
  sin, cos, 1/cos²; repeated) → x = a·sin t / x = a·tg t for other functions of √(a² ∓ x²) (back
  through sin(k·arcsin u), …) → universal substitution t = tg(x/2).
  `method` names the method of the top step (`table`, `linear-substitution`, `substitution`,
  `parts`, `parts-cyclic`, `rational`, `trig-power`, `trig-substitution`, `trig-product`,
  `quadratic-root`, `radical-polynomial`, `trig-root-substitution`, `rationalizing`,
  `universal-substitution`, `linearity`, `constant`).
  Every candidate is verified: `F′ − f` expanded to exactly 0, or `F′ = f` at sample points of the
  domain; either way F must be defined where f is (`ln x` for `1/x` is rejected). The answer is
  tidied (`arctg(tg u) → u`, constant terms go to C, `ln|u|` only where u can be negative). Refusals: `result: null` with `reason` — a named
  non-elementary integral (`e^{±x²}` → erf, sin x/x → Si, cos x/x → Ci, eˣ/x → Ei, 1/ln x → li,
  sin x²/cos x² → Fresnel, xˣ) or «не удалось».
- **`integrateDefinite(f, v, a, b, {steps})`** (a, b: numbers, strings, nodes, `inf`, ±Infinity) →
  `{value: node | 'inf' | '-inf' | null, numeric, exact, approx, converges, improper, antiderivative,
  method, steps, tex}`. Newton–Leibniz with the interval split at points where f blows up (zeros of
  denominators and log arguments, poles of tg…) or where the antiderivative jumps (after t = tg(x/2));
  infinite and singular ends are one-sided limits of F (`limit`); an infinite limit → «расходится»
  (`∫₋₁¹ dx/x` and `∫₋₁¹ dx/x²` diverge). Exact values are cross-checked with `numIntegrate`.
  Otherwise a numeric value with `approx: true` and `≈` in `tex`; an improper integral is given
  numerically only if its partial integrals settle, else it is refused. Letters other than v → `unbound`.
- **`areaBetween(f, g, v, a?, b?, {steps})`** → `{value, numeric, exact, approx, points, pieces,
  steps, tex}`: ∫|f − g| split at the crossings (exact roots via Poly when possible); without bounds
  the outermost intersections are used.

### limit.js — limits and Taylor polynomials

- **`limit(f, v, a, {steps, side: 'both' | 'left' | 'right'})`**, a: node/number/string, `'inf'`,
  `'-inf'`, ±Infinity → `{value: node | 'inf' | '-inf' | 'dne' | null, method, steps, table:
  [{x, fx, side}], verified, approx?, sides?: {left, right}, tex}`. Direct substitution when f is
  defined and continuous at a (0⁰, ln 0, poles of tg are not «defined»); otherwise limit arithmetic
  with ±∞ and a bounded factor (sin x/x → 0 at ∞), c/0 with the sign of the side, and for the
  indeterminate forms (steps name the form): 0/0 — factor and cancel (rational), equivalent
  infinitesimals (sin, tg, arcsin, arctg, sh, th ~ u; 1 − cos u ~ u²/2; eᵘ − 1 ~ u; aᵘ − 1 ~ u ln a;
  ln(1+u) ~ u; (1+u)ᵃ − 1 ~ au; only for factors of a product/quotient), conjugate (square and cube
  roots), L'Hôpital (≤ 5 rounds; a ratio of derivatives without a limit proves nothing and is not
  used); ∞/∞ — degree comparison, leading terms of algebraic expressions (x → −∞ handled by
  x = −t), divide by the dominant term, term-by-term; ∞ − ∞ — common denominator, conjugate,
  dominant term out; 0·∞ → a quotient; 1^∞ — second remarkable limit `e^{lim (u−1)·v}`; 0⁰, ∞⁰ —
  `e^{lim v ln u}`. |u| and sgn u at u = 0 are unfolded by side. A two-sided limit whose sides differ
  is computed side by side (`sides`) → `'dne'`. The table has 6 points per side (x = a ± 10⁻ᵏ or
  ±10ᵏ); the answer is cross-checked against the numbers (a contradiction discards the symbolic
  answer). When no method works: `value: null`, `approx: number`, `tex` with `≈`.
- **`taylorPolynomial(f, v, a, n ≤ 20, {steps})`** → `{poly (ascending powers of v − a), coeffs
  (exact nodes f⁽ᵏ⁾(a)/k!, limits at removable points: sin x/x), terms, polyCanonical, tex, steps}`.
  **`taylorRemainderBound(f, v, a, n, x)`** → `{bound, M, tex}` (Lagrange form, M sampled on [a, x]).

### Known limits of the calculus modules

- Integrals: no Euler substitutions, no x = a/cos t for √(x² − a²)·R(x), no partial fractions with
  factors irreducible over Q of degree ≥ 3 or real-reducible quartics such as x⁴ + 1, none with
  symbolic coefficients, no reduction for (Bx+C)/qᵏ when q has real irrational roots, no hyperbolic
  power reduction; sh/ch only through the table and parts; x·tg x, √(sin x) and the like are refused.
  Answers are valid on each interval of the domain (C may differ between intervals, e.g. after
  t = tg(x/2) or for ln|x|).
- Derivatives of floor/ceil/sgn are 0 away from the jumps; nothing is said about non-differentiable
  points except |u| (u ≠ 0).
- Limits: equivalents are applied to factors only (never inside sums); sequences are handled as
  functions of a real variable (lim over n → ∞ of (1 + 1/n)ⁿ works; n!, (−1)ⁿ do not); oscillating
  functions without a factor tending to 0 give 'dne'; limits with parameters work symbolically but
  are not cross-checked numerically (`verified: false`).
- Definite integrals need numeric bounds and no other letters; numeric fallbacks are approximate.
