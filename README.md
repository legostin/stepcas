# stepcas

A computer algebra system that shows its work. Exact answers with school-style step-by-step solutions in
Russian and English, in plain JavaScript with no dependencies. Runs in the browser and in Node.

**[Try it in the browser](https://legostin.github.io/stepcas/)**: 15 kinds of tasks and 174 examples, from
quadratic equations to ODEs and matrices.

```js
import { solveEquation, localize } from 'stepcas';

const r = localize(solveEquation('x^2 - 5x + 6 = 0'), 'en');
r.answer.text;                    // "2, 3"
r.steps.map((s) => s.title);      // "A quadratic equation: read off the coefficients", "Compute the discriminant",
                                  // "$D > 0$: two roots", "Compute each root", "Check with Vieta’s formulas",
                                  // "Check by substitution", "Answer"
r.steps[1].tex;                   // "D = b^2 - 4ac = (-5)^{2} - 4 \cdot 1 \cdot 6 = 25 - 24 = 1"
```

It is the maths engine behind the course «Математика — царица наук» and the canvas calculator on
[legost.in](https://legost.in/utilities/math). Use it to build solvers, homework checkers, trainers and
generated tests that explain the answer as a teacher would on the board.

- [Install](#install)
- [Quick start](#quick-start)
- [Showing the solution](#showing-the-solution)
- [Languages](#languages)
- [What it can solve](#what-it-can-solve)
- [Calculators](#calculators)
- [Building blocks](#building-blocks)
- [Task generators](#task-generators)
- [What you can type](#what-you-can-type)
- [The bench](#the-bench)
- [Development](#development)

## Install

The package is not on npm yet. Install it from GitHub:

```sh
npm install github:legostin/stepcas
```

It is a set of ES modules (Node ≥ 20, any modern browser), with TypeScript types built on install.

In a page without a bundler, import it straight from a CDN:

```html
<script type="module">
  import { integrate, localize } from 'https://cdn.jsdelivr.net/gh/legostin/stepcas@main/src/index.js';
  console.log(localize(integrate('x cos x'), 'en').answer.text); // "x*sin(x) + cos(x) + C"
</script>
```

## Quick start

Every solver takes the task as text and returns a result of the same shape:

```js
import { solveInequality, localize } from 'stepcas';

const r = solveInequality('(x - 1)(x + 3)/(x - 5) >= 0');
r.ok;     // true
r.kind;   // "set": what sort of answer this is
r.type;   // "rational": which method solved it
r.set;    // IntervalSet, the answer as an object
r.answer; // {tex, text}: the answer to show and the answer as plain text
r.steps;  // the solution

localize(r, 'en').answer.text; // "[-3, 1] ∪ (5, +∞)"
localize(r, 'en').answer.tex;  // "x \in [-3,\ 1] \cup (5,\ +\infty)"
localize(r, 'ru').answer.tex;  // "x \in [-3;\,1] \cup (5;\,+\infty)"
```

Texts in a result are messages in every language at once. `localize(r, lang)` turns the whole result into
plain strings in one language. That is the easiest way to read it.

**When there is no answer**, `ok` is `false`. A solver never throws on what a person types:

```js
const bad = localize(solveEquation('2x + = 3'), 'en');
// {ok: false, kind: 'invalid', reason: 'An expression is missing before "="', pos: 5, len: 1, code: 'syntax', …}
```

`kind` is `'invalid'` when the input does not parse (`pos` and `len` point at the mistake, so you can underline
it) and `'unsupported'` when the engine cannot solve the task. The engine prefers refusing to guessing. When an
answer is only numeric, it says so: the answer text starts with `≈`.

Steps are on by default. Pass `{steps: false}` in the options when you only need the answer.

## Showing the solution

`r.steps` is a list of steps. After `localize`, each one looks like this:

```js
{
  title: 'Product rule',                   // what we do; may hold inline TeX between $…$
  tex: "\\left(x^{2}\\sin x\\right)' = …",  // the formula, in TeX (no $ around it)
  text: 'By the product rule: …',          // why; may hold inline TeX between $…$
  rule: 'product',                         // the rule's name, for programs
  sub: [ /* nested steps */ ],             // the details of this step, when it has any
  data: { /* facts for programs */ },      // a table, a row operation…
  final: true,                             // only on the answer step
}
```

Every field except `title` may be missing. Here is a renderer with [KaTeX](https://katex.org):

```js
import katex from 'katex';
import { derivative, localize } from 'stepcas';

const escape = (s) => s.replace(/[&<>"]/g, (c) => `&#${c.charCodeAt(0)};`);
const tex = (s, displayMode) => katex.renderToString(s, { displayMode, throwOnError: false });
// "text with $inline$ maths": odd pieces are TeX
const inline = (s) => s.split(/\$([^$]+)\$/).map((p, i) => (i % 2 ? tex(p, false) : escape(p))).join('');

function renderSteps(steps) {
  return '<ol>' + steps.map((s) => `<li><b>${inline(s.title)}</b>
    ${s.tex ? tex(s.tex, true) : ''}
    ${s.text ? `<p>${inline(s.text)}</p>` : ''}
    ${s.sub ? renderSteps(s.sub) : ''}</li>`).join('') + '</ol>';
}

const r = localize(derivative('x^2 sin x'), 'en');
document.body.innerHTML = renderSteps(r.steps);
```

The derivative above comes out as three steps: «What we differentiate», «Product rule» (with «Power rule» and
«Table derivative» nested inside it) and «Answer».

## Languages

Russian and English are built in. Russian is the default, with its school notation: tg, ctg, lg, a decimal comma,
`;` between items. English writes tan, cot, `\log_{10}`, `2.5` and `,`.

```js
localize(r, 'ru');                 // the whole result in Russian
r.steps[0].title.en;               // one message in English
r.steps[0].title.in('ru');         // the same, by code
```

A new language is one catalog and one call, with no change to the code. Keys you leave out come from the base
language:

```js
import { registerLanguage } from 'stepcas';
registerLanguage('kk', catalog, { base: 'ru' });
```

The catalogs are in [src/i18n/](src/i18n/). Each one is a set of files, one file per domain.

## What it can solve

All examples are real output, after `localize(r, 'en')`.

### Equations and inequalities

| Call | `answer.text` |
|---|---|
| `solveEquation('log_2(x + 3) = 5')` | `29` |
| `solveEquation('sqrt(x + 7) = x - 5')` | `9` (the extraneous root 2 is shown and dropped) |
| `solveEquation('\|2x - 3\| = 5')` | `-1, 4` |
| `solveEquation('x^2 + 1 = 0')` | `No roots.` |
| `solveEquation('x^2 + 1 = 0', 'x', {domain: 'complex'})` | `-i, i` |
| `solveTrig('2sin^2 x - sin x - 1 = 0')` | families of roots with `n ∈ Z` |
| `solveTrig('2cos^2 x - 3cos x + 1 = 0', 'x', {interval: '[0; 2pi]'})` | the families, and `r.inInterval`: 0, π/3, 5π/3, 2π |
| `solveInequality('log_(1/2)(x - 1) > -2')` | `(1, 5)` |
| `checkRoot('sqrt(x + 7) = x - 5', 'x', 2)` | `kind: 'not-root'`, «an extraneous root» |

Equations: linear, quadratic, rational, radical, exponential, logarithmic, with |x|, trigonometric. The steps
find the domain and drop extraneous roots. Inequalities are solved by the method of intervals, also the
generalised one.

### Systems and parameters

| Call | `answer.text` |
|---|---|
| `solveLinearSystem('x + y = 3; x - y = 1')` | `(2, 1)` |
| `solveLinearSystem(['x + y + z = 6', '2x - y + z = 3', 'x + 2y - z = 2'], null, {method: 'gauss'})` | `(1, 2, 3)` |
| `solveSystem2('x + y = 5; x y = 6')` | `(2, 3), (3, 2)` |
| `solveWithParameter({task: 'x^3 - 3x = a', want: 3})` | `(-2, 2)` (the graphical way) |
| `solveWithParameter('x^2 - 2a x + a + 6 = 0', {want: 'two-roots'})` | `(-∞, -2) ∪ (3, +∞)` (the discriminant) |

`method` for linear systems is `'substitution'`, `'addition'`, `'cramer'` or `'gauss'`. `want` is
`'two-roots'`, `'one-root'`, `'no-roots'`, `'has-roots'` or a number of roots.

### Calculus

| Call | `answer.text` |
|---|---|
| `derivative('ln(cos x)')` | `-tan(x)` |
| `derivativeN('x e^x', 'x', 3)` | `e^x*(x + 3)` |
| `partialDerivative('x^2 y + y^3', 'y')` | `x^2 + 3y^2` |
| `gradientOf('x^2 y + y^3')` | `(2x*y, x^2 + 3y^2)` |
| `tangentLine('x^3', 'x', 1)` | `3x - 2` |
| `integrate('x cos x')` | `x*sin(x) + cos(x) + C` (by parts) |
| `integrate('x e^(x^2)')` | `e^(x^2)/2 + C` (substitution) |
| `integrateDefinite('1/x^2', 'x', 1, 'inf')` | `1` |
| `integrateDefinite('1/x', 'x', 1, 'inf')` | `diverges` |
| `areaBetween('x', 'x^2', 'x', 0, 1)` | `1/6` |
| `limit('sin(3x)/x', 'x', 0)` | `3` |
| `limit('(1 + 1/x)^x', 'x', 'inf')` | `e` |
| `limit('1/x', 'x', 0, {side: 'right'})` | `+∞` |
| `taylorPolynomial('e^x', 'x', 0, 4)` | `1 + x + x^2/2 + x^3/6 + x^4/24` |
| `extremeOnSegment('x^3 - 3x', 'x', 0, 2, {kind: 'min'})` | `-2` (at x = 1) |
| `extremePoints('x^3 - 3x')` | `max: -1; min: 1` |

Integrals use the table, substitution, parts, partial fractions and trigonometric forms. `r.method` names the
method. Limits use L'Hôpital's rule, equivalents and Taylor series.

### Differential equations and series

| Call | `answer.text` |
|---|---|
| `solveOde("y'' + y = x; y(0) = 0; y'(0) = 0")` | `x - sin(x)` |
| `solveOde("y' = 2xy")` | `C*e^(x^2)` |
| `sumSeries('sum(1/(k(k + 1)), k, 1, inf)')` | `1` (telescoping) |
| `sumSeries('sum(1/2^k, k, 0, inf)')` | `2` |
| `sumSeries('sum(1/k, k, 1, inf)')` | `diverges` |

ODEs: separable, linear and homogeneous first-order equations, and second-order equations with constant
coefficients. Right-hand sides are solved by undetermined coefficients or by variation of parameters. Initial
conditions go after `;`.

### Values and transformations

| Call | `answer.text` |
|---|---|
| `evaluateSteps('36^(log_6(5))')` | `25` |
| `evaluateSteps('log_2(12) - log_2(3)')` | `2` |
| `factorSteps('x^3 - 8')` | `(x - 2)*(x^2 + 2x + 4)` |
| `factorSteps('2x^2 - 7x + 3')` | `(2x - 1)*(x - 3)` |
| `expandSteps('(2x - 3)^2')` | `4x^2 - 12x + 9` |
| `simplifySteps('(x^2 - 4)/(x^2 + 4x + 4)')` | `(x - 2)/(x + 2)` (with the excluded value x ≠ -2) |

`evaluateSteps` computes a value the way a school solution does, with one named rule per step: logarithms,
powers, roots, reduction formulas.

Each solver's `kind` values are listed in [docs/API.md](docs/API.md#api--the-contract-solver-by-solver).

## Calculators

Number theory (`nt*`), numeric methods (`num*`) and exact linear algebra (`mat*`) return a bare value. With
`{steps: true}` they return `{value, steps}` too.

```js
import { ntGcd, ntFactor, ntFactorTex, ntCrt, ntToBase, ntBestApprox, matInverse, matSolve } from 'stepcas';

ntGcd(252, 198);                        // 18n
ntGcd(252, 198, { steps: true }).steps; // Euclid's algorithm, one division per step
ntFactorTex(ntFactor(360));             // "2^{3} \cdot 3^{2} \cdot 5"
ntCrt([2, 3, 2], [3, 5, 7]);            // {solvable: true, x: 23n, m: 105n}
ntToBase(0.1, 2);                       // "0.0(0011)"
ntBestApprox(Math.PI, 1000);            // {p: 355n, q: 113n}
matInverse([[2, 1], [1, 3]]).toString(); // "[[3/5, -1/5], [-1/5, 2/5]]"
matSolve([[1, 1], [1, -1]], [3, 1]);     // {kind: 'unique', x: [2, 1], …}
```

These also include primality tests, Miller–Rabin, φ(n), congruences, RSA keys, continued fractions, Egyptian
fractions, determinants (Gauss, cofactors, Sarrus), rank, eigenvalues, diagonalisation and Gram–Schmidt. Numbers
are exact: BigInt and rationals over BigInt.

## Building blocks

The solvers are built from parts you can use directly:

```js
import { parse, tryParse, toTex, toText, simplify, expand, equivalent, compile } from 'stepcas';

toTex(parse('x²−5x+6=0'));                    // "x^{2} - 5x + 6 = 0"
toTex(simplify(parse('sqrt(8)/2 + sin(pi/6)'))); // "\frac{1}{2} + \sqrt{2}"
toText(expand(parse('(2x-3)^2')));            // "4x^2 - 12x + 9"
equivalent('ln(x^2)', '2ln|x|');              // true: check a student's answer
toTex(parse('tg x'), { lang: 'en' });         // "\tan x"
compile(parse('x^3 - x'))(2);                 // 6: a fast function for plots
tryParse('sqr(x)').error.msg.en;              // '"sqr" is not supported here'
```

Expressions are frozen plain objects (`{type: 'add', args: […]}`). Never change them, build new ones.
[docs/API.md](docs/API.md) describes every function.

## Task generators

28 families of exam-style tasks. Each task is built backwards from its answer, so the answer is always right
and nice. The same seed always gives the same task.

```js
import { TASK_KINDS, generateTask, generateSet, localize } from 'stepcas';

TASK_KINDS; // linear-eq, quadratic-eq, exp-eq, log-eq, radical-eq, quad-ineq, rat-ineq, log-value, …

localize(generateTask('quadratic-eq', { seed: 42, level: 2 }), 'en');
// {family: 'quadratic-eq', level: 2, seed: 42, op: 'solve', task: '-x^2 - 8x = 12',
//  answer: {roots: [-6, -2]}, prompt: 'Solve the equation'}

generateSet('linear-eq', { count: 10, seed: 1, level: 1 }); // ten different tasks
```

Level 1 uses small integers, level 2 wider ranges and the usual traps, level 3 fractions. Pass `task` to a
solver to get the solution, or compare a student's answer with `equivalent`.

## What you can type

The parser reads maths the way people type it:

- `2x`, `x y`, `2(x+1)`, `x²`, `√x`, `∛x`, `|x|`, `π`, `∞`, `≤ ≥ ≠`, a decimal comma `3,5`;
- functions with or without brackets: `sin x`, `sin^2 x`, `tg x`, `arctg x`, `lg x`, `log_2 x`, `log_(a+1)(x)`;
- a bit of LaTeX: `\frac{a}{b}`, `\sqrt{x}`, `\cdot`, `\le`;
- Cyrillic look-alikes (`х`, `у`, `а`) are read as Latin letters;
- systems with `;` or one equation per line, a double inequality `-1 < x <= 2`.

Some readings to know: `1/2x` is (1/2)·x, `sin x^2` is sin(x²), `log x` is log base 10, and `e^2x` is e²·x (write
`e^(2x)`). Mistakes get a message and a position: `abc(x)` gets «Did you mean "abs"?». The full grammar is in
[docs/API.md](docs/API.md#coreparsejs).

## The bench

`bench/` runs the engine against real exam tasks: ЕГЭ (profile and base levels), ОГЭ, ЕНТ (Kazakhstan) and a
first-year university course, plus generated tasks. Every expected answer is checked independently with SymPy
(`bench/verify.py`). Where SymPy itself errs, numeric substitution checks decide. The current scoreboard is
[bench/REPORT.md](bench/REPORT.md):

| | tasks | solved | wrong | with steps |
|---|---:|---:|---:|---:|
| ЕГЭ, профиль | 212 | 100% | 0 | 100% |
| ЕГЭ, база | 20 | 100% | 0 | 100% |
| ОГЭ | 54 | 100% | 0 | 100% |
| ЕНТ | 67 | 100% | 0 | 100% |
| First-year course | 190 | 100% | 0 | 100% |
| Generated | 1008 | 100% | 0 | 100% |

A wrong answer counts against the engine. A refusal only counts as unsolved. New methods check their answers by
substituting them back.

## Development

```sh
git clone https://github.com/legostin/stepcas && cd stepcas && npm install
npm run check            # lint, formatting, tests (architecture, i18n and the result contract included),
                         # types and the golden fingerprints: run it before every commit
npm run bench            # the corpus → bench/REPORT.md (--strict fails on a wrong answer)
npm run snapshot:verify  # every answer and step against bench/golden.json
npm run snapshot:update  # after an intended change of output; commit golden.json with it
node bench/gen.mjs       # rebuild the generated part from fixed seeds
npm run bench:verify     # recheck the expected answers with SymPy (needs bench/.venv with sympy)
python3 -m http.server   # then open http://localhost:8000/demo/ for the demo page
```

The demo lives in [demo/](demo/). Its examples are in `demo/examples.js`, and a test runs every one of them.
Each push to `main` publishes the demo to GitHub Pages.

The engine is built in layers, from messages and core expressions up to the solvers, with no import cycles. A
test enforces this. [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) describes the layers, the result contract, the
step model and how to add a method or a language.

## License

MIT © 2026 legostin
