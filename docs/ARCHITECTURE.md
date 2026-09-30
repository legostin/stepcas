# stepcas architecture

How the engine is built: its layers and the rules between them, what a result and a step are, how languages are
kept out of the code, how recursion works without import cycles, and how everything is tested. The rules on this
page are checked by tests, not by memory. `test/architecture.test.cjs`, `test/i18n.test.cjs` and
`test/contract.test.cjs` fail when code breaks them.

## Principles

- **Exact first.** Numbers are `Q` (BigInt rationals) and expressions are immutable trees. Floating point is used
  in three places only: to check an answer, to locate roots before they are confirmed exactly, and as a numeric
  fallback. A numeric answer is always marked as approximate.
- **Nothing unchecked is shown as exact.** Every solver substitutes, differentiates back or compares with the
  numbers before it answers. When the check fails, the solver refuses.
- **Show the work.** Every answer comes with steps that name what is done and why, the way a teacher writes it on
  the board.
- **No language in the code.** The code names messages by key. The words live in catalogs, one per language, and
  are rendered when someone reads them.
- **One way to do a thing.** One step constructor, one result contract, one home for each helper.
- **Zero runtime dependencies.** Pure ES modules with no DOM. The engine runs in browsers and in Node ≥ 20.

## Layers

A *unit* is a directory of `src/` (`solve`, `numbers/theory`, `calculus/limit`, …) or a top-level file
(`api.js`, `index.js`). Units form layers, lowest first:

| Layer | Units | What they hold |
|---|---|---|
| 0 | `i18n` | messages, catalogs of every language, notation (tg or tan, 2,5 or 2.5) |
| 1 | `core` | `Q`, the AST, parse, print, simplify, expand, fractions, polynomials, equivalence, evaluation, steps |
| 2 | `numbers/theory`, `numbers/numeric` | calculators over integers (BigInt) and floats |
| 3 | `linalg` | matrices over Q, the float toolkit |
| 4 | `algebra` | values of expressions and transformations step by step |
| 5 | `solve` | equations, inequalities, systems, sets of answers |
| 6 | `calculus/display` | what every calculus module shares: constants, `simp`, the display form and TeX |
| 7 | `calculus/derivative` | derivatives with a step tree that mirrors the expression |
| 8 | `calculus/limit` | limits: limit arithmetic, indeterminate forms, Taylor polynomials |
| 9 | `calculus/integral`, `calculus/series` | antiderivatives, definite integrals, sums of series |
| 10 | `calculus/extrema`, `calculus/ode` | greatest and least values, differential equations |
| 11 | `problems`, `generate` | composite school tasks (a parameter, ЕГЭ №18), task generators |
| 12 | `api` | the public contract of the solvers |
| 13 | `index` | the package |

The rules, all checked on the import graph by `test/architecture.test.cjs`:

1. A module imports only its own unit and lower layers. Units of one layer do not import each other.
2. There are no import cycles at all, not even between two files of one unit.
3. A module enters another unit through that unit's `index.js`, when the unit has one.
4. Only the package index imports `api.js`, and nothing imports the package index.
5. A module takes its messages from its own catalog domain: `msg('solve.trig.…')` belongs in `src/solve/`.

A new unit gets a row in the `LAYERS` table of the test. Until then the test fails.

### Recursion without import cycles

Solvers are recursive. An equation method makes smaller equations, an integration method makes smaller
integrals, and resolving an indeterminate form needs more limits. The dispatcher calls the methods, so a method
must not import the dispatcher back. The dispatcher hands itself down through the context it already passes:

| Unit | Dispatcher | A method calls |
|---|---|---|
| `solve` | `solveCore(lhs, rhs, ctx)` | `ctx.solve(lhs, rhs)`, one level deeper |
| `calculus/integral` | `I(f, ctx)` in `engine.js` | `ctx.integrate(g, overrides?)`, e.g. `{v: 't'}` after a substitution |
| `calculus/limit` | `ev(n, C)` in `evaluator.js` | `C.ev(n, C)`, with `C` from `limitContext(v, P)` |

Helpers shared by the methods live in a leaf module of the unit (`solve/common.js`, `integral/common.js`,
`limit/common.js`) that imports no method and not the dispatcher.

## Results

Callers from outside use the solvers through `api.js`, and every solver there returns one shape:

```js
const r = solveEquation('x^2 = 4');
r.ok        // true when there is an answer
r.kind      // what the answer is: 'roots', 'none', 'all', 'set', 'value', 'antiderivative', 'expression', …
            // or 'invalid' (the input does not parse) or 'unsupported' (the solver cannot do it yet)
r.answer    // {tex, text} when ok: messages or {lang: string} values
r.reason    // why there is no answer (a message); r.pos and r.len point into the input for an input error
r.steps     // the explanation, built unless the options say {steps: false}
            // …and the solver's own fields: roots, set, value, result, method, …
```

The API layer never throws on what a person types: a parse error comes back as `{ok: false, kind: 'invalid'}`.
A thrown error is a bug. Inside the engine the modules call each other directly, and there errors are
`MathError`s with a `code` (`syntax`, `brackets`, `empty`, `arity`, `unknown-fn`, `not-expr`, `too-big`, `div0`,
`unsupported`, …) and a message.

Calculators (`ntGcd`, `matDet`, `numIntegrate`, …) keep their own convention. They return a bare value, or
`{value, steps}` when called with `{steps: true}`.

`test/contract.test.cjs` runs the whole benchmark corpus and checks every result against this shape.

### Types

The package is JavaScript and its types are declarations generated from JSDoc (`npm run types` writes `types/`;
`prepare` runs it on install). The contract has hand-written types: `Node` (the AST union, `core/ast.js`), `Text`
(`i18n`), `Step` and `StepInput` (`core/steps.js`), and in `api.js` `Result<K, X> = Solved<K, X> | Failed` with
the signature of every solver. Narrowing on `ok` gives the answer or the reason, and `kind` is the solver's own
union. `test/types/consumer.ts` uses the package the way a TypeScript program would, and it compiles in strict
mode as part of `npm run check`.

## Steps

```
Step = { title: Msg, tex?: string | {lang: string}, text?: Msg, rule?: string, data?: object, sub?: Step[],
         final?: true }
```

- There is one constructor, `step({title, tex, text, rule, data, sub, final})` in `core/steps.js`. It turns a plain
  string or a `{lang: text}` object into a message, and it renders an AST node or a message given as `tex` in
  every language.
- `rule` is a stable code of what the step does (`'chain'`, `'abs-case'`, `'answer'`). The last step of a
  solution has `rule: 'answer'` and `final: true`.
- Every step has a type, `stepType(step)`: its `rule` when it names one, else the key of its title message
  (`'solve.polynomial.compute_discriminant'`). A title glued together from pieces has no key, so such a step
  names a rule. The contract test holds every step of the corpus to this, which lets a program tell steps apart
  without reading their text.
- `data` holds the step's facts for a program rather than a reader. A row operation is
  `{op: 'add', i: 1, j: 0, k: -2, phase, opTex, matrixTex}`, and the Euclid table is `{rows}`.
- `sub` nests steps. For example, each node of a derivative has its own step tree.

A step is language-neutral until someone reads it: `step.title.en`, `step.title.in('kk')`, or
`localize(result, 'en')` for a whole result.

## Languages

The code holds no words. It names a message and passes parameters:

```js
msg('solve.polynomial.two_roots')                                   // '$D > 0$ — два корня'
msg('numbers.theory.modular.solutions_modulo', { d, n, M })         // '%{d} %{n|решение|решения|решений} по модулю %{M}'
msg('solve.inequality.check_sign_by_substituting_point_from', {
    p: (lang) => points.map((p) => `$${tex(p, lang)}$`).join(', '), // a parameter that depends on the language
})
```

- **Keys** are `domain.module.name`, where the domain is the unit's top directory: `solve`, `calculus`, `linalg`,
  `numbers`, `algebra`, `problems`, `generate`, `core`, `api`.
- **Catalogs** live in `src/i18n/<lang>/<domain>.js`, one file per domain, plus `notation.js` (how the language
  writes mathematics) and `grammar.js` (helpers its templates need, such as Russian cases of ordinals).
- **Templates** are strings with slots `%{name}` and plural slots `%{n|one|few|many}`, whose forms follow the
  `Intl.PluralRules` categories of the language. When a slot cannot express the grammar, a template is a function
  `(params, lang, say) => string`.
- **Parameters** are strings, numbers, messages, arrays, or functions of the language. A function is computed for
  every language when the message is made, so it sees the values as they are at that moment.
- **Rendering** happens on demand: `m.ru`, `m.in('kk')`, `` `${m}` `` (the default language), and `JSON.stringify(m)`
  (every language). `localize(tree, lang)` renders a whole result.
- **Notation** is a record per language: the decimal separator, list separators, interval brackets, function
  names (`tg`/`tan`, `lg`/`\log_{10}`), the identity matrix (`E`/`I`), and the words people type in answers
  (`нет решений`, `no solutions`). The printer and the parser read it, so `toTex(node, {lang})` and
  `parse(text, {lang})` follow the language. Machine-readable plain text uses the `MACHINE` notation (English).

`test/i18n.test.cjs` checks that every catalog has every key with compatible slots, that every key the code
names exists, that no message is unused, and that the code contains no Russian text, no comparison with a
language code, and no value written per language.

### Adding a language

1. Copy `src/i18n/en/` to `src/i18n/<code>/` and translate. A catalog may leave keys out: the base language fills
   the gaps.
2. Register it with `registerLanguage('kk', catalog, { base: 'ru' })`. Every message gains a `.kk` getter, and
   everything that renders per language (TeX, steps, answers) renders in `kk` too.
3. To ship the language with the package, register it next to `ru` and `en` at the end of `src/i18n/index.js`.
   The i18n test then holds its catalog to the same completeness rules.

No module outside `src/i18n/` changes.

## Adding a solver method

1. Put it in the unit it belongs to, below the dispatcher. It receives the context and calls the dispatcher back
   through it (`ctx.solve`, `ctx.integrate`, `C.ev`), never by import.
2. Build steps with `step()`. Name the rule, and write every word as a message in both built-in catalogs.
3. Check the answer before returning it: substitute, differentiate back, or compare with the numbers.
4. Add unit tests, and tasks to `bench/tasks/`. Run `npm run check` and the snapshot comparison (see below).

## Testing

| Layer | Where | What it guards |
|---|---|---|
| unit tests | `test/<unit>.test.cjs` | each unit's behaviour, with independent checks (numeric derivatives, quadrature, …) |
| architecture | `test/architecture.test.cjs` | layers, no cycles, entries through `index.js`, message domains |
| i18n | `test/i18n.test.cjs` | complete catalogs, used keys, no language in the code, a third language works |
| contract | `test/contract.test.cjs` | the shape of every result and every step over the whole corpus |
| golden record | `bench/snapshot.mjs`, `bench/golden.json` | every corpus answer and step rendered in every language, and the extra API calls, one hash per record; a refactoring must leave them unchanged |
| benchmark | `bench/run.mjs`, `bench/verify.py` | ~1480 exam and university tasks; the expected answers are checked by SymPy |
| types | `test/types/consumer.ts` | the generated declarations serve a strict TypeScript consumer |
| style | ESLint, Prettier | `npm run lint`, `npm run format:check` |

`npm run check` runs lint, formatting, the tests, the type check and the golden record, and CI (`.github/workflows/ci.yml`) runs
it on Node 20, 22 and 24, followed by the benchmark in strict mode (no wrong answers, errors or timeouts).

A refactoring is done when the golden record does not move. `npm run snapshot:verify` names the records that
changed. For the details, write two full records and compare them:

```sh
node bench/snapshot.mjs --out bench/out/before.json      # on the old code
node bench/snapshot.mjs --out bench/out/after.json       # on the new code
node bench/snapshot.mjs --compare bench/out/before.json bench/out/after.json
```

When the output changes on purpose, update the fingerprints with `npm run snapshot:update` and commit them
together with the change. Floats in the record are rounded to 12 significant digits, so the fingerprints are the
same on every platform.

## Tools for changing the structure

The refactoring tools in `scripts/` work on the syntax tree (acorn), so imports stay right:

- `move-modules.mjs` moves files and rewrites every import of them.
- `split-module.mjs` splits a module by line ranges. It works out the imports and exports of each part and
  refuses to drop a line.
- `move-symbols.mjs` moves declarations between modules and warns when the move would create a cycle.
- `dedupe.mjs` replaces the private copies of a helper with its one shared version.
- `prune-imports.mjs` and `add-imports.mjs` clean up after a move. They remove unused names, merge declarations,
  and import undefined names from their homes.
- `i18n-extract.mjs` moved the texts into the catalogs. `snapshot-lang.mjs` compares two golden records in one
  language.

## Known debts

- Steps record the expression they arrive at only as TeX. A trainer that checks a student's own solution will
  need the expression tree after each step, in `data`, next to the step's type.
- Some checks are heuristics: a sign on an interval is tested at a few points, and convergence is estimated from
  a few distant terms. The engine refuses whenever they disagree, but the step text does not yet say that the
  check was numeric.
