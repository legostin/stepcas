# stepcas

A computer algebra system that shows its work. Exact answers with school-style step-by-step solutions in
Russian and English, in plain JavaScript with no dependencies. Runs in the browser and in Node.

```js
import { solveEquation, evaluateSteps, integrate, solveOde, solveWithParameter } from 'stepcas';

solveEquation('log_2(x + 3) = 5').answer.text;            // "29"
evaluateSteps('36^(log_6(5))').steps;                       // 36 = 6², a^(log_a b) = b, … = 25
integrate('1/(x^4 + 1)').steps;                             // split along x² ± 1, t = x ∓ 1/x, …
solveOde("y'' + y = x; y(0) = 0; y'(0) = 0").text;         // "x - sin(x)"
solveWithParameter({ task: 'x^3 - 3x = a', want: 3 }).text; // "(-2, 2)"
```

Every solver returns the same shape: `{ok, kind, answer: {tex, text}, steps, …}`, or `{ok: false, kind:
'invalid' | 'unsupported', reason}` when there is no answer. It never throws on what a person types. Each step
names the rule it used and gives the formula in TeX, the way a teacher would write it on the board. Answers are
exact (BigInt rationals, radicals, π, e). When an answer is only numeric, it is marked as approximate.

TypeScript types come with the package: `Result<K, X>` narrows on `ok` to the answer or the reason.

Texts are messages, rendered in any registered language: `r.steps[0].title.en`, `localize(r, 'ru')`. Russian
and English are built in. A new language is one catalog and one call, `registerLanguage('kk', catalog, {base:
'ru'})`, with no change to the code.

## What it covers

- **Arithmetic and algebra**: exact rationals, simplification, expanding, factoring (with the formula for each
  step), reducing fractions with the excluded values, the value of an expression step by step (logarithms,
  powers, roots, reduction formulas).
- **Equations and inequalities**: linear, quadratic, rational, radical, exponential, logarithmic, with |x|,
  trigonometric (families of roots, selection on a segment); the domain, extraneous roots, the method of
  intervals (also the generalised one); systems, linear and nonlinear.
- **Parameters**: through the discriminant, or the graphical way (a = g(x), monotone pieces, counting roots
  for every level).
- **Calculus**: derivatives, integrals (table, substitution, parts, rational functions, trigonometric forms,
  definite and improper), limits (L'Hôpital, equivalents, Taylor), greatest and least values on a segment.
- **ODEs**: separable, linear, homogeneous first-order equations; second order with constant coefficients,
  with right-hand sides by undetermined coefficients or variation of parameters.
- **Series**: arithmetic, geometric, arithmetico-geometric, telescoping, classic sums, tests for divergence.
- **Linear algebra**: exact matrices over Q, Gauss–Jordan with every row operation, determinants, inverses,
  eigenvalues, least squares.
- **Number theory**: gcd/lcm, primes and factorisation, congruences.
- **Task generators**: 28 families of exam-style tasks built backwards from their answers, with a seed, a level
  (1–3) and wording in every language. They are meant for trainers and tests.

The full API is in [docs/API.md](docs/API.md). How the engine is built — its layers, the result contract, the
step model, languages and the tests that hold it together — is in [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md).

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

A wrong answer counts against the engine; a refusal only counts as unsolved. The engine prefers saying it
cannot solve something to guessing: numeric fallbacks are labelled as such, and new methods check their
answers by substituting them back.

```sh
npm run check            # lint, formatting and 514 tests (architecture, i18n and the result contract included)
npm run bench            # the corpus → bench/REPORT.md (--strict fails on a wrong answer)
npm run snapshot:verify  # every answer and step against the golden fingerprints
node bench/gen.mjs       # rebuild the generated part from fixed seeds
npm run bench:verify     # recheck the expected answers with SymPy (needs bench/.venv with sympy)
```

## Where it comes from

stepcas is the maths engine of [legost.in](https://legost.in/utilities/math): the course «Математика — царица
наук» and the canvas calculator. It was taken out as a package to grow it past the site's needs, towards
solvers and trainers.

## License

MIT © 2026 legostin
