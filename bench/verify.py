"""stepcas bench: recompute every expected answer with SymPy, independently of the engine.

    node bench/prep-verify.mjs && bench/.venv/bin/python bench/verify.py [--id ID]

Prints MISMATCH lines (a wrong expected answer in the corpus) and a summary. Tasks SymPy can't settle are
'unverified' (they keep the hand-computed answer).
"""
import json
import re
import signal
import sys
from pathlib import Path

import sympy as sp
from sympy import (E, Eq, I, Integer, Interval, Matrix, Rational, S, Symbol, FiniteSet, Union, EmptySet, oo, pi,
                   N, diff, integrate, limit, simplify, solveset, symbols, sqrt, log, exp, sin, cos, tan, cot, sec, csc,
                   asin, acos, atan, acot, sinh, cosh, tanh, coth, asinh, acosh, atanh, Abs, sign, floor, ceiling,
                   factorial, root, cbrt, Ne, And)
from sympy.solvers.inequalities import solve_univariate_inequality

HERE = Path(__file__).parent
x, y, z, t, n, k, a, b, c = symbols('x y z t n k a b c', real=True)
NS = {name: obj for name, obj in vars(sp).items() if not name.startswith('_')}
NS.update(dict(x=x, y=y, z=z, t=t, n=n, k=k, a=a, b=b, c=c, E=E, I=I, oo=oo, pi=pi))
TOL = 1e-7


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


signal.signal(signal.SIGALRM, _alarm)


def ev(src):
    return eval(src, dict(NS))


def fnum(e):
    v = complex(N(e, 30))
    return v.real if abs(v.imag) < 1e-12 else float('nan')


def close(p, q):
    if p == q:
        return True
    return abs(p - q) <= TOL * max(1, abs(p), abs(q))


def same_numbers(got, want):
    g = sorted(set(round(v, 9) for v in got))
    w = sorted(set(round(v, 9) for v in want))
    return len(g) == len(w) and all(close(p, q) for p, q in zip(g, w))


def parse_set(text):
    """RU interval notation: (-inf; 1] U (3; +inf), {3}, [0; 2]."""
    parts = [p.strip() for p in re.split(r'\s*[U∪]\s*', text)]
    out = EmptySet
    for p in parts:
        if p.startswith('{'):
            out = Union(out, FiniteSet(*[ev(prep(v)) for v in p[1:-1].split(';')]))
            continue
        lo, hi = [s.strip() for s in p[1:-1].split(';')]
        lo = -oo if 'inf' in lo else ev(prep(lo))
        hi = oo if 'inf' in hi else ev(prep(hi))
        out = Union(out, Interval(lo, hi, left_open=p[0] == '(', right_open=p[-1] == ')'))
    return out


def prep(s):
    s = s.replace('^', '**')
    s = re.sub(r'(\d)(pi|sqrt)', r'\1*\2', s)
    return s


def same_set(s1, s2):
    pts = [i / 7 - 40 for i in range(0, 560)]
    for bnd in list(getattr(s1, 'boundary', [])) + list(getattr(s2, 'boundary', [])):
        try:
            v = fnum(bnd)
            pts += [v, v - 1e-6, v + 1e-6]
        except Exception:
            pass
    for p in pts:
        if (sp.Float(p) in s1) != (sp.Float(p) in s2):
            return False, p
    return True, None


def real_roots(eq, var, dom=S.Reals):
    sol = solveset(eq, var, domain=dom)
    return sol


def sample_set(sol, lo=-20, hi=20):
    """Numbers of a solveset answer inside [lo, hi] (ImageSets are unrolled)."""
    vals = []
    if isinstance(sol, FiniteSet):
        return [fnum(s) for s in sol]
    if isinstance(sol, Union):
        for arg in sol.args:
            r = sample_set(arg, lo, hi)
            if r is None:
                return None
            vals += r
        return vals
    if isinstance(sol, sp.ImageSet):
        lam = sol.lamda
        nvar = lam.variables[0]
        for m in range(-40, 41):
            try:
                v = fnum(lam.expr.subs(nvar, m))
            except Exception:
                continue
            if lo - 1e-9 <= v <= hi + 1e-9:
                vals.append(v)
        return vals
    if isinstance(sol, sp.Intersection) or isinstance(sol, sp.Complement):
        return None
    if sol == EmptySet:
        return []
    return None


def fam_values(fams, lo=-20, hi=20):
    out = []
    for bsrc, psrc in fams:
        b0, p0 = fnum(ev(bsrc)), fnum(ev(psrc))
        mm = int((lo - b0) // p0) - 1
        while b0 + mm * p0 <= hi + 1e-9:
            v = b0 + mm * p0
            if v >= lo - 1e-9:
                out.append(v)
            mm += 1
    return out


def satisfies(eq, var, r):
    """The root really solves the equation: both sides defined and real there, and equal."""
    try:
        lv = complex(N(eq.lhs.subs(var, r), 30))
        rv = complex(N(eq.rhs.subs(var, r), 30))
    except Exception:
        return False
    if abs(lv.imag) > 1e-9 or abs(rv.imag) > 1e-9:
        return False
    return abs(lv.real - rv.real) <= 1e-8 * max(1, abs(lv.real), abs(rv.real))


def roots_verdict(eq, var, got, want_vals, want_nodes):
    """SymPy's roots must all be expected ones; expected roots SymPy missed must pass substitution."""
    gs = sorted(set(round(q, 9) for q in got))
    ws = sorted(set(round(q, 9) for q in want_vals))
    extra = [g for g in gs if not any(close(g, w) for w in ws)]
    if extra:
        return 'MISMATCH', f'SymPy has more roots: {extra[:6]}'
    missing = [w for w in ws if not any(close(g, w) for g in gs)]
    if not missing:
        return 'ok', None
    bad = [w for w, node in zip(want_vals, want_nodes) if round(w, 9) in [round(m, 9) for m in missing] and not satisfies(eq, var, node)]
    if bad:
        return 'MISMATCH', f'not roots: {bad[:6]}'
    return 'ok', 'SymPy incomplete, expected roots checked by substitution'


import mpmath


def num_fn(expr, var):
    f = sp.lambdify(var, expr, modules=['mpmath'])

    def g(q):
        try:
            v = complex(f(mpmath.mpf(q)))
        except Exception:
            return float('nan')
        if abs(v.imag) >= 1e-12 or v.real in (float('inf'), float('-inf')):
            return float('nan')
        return v.real
    return g


def scan_roots(expr, var, lo, hi, steps=24000):
    """Real roots of expr on [lo, hi] by a fine scan: sign changes (not poles) and near-zero dips, refined."""
    f = num_fn(expr, var)
    xs = [lo + (hi - lo) * i / steps for i in range(steps + 1)]
    ys = [f(q) for q in xs]
    out = []
    for i in range(steps):
        a0, b0, fa, fb = xs[i], xs[i + 1], ys[i], ys[i + 1]
        if fa != fa or fb != fb:
            continue
        if fa == 0:
            out.append(a0)
            continue
        if fa * fb < 0 and abs(fa) < 1e3 and abs(fb) < 1e3:
            for _ in range(80):
                m = (a0 + b0) / 2
                fm = f(m)
                if fm != fm:
                    break
                if fa * fm <= 0:
                    b0, fb = m, fm
                else:
                    a0, fa = m, fm
            if abs(f((a0 + b0) / 2)) < 1e-6:
                out.append((a0 + b0) / 2)
    for i in range(1, steps):
        if ys[i] == ys[i] and ys[i - 1] == ys[i - 1] and ys[i + 1] == ys[i + 1]:
            if abs(ys[i]) <= abs(ys[i - 1]) and abs(ys[i]) <= abs(ys[i + 1]) and abs(ys[i]) < 1e-3:
                try:
                    r = float(mpmath.findroot(lambda q: f(q), xs[i]))
                    if lo - 1e-9 <= r <= hi + 1e-9 and abs(f(r)) < 1e-9:
                        out.append(r)
                except Exception:
                    pass
    res = []
    for r in sorted(out):
        if not res or abs(r - res[-1]) > 1e-6:
            res.append(r)
    return res


def numeric_solve_check(eq, var, t, ans):
    lo, hi = (-60.0, 60.0)
    if t.get('interval'):
        lo, hi = fnum(ev(t['interval'][0])), fnum(ev(t['interval'][1]))
    got = scan_roots(eq.lhs - eq.rhs, var, lo, hi)
    if 'families' in ans:
        want = fam_values(ans['families'], lo, hi)
    elif ans.get('none'):
        want = []
    elif t.get('ask') and t['ask'] != 'roots':
        g = sorted(got)
        val = {'min': g[0], 'max': g[-1], 'sum': sum(g), 'count': len(g)}.get(t['ask']) if g else None
        return ('ok', 'numeric') if val is not None and close(val, fnum(ev(ans['value']))) else ('MISMATCH', f'numeric roots {g[:8]}')
    else:
        want = [q for q in (fnum(ev(r)) for r in ans['roots']) if lo - 1e-9 <= q <= hi + 1e-9]
    return ('ok', 'numeric') if same_numbers(got, want) else ('MISMATCH', f'numeric roots {got[:8]}')


def numeric_ineq_check(rel, var, want_set):
    f_l, f_r = num_fn(rel.lhs, var), num_fn(rel.rhs, var)
    op = type(rel).__name__
    test = {'StrictLessThan': lambda p, q: p < q, 'LessThan': lambda p, q: p <= q + 1e-12,
            'StrictGreaterThan': lambda p, q: p > q, 'GreaterThan': lambda p, q: p >= q - 1e-12}[op]
    pts = [i / 13 - 30 for i in range(0, 780)]
    for bnd in list(getattr(want_set, 'boundary', [])):
        try:
            v0 = fnum(bnd)
            pts += [v0 - 1e-5, v0 + 1e-5]
        except Exception:
            pass
    for p in pts:
        lv, rv = f_l(p), f_r(p)
        truth = (lv == lv and rv == rv) and test(lv, rv)
        if truth != (sp.Float(p) in want_set):
            return 'MISMATCH', f'differs at {p}'
    return 'ok', 'numeric'


def param_check(t, ans):
    """For a grid of parameter values count the equation's real roots and compare with the expected set."""
    e = ev(t['task'])
    eq = e if isinstance(e, sp.Equality) else Eq(e, 0)
    want = parse_set(ans['set'])
    kind = t.get('want', 'two-roots')
    grid = [sp.Rational(i, 4) for i in range(-48, 49)]
    for bnd in list(getattr(want, 'boundary', [])):
        grid += [sp.nsimplify(bnd)]
    for av in grid:
        e2 = (eq.lhs - eq.rhs).subs(a, av)
        sol = solveset(e2, x, S.Reals)
        if isinstance(sol, FiniteSet):
            cnt = len(sol)
        elif sol == EmptySet:
            cnt = 0
        else:
            cnt = 99
        ok_here = {'two-roots': cnt == 2, 'one-root': cnt == 1, 'has-roots': cnt >= 1}[kind]
        if ok_here != (av in want):
            return 'MISMATCH', f'a = {av}: {cnt} roots'
    return 'ok', 'grid'


def check(t):
    op = t['op']
    ans = t.get('answer', {})
    v = Symbol(t.get('v', 'x'), real=True)
    NS[t.get('v', 'x')] = v
    if op == 'solve':
        e = ev(t['task'])
        eq = e if isinstance(e, sp.Equality) else Eq(e, 0)
        dom = S.Reals
        if t.get('interval'):
            dom = Interval(ev(t['interval'][0]), ev(t['interval'][1]))
        sol = real_roots(eq, v, dom)
        if isinstance(sol, sp.ConditionSet) or sample_set(sol) is None:
            return numeric_solve_check(eq, v, t, ans)
        if ans.get('none'):
            return ('ok', None) if sol == EmptySet else ('MISMATCH', str(sol))
        if 'families' in ans:
            got = sample_set(sol)
            if got is None:
                return 'unverified', str(sol)[:80]
            wv = fam_values(ans['families'])
            return roots_verdict(eq, v, got, wv, [sp.Float(q, 30) for q in wv])
        lo, hi = (-1e6, 1e6)
        if t.get('interval'):
            lo, hi = fnum(ev(t['interval'][0])), fnum(ev(t['interval'][1]))
        got = sample_set(sol, lo, hi) if isinstance(sol, (sp.ImageSet, Union)) else sample_set(sol)
        if got is None:
            return 'unverified', str(sol)[:80]
        if t.get('ask') and t['ask'] != 'roots':
            g = sorted(got)
            val = {'min': g[0], 'max': g[-1], 'sum': sum(g), 'count': len(g)}.get(t['ask']) if g else None
            return ('ok', None) if val is not None and close(val, fnum(ev(ans['value']))) else ('MISMATCH', str(g))
        nodes = [ev(r) for r in ans['roots']]
        return roots_verdict(eq, v, got, [fnum(q) for q in nodes], nodes)
    if op == 'ineq':
        rel = ev(t['task'])
        want = parse_set(ans['set'])
        try:
            sol = solve_univariate_inequality(rel, v, relational=False)
        except Exception:
            return numeric_ineq_check(rel, v, want)
        try:
            ok, at = same_set(sol, want)
        except Exception:
            return numeric_ineq_check(rel, v, want)
        if ok:
            return 'ok', None
        return numeric_ineq_check(rel, v, want) if numeric_ineq_check(rel, v, want)[0] == 'ok' else ('MISMATCH', f'{sol} (differs at {at})')
    if op == 'value':
        return ('ok', None) if close(fnum(ev(t['task'])), fnum(ev(ans['value']))) else ('MISMATCH', str(N(ev(t['task']))))
    if op in ('simplify', 'factor'):
        d = simplify(ev(t['task']) - ev(ans['expr']))
        return ('ok', None) if d == 0 else ('MISMATCH', str(d))
    if op == 'diff':
        d = simplify(diff(ev(t['task']), v) - ev(ans['expr']))
        if d == 0:
            return 'ok', None
        pts = [0.37, 1.3, 2.1, -0.7, 3.3]
        diffs = []
        for p in pts:
            try:
                diffs.append(abs(fnum(d.subs(v, p))))
            except Exception:
                pass
        return ('ok', None) if diffs and max(diffs) < 1e-8 else ('MISMATCH', str(d)[:120])
    if op == 'integral':
        lo, hi = [ev(s) for s in t['bounds']]
        r = integrate(ev(t['task']), (v, lo, hi))
        if ans.get('diverges'):
            return ('ok', None) if r in (oo, -oo, sp.zoo) or r.has(oo) else ('MISMATCH', str(r))
        if r.has(sp.Integral):
            r = sp.Integral(ev(t['task']), (v, lo, hi)).evalf()
        return ('ok', None) if close(fnum(r), fnum(ev(ans['value']))) else ('MISMATCH', str(r))
    if op == 'limit':
        at = ev(t['at'])
        d = {'right': '+', 'left': '-'}.get(t.get('side'), '+-')
        r = limit(ev(t['task']), v, at, d)
        want = ans['value']
        if want == 'dne':
            return ('ok', None) if isinstance(r, sp.AccumBounds) or r.has(sp.AccumBounds) else ('MISMATCH', str(r))
        if want in ('inf', '-inf'):
            return ('ok', None) if r == (oo if want == 'inf' else -oo) else ('MISMATCH', str(r))
        return ('ok', None) if close(fnum(r), fnum(ev(want))) else ('MISMATCH', str(r))
    if op == 'extremum':
        f = ev(t['task'])
        lo, hi = [ev(s) for s in t['segment']]
        crit = solveset(diff(f, v), v, Interval(lo, hi))
        pts = [lo, hi]
        if isinstance(crit, FiniteSet):
            pts += list(crit)
        elif crit != EmptySet:
            vals = sample_set(crit, fnum(lo), fnum(hi))
            if vals is None:
                return 'unverified', str(crit)[:80]
            pts += vals
        vals = [fnum(f.subs(v, p)) for p in pts]
        got = max(vals) if t['kind'] == 'max' else min(vals)
        return ('ok', None) if close(got, fnum(ev(ans['value']))) else ('MISMATCH', f'{got}')
    if op == 'system':
        eqs = [ev(s) for s in t['task']]
        vs = [Symbol(q, real=True) for q in t['vars']]
        for q, s in zip(t['vars'], vs):
            NS[q] = s
        eqs = [ev(s) for s in t['task']]
        sols = sp.solve(eqs, vs, dict=True)
        sols = [s for s in sols if all(sp.im(N(s.get(q, 0))) == 0 for q in vs)]
        if ans.get('none'):
            return ('ok', None) if not sols else ('MISMATCH', str(sols))
        got = sorted(tuple(round(fnum(s[q]), 9) for q in vs) for s in sols)
        want = sorted(tuple(round(fnum(ev(q)), 9) for q in s) for s in ans['solutions'])
        return ('ok', None) if len(got) == len(want) and all(all(close(p, q) for p, q in zip(g, w)) for g, w in zip(got, want)) else ('MISMATCH', str(got))
    if op in ('det', 'inv', 'rank', 'eigen', 'linsolve'):
        M = Matrix([[sp.nsimplify(q) for q in row] for row in t['matrix']])
        if op == 'det':
            return ('ok', None) if close(fnum(M.det()), fnum(ev(ans['value']))) else ('MISMATCH', str(M.det()))
        if op == 'rank':
            return ('ok', None) if M.rank() == ans['value'] else ('MISMATCH', str(M.rank()))
        if op == 'inv':
            if ans.get('none'):
                return ('ok', None) if M.det() == 0 else ('MISMATCH', 'invertible')
            Mi = M.inv()
            W = Matrix([[ev(q) for q in row] for row in ans['matrix']])
            return ('ok', None) if simplify(Mi - W) == sp.zeros(*M.shape) else ('MISMATCH', str(Mi))
        if op == 'eigen':
            got = sorted(set(round(fnum(q), 9) for q in M.eigenvals()))
            want = sorted(set(round(fnum(ev(q)), 9) for q in ans['values']))
            return ('ok', None) if same_numbers(got, want) else ('MISMATCH', str(M.eigenvals()))
        bb = Matrix([sp.nsimplify(q) for q in t['b']])
        try:
            sol = M.LUsolve(bb)
        except Exception:
            return ('ok', None) if ans.get('none') else ('MISMATCH', 'singular')
        if ans.get('none'):
            return 'MISMATCH', str(sol)
        return ('ok', None) if all(close(fnum(sol[i]), fnum(ev(q))) for i, q in enumerate(ans['x'])) else ('MISMATCH', str(list(sol)))
    if op in ('gcd', 'lcm'):
        from math import gcd
        from functools import reduce
        vals = [int(q) for q in t['args']]
        r = reduce(gcd, vals) if op == 'gcd' else reduce(lambda p, q: p * q // gcd(p, q), vals)
        return ('ok', None) if str(r) == str(ans['value']) else ('MISMATCH', str(r))
    if op == 'series':
        return 'unverified', 'series'
    if op == 'param':
        return param_check(t, ans)
    return 'unverified', f'op {op}'


def main():
    only = sys.argv[sys.argv.index('--id') + 1] if '--id' in sys.argv else None
    tasks = json.loads((HERE / 'out' / 'verify.json').read_text())
    counts = {}
    for tk in tasks:
        if only and tk['id'] != only:
            continue
        if 'error' in tk:
            status, note = 'unverified', tk['error']
        else:
            signal.alarm(20)
            try:
                status, note = check(tk)
            except Timeout:
                status, note = 'unverified', 'timeout'
            except Exception as e:  # noqa: BLE001
                status, note = 'unverified', f'{type(e).__name__}: {e}'[:120]
            finally:
                signal.alarm(0)
        counts[status] = counts.get(status, 0) + 1
        if status == 'MISMATCH' or (only and status != 'ok') or ('--all' in sys.argv and status != 'ok'):
            print(f'{status}  {tk["id"]}  {note}')
    print(' · '.join(f'{k}: {v}' for k, v in sorted(counts.items())))


if __name__ == '__main__':
    main()
