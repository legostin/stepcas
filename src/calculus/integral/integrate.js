// integral/integrate — the public entry integrate(): the cascade, a clean answer, hints for non-elementary integrals.

import { splitCoeff } from '../../core/simplify.js';
import { containsVar, nodeKey, sym, isConst, pow, mapNode, fn, add, freeVars, nodeSome } from '../../core/ast.js';
import { Poly } from '../../core/poly.js';
import { niceForm, prettyForm } from '../derivative/index.js';
import { MathError } from '../../core/rational.js';
import { step } from '../../core/steps.js';
import { NM1, asNode, checkAnti, iTex, isNum, isVar, simp, surelyPositive, trySimp, tx } from './common.js';
import { I } from './engine.js';
import { msg, eachLanguage } from '../../i18n/index.js';

// ---------------------------------------------------------------- non-elementary integrals

function nonElementaryHint(f, v) {
    const g = trySimp(f) ?? f;
    const { rest } = splitCoeff(g);
    if (!rest) return null;
    const fs = rest.type === 'mul' ? rest.args : [rest];
    const vfs = fs.filter((x) => containsVar(x, v));
    const key = (x) => nodeKey(x);
    const X = sym(v);
    const quadExp = (x) => x.type === 'pow' && isConst(x.base) && x.base.name === 'e' && (() => {
        const P = Poly.fromNode(x.exp, v);
        return P && P.degree === 2;
    })();
    if (vfs.length === 1 && quadExp(vfs[0])) {
        // e^(−x²) goes with erf, e^(+x²) with the imaginary error function erfi
        if (Poly.fromNode(vfs[0].exp, v).lead.isPos()) {
            return msg('calculus.integral.integrate.this_integral_has_no_elementary_antiderivative');
        }
        return msg('calculus.integral.integrate.this_integral_has_no_elementary_antiderivative_2');
    }
    const names = vfs.map((x) => (x.type === 'fn' ? x.name : x.type === 'pow' && x.base.type === 'fn' ? x.base.name + '^' + key(x.exp) : key(x)));
    const xm1 = key(pow(X, NM1));
    if (vfs.length === 2 && vfs.some((x) => key(x) === xm1)) {
        const other = vfs.find((x) => key(x) !== xm1);
        if (other.type === 'fn' && other.name === 'sin' && isVar(other.args[0], v)) return msg('calculus.integral.integrate.sin_x_x_dx_has_no');
        if (other.type === 'fn' && other.name === 'cos' && isVar(other.args[0], v)) return msg('calculus.integral.integrate.cos_x_x_dx_has_no');
        if (other.type === 'pow' && isConst(other.base) && other.base.name === 'e' && isVar(other.exp, v)) return msg('calculus.integral.integrate.e_x_dx_has_no_elementary');
    }
    if (vfs.length === 1 && vfs[0].type === 'pow' && isNum(vfs[0].exp) && vfs[0].exp.value.eq(-1) && vfs[0].base.type === 'fn' && vfs[0].base.name === 'ln') {
        return msg('calculus.integral.integrate.dx_ln_x_has_no_elementary');
    }
    if (vfs.length === 1 && vfs[0].type === 'fn' && (vfs[0].name === 'sin' || vfs[0].name === 'cos')) {
        const P = Poly.fromNode(vfs[0].args[0], v);
        if (P && P.degree === 2) return msg('calculus.integral.integrate.fresnel_integrals_sin_x_dx_and');
    }
    if (vfs.length === 1 && vfs[0].type === 'pow' && isVar(vfs[0].base, v) && isVar(vfs[0].exp, v)) return msg('calculus.integral.integrate.x_dx_has_no_elementary_antiderivative');
    void names;
    return null;
}

// ---------------------------------------------------------------- cleaning the answer

export function cleanAnti(F, v) {
    let G = simp(F);
    // atan(tan u) = u up to a piecewise constant — fine for an antiderivative
    G = simp(mapNode(G, (m) => (m.type === 'fn' && m.name === 'atan' && m.args[0].type === 'fn' && m.args[0].name === 'tan' ? m.args[0].args[0] : undefined)));
    // ln|u| with u > 0 everywhere (after a substitution t = eˣ, …) is just ln u
    G = simp(mapNode(G, (m) => (m.type === 'fn' && m.name === 'ln' && m.args[0].type === 'fn' && m.args[0].name === 'abs' && surelyPositive(m.args[0].args[0], v) ? fn('ln', m.args[0].args[0]) : undefined)));
    if (G.type === 'add') {
        const kept = G.args.filter((t) => containsVar(t, v));
        if (kept.length && kept.length < G.args.length) G = simp(add(kept));
    }
    return niceForm(G, v, { fnFractions: false });
}

// ---------------------------------------------------------------- public API

export function checkExpr(node) {
    if (node.type === 'rel' || node.type === 'chain' || node.type === 'list') {
        throw new MathError(msg('calculus.integral.integrate.formula_is_needed_not_equation_or'), null, null, 'not-expr');
    }
}

export function answerStep(title, tex) {
    const s = step({ title, tex, rule: 'answer' });
    s.final = true;
    return s;
}

/**
 * Indefinite integral. → {result: node | null, method, steps, verified, reason?: {ru, en}, tex}.
 * result is an antiderivative (the printed tex adds + C); verified means F′ = f was checked numerically on
 * the domain. When nothing works (or the only candidate fails the check), result is null and reason says
 * so honestly (with a hint for known non-elementary integrals).
 */
export function integrate(node, v = 'x', opts = {}) {
    node = asNode(node);
    checkExpr(node);
    let f;
    try {
        f = simp(node);
    } catch (e) {
        if (e instanceof MathError) throw e;
        throw new MathError(msg('calculus.integral.integrate.could_not_process_expression'), null, null, 'internal');
    }
    const ctx = { v, depth: 0, budget: { calls: 0, max: opts.budget ?? 600, memo: new Map() } };
    const start = step({
        title: msg('calculus.integral.integrate.what_we_integrate'),
        tex: eachLanguage((L) => iTex(node, v, L)),
        text: freeVars(node).filter((w) => w !== v).length
            ? msg('calculus.integral.integrate.we_integrate_with_respect_to_other', { v })
            : msg('calculus.integral.integrate.we_look_for_antiderivative_function_whose'),
        rule: 'start',
    });
    const r = I(f, ctx);
    const fail = (reason) => ({
        result: null,
        method: null,
        steps: opts.steps ? [start, step({ title: msg('calculus.integral.integrate.not_found'), text: reason, rule: 'fail' })] : [],
        verified: false,
        reason,
        tex: null,
    });
    if (!r) {
        const hint = nonElementaryHint(f, v);
        return fail(hint ?? msg('calculus.integral.integrate.could_not_find_antiderivative_engine_cannot'));
    }
    let F = cleanAnti(r.F, v);
    let verified = checkAnti(F, f, v) === true;
    if (!verified) {
        const raw = simp(r.F);
        if (checkAnti(raw, f, v) === true) {
            F = prettyForm(raw);
            verified = true;
        }
    }
    if (!verified && checkAnti(F, f, v) === false) {
        return fail(msg('calculus.integral.integrate.candidate_failed_check_by_differentiation_so'));
    }
    const tex = eachLanguage((L) => `${iTex(node, v, L)} = ${tx(F, L)} + C`);
    const steps = [];
    if (opts.steps) {
        steps.push(start);
        steps.push(r.step);
        const rawTex = (L) => tx(simp(r.F), L);
        if (rawTex('ru') !== tx(F, 'ru')) {
            const raw = simp(r.F);
            const dropped = raw.type === 'add' && raw.args.some((t) => !containsVar(t, v));
            const atanTan = nodeSome(raw, (m) => m.type === 'fn' && m.name === 'atan' && m.args[0].type === 'fn' && m.args[0].name === 'tan');
            let text = dropped
                ? msg('calculus.integral.integrate.tidy_up_answer_constant_terms_go')
                : msg('calculus.integral.integrate.tidy_up_answer');
            if (atanTan) {
                text = msg('calculus.integral.integrate.arctan_tan_u_differs_from_u', { p: (lng) => text[lng] });
            }
            steps.push(step({
                title: msg('calculus.integral.integrate.simplify'),
                tex: eachLanguage((L) => `${rawTex(L)} = ${tx(F, L)}${dropped ? ' + \\mathrm{const}' : ''}`),
                text,
                rule: 'simplify',
            }));
        }
        steps.push(step({
            title: msg('calculus.integral.integrate.check'),
            tex: eachLanguage((L) => `\\left(${tx(F, L)}\\right)' = ${tx(f, L)}`),
            text: verified
                ? msg('calculus.integral.integrate.differentiate_answer_and_compare_with_integrand')
                : msg('calculus.integral.integrate.numeric_check_could_not_be_done'),
            rule: 'check',
        }));
        steps.push(answerStep(msg('calculus.integral.integrate.answer'), tex));
    }
    return { result: F, method: r.method, steps, verified, tex };
}
