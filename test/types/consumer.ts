// A consumer of the package in TypeScript: compiles against the generated declarations (npm run types:check).
import { solveEquation, integrate, limit, checkRoot, step, msg, localize, parse, toTex, Q, type Step, type Node, type Result } from '../../types/index.js';

const r = solveEquation('x^2 = 4');
if (r.ok) {
    const kind: 'roots' | 'none' | 'all' | 'set' = r.kind;
    const first: Node = r.roots[0].node;
    const s: Step = r.steps[0];
    const title: string = s.title.in('en');
    void [kind, first, title, r.answer.tex, r.answer.text];
} else {
    const why: 'invalid' | 'unsupported' = r.kind;
    void [why, r.reason, r.pos];
}

const F: Result<'antiderivative', { result: Node }> = integrate('x e^x');
if (F.ok) void toTex(F.result, { lang: 'en' });

const L = limit('sin(x)/x', 'x', 0);
if (L.ok && L.kind === 'value') void L.value;

const c = checkRoot('x^2 = 4', 'x', 2);
if (c.ok) void (c.isRoot ? c.why : null);

const own: Step = step({ title: msg('api.unsupported'), tex: parse('x^2'), rule: 'demo', data: { k: 1 } });
void localize(own, 'en');
void Q.of('3/4').add(1).toTex();
