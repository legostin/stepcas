// Move top-level declarations from one module to another, with the imports worked out from the syntax tree.
//   node scripts/move-symbols.mjs '{"from": "src/solve/trig.js", "to": "src/solve/families.js", "names": ["mkFamily"],
//                                   "doc": "// families — …"}'
// The declarations (with the comment block right above each) are appended to the target, which is created with
// `doc` as its header when it does not exist. The target imports what they use — from the source's own imports or
// from the source itself (a warning then: the two modules may now import each other); the source imports back the
// moved names it still uses; every other module that imported a moved name from the source imports it from the
// target. Unused imports are left for prune-imports; run prettier after.
import fs from 'node:fs';
import path from 'node:path';
import * as acorn from 'acorn';
import * as walk from 'acorn-walk';

const root = process.cwd();
const plan = JSON.parse(process.argv[2]);
const fromPath = path.resolve(root, plan.from);
const toPath = path.resolve(root, plan.to);
const parse = (text) => acorn.parse(text, { ecmaVersion: 'latest', sourceType: 'module', locations: true });
const rel = (fromFile, target) => {
    const r = path.relative(path.dirname(fromFile), target).split(path.sep).join('/');
    return r.startsWith('.') ? r : `./${r}`;
};

function collectPattern(pat, out) {
    if (pat.type === 'Identifier') out.push(pat.name);
    else if (pat.type === 'ObjectPattern') pat.properties.forEach((q) => collectPattern(q.type === 'RestElement' ? q.argument : q.value, out));
    else if (pat.type === 'ArrayPattern') pat.elements.forEach((q) => q && collectPattern(q.type === 'RestElement' ? q.argument : q, out));
    else if (pat.type === 'AssignmentPattern') collectPattern(pat.left, out);
}
function declaredNames(st) {
    const decl = st.type === 'ExportNamedDeclaration' ? st.declaration : st;
    const names = [];
    if (!decl) return names;
    if (decl.type === 'FunctionDeclaration' || decl.type === 'ClassDeclaration') names.push(decl.id.name);
    else if (decl.type === 'VariableDeclaration') for (const d of decl.declarations) collectPattern(d.id, names);
    return names;
}
// identifiers a node refers to (property names and object keys excluded; shadowing ignored — harmless)
function refs(node) {
    const out = new Set();
    walk.fullAncestor(node, (n, _state, anc) => {
        if (n.type !== 'Identifier') return;
        const parent = anc[anc.length - 2];
        if (parent?.type === 'MemberExpression' && parent.property === n && !parent.computed) return;
        if ((parent?.type === 'Property' || parent?.type === 'MethodDefinition' || parent?.type === 'PropertyDefinition') && parent.key === n && !parent.computed && !parent.shorthand)
            return;
        if (parent?.type === 'LabeledStatement' || parent?.type === 'BreakStatement' || parent?.type === 'ContinueStatement') return;
        out.add(n.name);
    });
    return out;
}
function importsOf(ast) {
    const m = new Map(); // local → {source, imported, ns}
    for (const st of ast.body) {
        if (st.type !== 'ImportDeclaration') continue;
        for (const sp of st.specifiers) m.set(sp.local.name, { source: st.source.value, imported: sp.imported ? sp.imported.name : 'default', ns: sp.type === 'ImportNamespaceSpecifier' });
    }
    return m;
}
const specText = (imported, local) => (imported === local ? local : `${imported} as ${local}`);

// ---------------------------------------------------------------- the source
const srcText = fs.readFileSync(fromPath, 'utf8');
const lines = srcText.split('\n');
const ast = parse(srcText);
const ext = importsOf(ast);
const top = new Map(); // name → statement
for (const st of ast.body) for (const n of declaredNames(st)) top.set(n, st);
const moved = new Set(plan.names);
for (const n of plan.names) if (!top.has(n)) throw new Error(`${n} is not declared at the top level of ${plan.from}`);
const stmts = [...new Set(plan.names.map((n) => top.get(n)))].sort((a, b) => a.start - b.start);
for (const st of stmts) for (const n of declaredNames(st)) moved.add(n);

const isComment = (ln) => /^\s*(\/\/|\/\*|\*)/.test(ln);
const chunks = stmts.map((st) => {
    let a = st.loc.start.line - 1;
    while (a > 0 && isComment(lines[a - 1])) a--;
    return { st, a, b: st.loc.end.line - 1 };
});

// what the moved code uses: the source's imports, or names that stay in the source
const needExt = new Map();
const needSource = new Set();
for (const { st } of chunks)
    for (const name of refs(st)) {
        if (moved.has(name)) continue;
        if (top.has(name)) needSource.add(name);
        else if (ext.has(name)) needExt.set(name, ext.get(name));
    }

// the source without the moved code
const drop = new Set();
for (const c of chunks) for (let i = c.a; i <= c.b; i++) drop.add(i);
let rest = lines.filter((_, i) => !drop.has(i));
// names the source still uses
const restAst = parse(rest.join('\n'));
const stillUsed = new Set();
for (const st of restAst.body) if (st.type !== 'ImportDeclaration') for (const n of refs(st)) if (moved.has(n)) stillUsed.add(n);
// names that stay in the source but the moved code needs: exported
const restTop = new Map();
for (const st of restAst.body) for (const n of declaredNames(st)) restTop.set(n, st);
const exportLines = new Set();
for (const n of needSource) {
    const st = restTop.get(n);
    if (st && st.type !== 'ExportNamedDeclaration') exportLines.add(st.loc.start.line - 1);
}
rest = rest.map((ln, i) => (exportLines.has(i) && !ln.startsWith('export ') ? `export ${ln}` : ln));
if (stillUsed.size) {
    const lastImport = restAst.body.filter((st) => st.type === 'ImportDeclaration').at(-1);
    const at = lastImport ? lastImport.loc.end.line : 0;
    rest.splice(at, 0, `import { ${[...stillUsed].sort().join(', ')} } from '${rel(fromPath, toPath)}';`);
}
fs.writeFileSync(fromPath, rest.join('\n').replace(/\n{3,}/g, '\n\n'));

// ---------------------------------------------------------------- the target
const exported = (st, names) => st.type === 'ExportNamedDeclaration' || names.some((n) => stillUsed.has(n));
const body = chunks
    .map(({ st, a, b }) => {
        const text = lines.slice(a, b + 1);
        const first = st.loc.start.line - 1 - a;
        if (st.type !== 'ExportNamedDeclaration' && exported(st, declaredNames(st))) text[first] = `export ${text[first]}`;
        return text.join('\n');
    })
    .join('\n\n');
let target = fs.existsSync(toPath) ? fs.readFileSync(toPath, 'utf8') : `${(plan.doc ?? `// ${path.basename(toPath, '.js')}`).trim()}\n`;
const tAst = parse(target);
const have = importsOf(tAst);
const tTop = new Set(tAst.body.flatMap((st) => declaredNames(st)));
const bySource = new Map();
const add = (spec, s) => {
    if (!bySource.has(spec)) bySource.set(spec, []);
    bySource.get(spec).push(s);
};
for (const [local, e] of needExt) {
    if (have.has(local) || tTop.has(local)) continue;
    const spec = e.source.startsWith('.') ? rel(toPath, path.resolve(path.dirname(fromPath), e.source)) : e.source;
    add(spec, e.ns ? `* as ${local}` : specText(e.imported, local));
}
for (const n of needSource) if (!have.has(n) && !tTop.has(n)) add(rel(toPath, fromPath), n);
if (needSource.size) console.warn(`warning: ${plan.to} now imports ${[...needSource].join(', ')} from ${plan.from}`);
const newImports = [...bySource].map(([spec, names]) => (names[0].startsWith('* as') ? `import ${names[0]} from '${spec}';` : `import { ${names.join(', ')} } from '${spec}';`));
// the target stops importing what it now declares
const tLines = target.split('\n');
for (const st of tAst.body) {
    if (st.type !== 'ImportDeclaration' || st.specifiers.some((sp) => sp.type !== 'ImportSpecifier')) continue;
    const keep = st.specifiers.filter((sp) => !moved.has(sp.local.name));
    if (keep.length === st.specifiers.length) continue;
    for (let i = st.loc.start.line - 1; i < st.loc.end.line; i++) tLines[i] = null;
    if (keep.length) tLines[st.loc.start.line - 1] = `import { ${keep.map((sp) => specText(sp.imported.name, sp.local.name)).join(', ')} } from '${st.source.value}';`;
}
const lastImport = tAst.body.filter((st) => st.type === 'ImportDeclaration').at(-1);
const insertAt = lastImport ? lastImport.loc.end.line : tLines.findIndex((ln) => !isComment(ln)) + 0;
if (newImports.length) tLines.splice(insertAt < 0 ? tLines.length : insertAt, 0, ...(lastImport ? [] : ['']), ...newImports);
target = `${tLines
    .filter((l) => l !== null)
    .join('\n')
    .replace(/\n+$/, '')}\n\n${body}\n`;
fs.mkdirSync(path.dirname(toPath), { recursive: true });
fs.writeFileSync(toPath, target);

// ---------------------------------------------------------------- everyone else
const files = [];
const walkDir = (d) => {
    for (const f of fs.readdirSync(d)) {
        const p = path.join(d, f);
        if (f === 'node_modules' || f.startsWith('.')) continue;
        if (fs.statSync(p).isDirectory()) walkDir(p);
        else if (/\.m?js$/.test(f)) files.push(p);
    }
};
for (const d of ['src', 'test', 'bench', 'scripts']) if (fs.existsSync(path.resolve(root, d))) walkDir(path.resolve(root, d));
let touched = 0;
for (const f of files) {
    if (f === fromPath || f === toPath) continue;
    const text = fs.readFileSync(f, 'utf8');
    let a;
    try {
        a = parse(text);
    } catch {
        continue;
    }
    const edits = [];
    for (const st of a.body) {
        const isImport = st.type === 'ImportDeclaration';
        const isReexport = st.type === 'ExportNamedDeclaration' && st.source;
        if (!isImport && !isReexport) continue;
        if (!st.source.value.startsWith('.') || path.resolve(path.dirname(f), st.source.value) !== fromPath) continue;
        if (st.type === 'ExportAllDeclaration') continue;
        const nameOf = (sp) => (isImport ? sp.imported?.name : sp.local.name);
        const go = st.specifiers.filter((sp) => sp.type !== 'ImportNamespaceSpecifier' && sp.type !== 'ImportDefaultSpecifier' && moved.has(nameOf(sp)));
        if (!go.length) continue;
        const stay = st.specifiers.filter((sp) => !go.includes(sp));
        const kw = isImport ? 'import' : 'export';
        const list = (sps) => sps.map((sp) => (isImport ? specText(sp.imported.name, sp.local.name) : specText(sp.local.name, sp.exported.name))).join(', ');
        const out = [];
        if (stay.length) out.push(`${kw} { ${list(stay)} } from '${st.source.value}';`);
        out.push(`${kw} { ${list(go)} } from '${rel(f, toPath)}';`);
        edits.push([st.start, st.end, out.join('\n')]);
    }
    for (const st of a.body)
        if (st.type === 'ExportAllDeclaration' && path.resolve(path.dirname(f), st.source.value) === fromPath)
            console.warn(`warning: ${path.relative(root, f)} re-exports * from ${plan.from}; the moved names now live in ${plan.to}`);
    if (!edits.length) continue;
    let s = text;
    for (const [x, y, t] of edits.sort((p, q) => q[0] - p[0])) s = s.slice(0, x) + t + s.slice(y);
    fs.writeFileSync(f, s);
    touched++;
}
console.log(`moved ${stmts.length} declarations (${[...moved].join(', ')}) to ${plan.to}; ${touched} importers updated`);
