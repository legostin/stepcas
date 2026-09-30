// Split one large module into several by line ranges, with the imports and exports worked out from the syntax tree.
//   node scripts/split-module.mjs plan.json
// plan: {
//   "source": "src/solve/solve.js",
//   "index": "src/solve/index.js",            // re-exports the source's public names (the source file is removed)
//   "parts": [{ "file": "src/solve/intervals.js", "ranges": [[169, 585]], "doc": "// intervals — …" }, …]
// }
// Every top-level statement goes to the part whose range holds its first line (lines before the first range and
// the original imports are dropped: imports are rebuilt per part). A top-level name used by another part gets
// `export`; each part imports exactly the names it uses — from the original external modules or from its
// siblings. Other files that imported the source are pointed at the index.
import fs from 'node:fs';
import path from 'node:path';
import * as acorn from 'acorn';
import * as walk from 'acorn-walk';

const root = process.cwd();
const plan = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const srcPath = path.resolve(root, plan.source);
const text = fs.readFileSync(srcPath, 'utf8');
const lines = text.split('\n');
const ast = acorn.parse(text, { ecmaVersion: 'latest', sourceType: 'module', locations: true });

const partOf = (line) => plan.parts.findIndex((p) => p.ranges.some(([a, b]) => line >= a && line <= b));

// external imports: local name → {source, imported}
const external = new Map();
for (const st of ast.body) {
    if (st.type !== 'ImportDeclaration') continue;
    for (const sp of st.specifiers) external.set(sp.local.name, { source: st.source.value, imported: sp.imported ? sp.imported.name : 'default', ns: sp.type === 'ImportNamespaceSpecifier' });
}

// top-level declarations: name → part
const declared = new Map();
const publicNames = new Set();
const stmts = [];
for (const st of ast.body) {
    if (st.type === 'ImportDeclaration') continue;
    const p = partOf(st.loc.start.line);
    if (p < 0) throw new Error(`line ${st.loc.start.line} (${text.slice(st.start, st.start + 60)}…) is in no part`);
    const decl = st.type === 'ExportNamedDeclaration' ? st.declaration : st;
    const names = [];
    if (!decl) throw new Error(`bare export list at line ${st.loc.start.line}`);
    if (decl.type === 'FunctionDeclaration' || decl.type === 'ClassDeclaration') names.push(decl.id.name);
    else if (decl.type === 'VariableDeclaration') for (const d of decl.declarations) collectPattern(d.id, names);
    for (const n of names) {
        declared.set(n, p);
        if (st.type === 'ExportNamedDeclaration') publicNames.add(n);
    }
    stmts.push({ st, part: p, names, exported: st.type === 'ExportNamedDeclaration' });
}
function collectPattern(pat, out) {
    if (pat.type === 'Identifier') out.push(pat.name);
    else if (pat.type === 'ObjectPattern') pat.properties.forEach((q) => collectPattern(q.type === 'RestElement' ? q.argument : q.value, out));
    else if (pat.type === 'ArrayPattern') pat.elements.forEach((q) => q && collectPattern(q.type === 'RestElement' ? q.argument : q, out));
    else if (pat.type === 'AssignmentPattern') collectPattern(pat.left, out);
}

// identifiers a statement refers to (property names and object keys excluded; shadowing ignored — harmless)
function refs(node) {
    const out = new Set();
    walk.fullAncestor(node, (n, _state, anc) => {
        if (n.type !== 'Identifier') return;
        const parent = anc[anc.length - 2];
        if (parent?.type === 'MemberExpression' && parent.property === n && !parent.computed) return;
        if ((parent?.type === 'Property' || parent?.type === 'MethodDefinition' || parent?.type === 'PropertyDefinition') && parent.key === n && !parent.computed && !parent.shorthand) return;
        if (parent?.type === 'LabeledStatement' || parent?.type === 'BreakStatement' || parent?.type === 'ContinueStatement') return;
        out.add(n.name);
    });
    return out;
}

const parts = plan.parts.map(() => ({ uses: new Map(), ext: new Map(), chunks: [] }));
const needExport = new Set();
for (const s of stmts) {
    for (const name of refs(s.st)) {
        if (s.names.includes(name)) continue;
        if (declared.has(name)) {
            const owner = declared.get(name);
            if (owner !== s.part) {
                parts[s.part].uses.set(name, owner);
                needExport.add(name);
            }
        } else if (external.has(name)) parts[s.part].ext.set(name, external.get(name));
    }
}

// the text of each part: its lines, with `export` added where a sibling needs the name
const lineOwner = lines.map((_, i) => partOf(i + 1));
const startLines = new Map(stmts.map((s) => [s.st.loc.start.line, s]));
plan.parts.forEach((p, k) => {
    const body = [];
    lines.forEach((ln, i) => {
        if (lineOwner[i] !== k) return;
        const s = startLines.get(i + 1);
        if (s && !s.exported && s.names.some((n) => needExport.has(n)) && s.st.loc.start.column === 0) ln = `export ${ln}`;
        body.push(ln);
    });
    parts[k].body = body.join('\n').replace(/^\n+/, '').replace(/\n+$/, '\n');
});

const relSpec = (fromFile, spec) => {
    if (!spec.startsWith('.')) return spec;
    const target = path.resolve(path.dirname(srcPath), spec);
    let r = path.relative(path.dirname(path.resolve(root, fromFile)), target).split(path.sep).join('/');
    return r.startsWith('.') ? r : `./${r}`;
};
plan.parts.forEach((p, k) => {
    const P = parts[k];
    const imports = [];
    const bySource = new Map();
    for (const [local, e] of P.ext) {
        const key = relSpec(p.file, e.source);
        if (!bySource.has(key)) bySource.set(key, []);
        bySource.get(key).push(e.ns ? `* as ${local}` : e.imported === local ? local : `${e.imported} as ${local}`);
    }
    for (const [src, names] of bySource) imports.push(names.some((n) => n.startsWith('* as')) ? `import ${names[0]} from '${src}';` : `import { ${names.join(', ')} } from '${src}';`);
    const sib = new Map();
    for (const [name, owner] of P.uses) {
        const f = `./${path.basename(plan.parts[owner].file)}`;
        if (!sib.has(f)) sib.set(f, []);
        sib.get(f).push(name);
    }
    for (const [f, names] of [...sib].sort()) imports.push(`import { ${names.sort().join(', ')} } from '${f}';`);
    const out = `${p.doc.trim()}\n\n${imports.join('\n')}\n\n${P.body}`;
    fs.writeFileSync(path.resolve(root, p.file), out);
});

// the index re-exports the public names from their new homes
const byPart = new Map();
for (const n of publicNames) {
    const k = declared.get(n);
    if (!byPart.has(k)) byPart.set(k, []);
    byPart.get(k).push(n);
}
const idx = [plan.indexDoc?.trim() ?? '', ...[...byPart].sort((a, b) => a[0] - b[0]).map(([k, names]) => `export { ${names.sort().join(', ')} } from './${path.basename(plan.parts[k].file)}';`)].join('\n');
fs.writeFileSync(path.resolve(root, plan.index), `${idx}\n`);
fs.unlinkSync(srcPath);

// importers of the old file → the index
const files = [];
const walkDir = (d) => {
    for (const f of fs.readdirSync(d)) {
        const p = path.join(d, f);
        if (f === 'node_modules' || f.startsWith('.')) continue;
        if (fs.statSync(p).isDirectory()) walkDir(p);
        else if (/\.(m?js|cjs)$/.test(f)) files.push(p);
    }
};
for (const d of ['src', 'test', 'bench', 'scripts']) walkDir(path.resolve(root, d));
const idxPath = path.resolve(root, plan.index);
for (const f of files) {
    const src = fs.readFileSync(f, 'utf8');
    const out = src.replace(/(\bfrom\s+|\bimport\s*\(\s*)(['"])(\.{1,2}\/[^'"]+)\2/g, (m, pre, q, spec) => {
        if (path.resolve(path.dirname(f), spec) !== srcPath) return m;
        let r = path.relative(path.dirname(f), idxPath).split(path.sep).join('/');
        if (!r.startsWith('.')) r = `./${r}`;
        return `${pre}${q}${r}${q}`;
    });
    if (out !== src) fs.writeFileSync(f, out);
}
console.log(`split into ${plan.parts.length} parts; ${needExport.size} names shared between parts; ${publicNames.size} public`);
for (const [k, p] of plan.parts.entries()) console.log(`  ${p.file}: ${parts[k].body.split('\n').length} lines, imports ${parts[k].uses.size} sibling names`);
