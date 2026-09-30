// Replace the private copies of a helper with the one shared version.
//   node scripts/dedupe.mjs '{"name": "asNode", "home": "src/core/parse.js", "keep": [], "scope": "src"}'
// Every other top-level declaration of `name` in src/ is removed (with the comment block right above it), every
// import or re-export of `name` from another module is dropped, and each module that still uses the name imports it
// from the home module. Only files under `scope` (default src) are touched, and files listed in `keep` are left alone
// (a different function under the same name). The copies
// must do the same thing (the home version may do more): check that before running. Run prune-imports and prettier
// after.
import fs from 'node:fs';
import path from 'node:path';
import * as acorn from 'acorn';
import * as walk from 'acorn-walk';

const root = process.cwd();
const { name, home, keep = [], scope = 'src' } = JSON.parse(process.argv[2]);
const homePath = path.resolve(root, home);
const keepPaths = new Set(keep.map((k) => path.resolve(root, k)));
const parse = (text) => acorn.parse(text, { ecmaVersion: 'latest', sourceType: 'module', locations: true });
const rel = (fromFile, target) => {
    const r = path.relative(path.dirname(fromFile), target).split(path.sep).join('/');
    return r.startsWith('.') ? r : `./${r}`;
};
const declares = (st) => {
    const d = st.type === 'ExportNamedDeclaration' ? st.declaration : st;
    if (!d) return false;
    if (d.type === 'FunctionDeclaration' || d.type === 'ClassDeclaration') return d.id.name === name;
    if (d.type === 'VariableDeclaration')
        return d.declarations.length === 1 && d.declarations[0].id.type === 'Identifier' && d.declarations[0].id.name === name;
    return false;
};
function uses(ast) {
    let found = false;
    walk.fullAncestor(ast, (n, _s, anc) => {
        if (found || n.type !== 'Identifier' || n.name !== name) return;
        const parent = anc[anc.length - 2];
        if (parent?.type === 'MemberExpression' && parent.property === n && !parent.computed) return;
        if (parent?.type === 'Property' && parent.key === n && !parent.computed && !parent.shorthand) return;
        if (anc.some((a) => a.type === 'ImportDeclaration' || (a.type === 'ExportNamedDeclaration' && a.source))) return;
        found = true;
    });
    return found;
}

const files = [];
const walkDir = (d) =>
    fs.readdirSync(d).forEach((f) => {
        const p = path.join(d, f);
        if (fs.statSync(p).isDirectory()) walkDir(p);
        else if (p.endsWith('.js')) files.push(p);
    });
walkDir(path.resolve(root, scope));

let removed = 0;
let rewired = 0;
for (const f of files) {
    if (f === homePath || keepPaths.has(f)) continue;
    let text = fs.readFileSync(f, 'utf8');
    const ast = parse(text);
    const lines = text.split('\n');
    const cut = []; // [start, end) offsets
    for (const st of ast.body) {
        if (declares(st)) {
            // take the comment block right above
            let line = st.loc.start.line - 1;
            while (line > 0 && /^\s*(\/\/|\/\*|\*)/.test(lines[line - 1])) line--;
            const start = lines.slice(0, line).join('\n').length + (line ? 1 : 0);
            cut.push([start, st.end + (text[st.end] === '\n' ? 1 : 0), '']);
            removed++;
            continue;
        }
        const isImport = st.type === 'ImportDeclaration';
        const isReexport = st.type === 'ExportNamedDeclaration' && st.source;
        if (!isImport && !isReexport) continue;
        if (st.specifiers.some((sp) => sp.type !== 'ImportSpecifier' && sp.type !== 'ExportSpecifier')) continue;
        const from = st.source.value.startsWith('.') ? path.resolve(path.dirname(f), st.source.value) : null;
        if (from === homePath) continue;
        const own = (sp) => (isImport ? sp.imported.name : sp.local.name) === name;
        if (!st.specifiers.some(own)) continue;
        const rest = st.specifiers.filter((sp) => !own(sp));
        const list = rest.map((sp) =>
            isImport
                ? sp.imported.name === sp.local.name
                    ? sp.local.name
                    : `${sp.imported.name} as ${sp.local.name}`
                : sp.local.name === sp.exported.name
                  ? sp.local.name
                  : `${sp.local.name} as ${sp.exported.name}`,
        );
        cut.push([st.start, st.end, rest.length ? `${isImport ? 'import' : 'export'} { ${list.join(', ')} } from '${st.source.value}';` : '']);
        rewired++;
    }
    if (!cut.length) continue;
    for (const [a, b, t] of cut.sort((x, y) => y[0] - x[0])) text = text.slice(0, a) + t + text.slice(b);
    const after = parse(text);
    if (uses(after)) {
        const last = after.body.filter((st) => st.type === 'ImportDeclaration').at(-1);
        const at = last ? last.end : 0;
        text = `${text.slice(0, at)}\nimport { ${name} } from '${rel(f, homePath)}';${text.slice(at)}`;
    }
    fs.writeFileSync(f, text);
}
console.log(`${name}: removed ${removed} copies, rewired ${rewired} imports; the home is ${home}`);
