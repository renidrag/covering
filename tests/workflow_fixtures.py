"""Fresh source trees for policy tests and real subprocess workflow controls.

The registry and import headers come from the project. SHORT_IMPORTS replaces
only the old, deliberately tiny workflow graphs; it is not a component registry.
Whole-library integration uses the real graph, without these substitutions.
"""
from pathlib import Path, PurePosixPath
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import audit_library as audit


def source_headers(*, whole=False):
    paths = sorted((ROOT / 'lean/CoveringDesigns').rglob('*.lean'))
    paths.append(ROOT / 'lean/CoveringDesigns.lean')
    headers = {}
    for path in paths:
        name = str(path.relative_to(ROOT))
        imports = audit.project_imports(path.read_text(), path)
        headers[name] = ''.join('import ' + dep + '\n' for dep in imports)
    if not whole:
        for module, imports in SHORT_IMPORTS.items():
            headers['lean/' + module.replace('.', '/') + '.lean'] = ''.join(
                'import ' + dep + '\n' for dep in imports)
        headers['lean/CoveringDesigns.lean'] = ''.join(
            'import ' + info['entry'] + '\n' for info in audit.COMPONENTS.values())
    return headers


def memory_tree(contents):
    """A per-test regular-file adapter, not a replacement policy or graph walker.

    Production module_order, project_imports and check_sources run unchanged.
    Only their filesystem reads/writes are in memory. Real path aliases, missing
    files, fingerprints and process behaviour have separate disk/CLI tests.
    No closure/result cache survives (or is used within) a validation call.
    """
    files, children = {}, {}

    class TreePath(PurePosixPath):
        def read_text(self):
            try:
                return files[str(self)]
            except KeyError:
                raise FileNotFoundError(str(self)) from None

        def write_text(self, text):
            files[str(self)] = text
            self.parent.mkdir()
            children[str(self.parent)][self.name] = self
            return len(text)

        def mkdir(self, **kwargs):
            children.setdefault(str(self), {})
            if self.parent != self:
                self.parent.mkdir()
                children[str(self.parent)][self.name] = self

        def is_file(self):
            return str(self) in files

        def exists(self):
            return self.is_file() or str(self) in children

        def unlink(self):
            del files[str(self)]
            del children[str(self.parent)][self.name]

        def is_symlink(self):
            return False

        def iterdir(self):
            return iter(children[str(self)].values())

        def glob(self, pattern):
            return (path for path in self.iterdir() if path.match(pattern)) if self.exists() else iter(())

    for name, text in contents.items():
        TreePath(name).write_text(text)
    return TreePath('.')


def header_graph(headers):
    """Read our normalized fixture format, independently of module_order."""
    return {name.removeprefix('lean/').removesuffix('.lean').replace('/', '.'):
            tuple(line.split()[1] for line in content.splitlines())
            for name, content in headers.items()}


def reachable(graph, entry):
    """Independent work-list oracle: membership only, not a topological sort."""
    pending, found = {entry}, set()
    while pending:
        module = pending.pop()
        if module not in found:
            found.add(module)
            pending.update(graph[module])
    return found


SHORT_IMPORTS = {'CoveringDesigns.CaroTuza': ['CoveringDesigns.CaroTuza.Examples'], 'CoveringDesigns.HorsleySingh.LowerBound': ['CoveringDesigns.HorsleySingh.Matrices'], 'CoveringDesigns.Equality.Slack': [], 'CoveringDesigns.C17_9_5': ['CoveringDesigns.Applications.ZeroDefect'], 'CoveringDesigns.Schoenheim': [], 'CoveringDesigns.C11_5_2.Stanton': [], 'CoveringDesigns.C11_5_2': ['CoveringDesigns.C11_5_2.Stanton'], 'CoveringDesigns.C12_6_3.Structural.Reduction': ['CoveringDesigns.C11_5_2'], 'CoveringDesigns.C12_6_3': ['CoveringDesigns.C12_6_3.Structural.Reduction'], 'CoveringDesigns.C13_7_4': ['CoveringDesigns.C12_6_3.Structural.Reduction'], 'CoveringDesigns.C13_7_4.Structural.CoveringNumber': ['CoveringDesigns.C13_7_4']}
