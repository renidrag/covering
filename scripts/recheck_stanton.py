#!/usr/bin/env python3
"""Recompile the standalone structural proof without project build artifacts.

Run through `lake -d lean env python3 scripts/recheck_stanton.py` from the
repository root. Vendored dependency caches are reused; every project module
in the eleven-point import closure is compiled into a fresh temporary tree.
The normal project build directory is excluded from the import search path.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


def recheck(entry='CoveringDesigns.C11_5_2', audit='lean/audits/C11_5_2.lean',
            record_path='results/stanton-structural-fresh.json',
            prefix='stanton-recheck-', memory_mib=3072, long_checks=None):
    root = Path('lean').resolve()
    compiler = shutil.which('lean')
    if compiler is None or 'LEAN_PATH' not in os.environ:
        raise SystemExit('Run this script through lake env.')
    ordered = []
    seen = set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        source = root / (module.replace('.', '/') + '.lean')
        for dep in re.findall(r'^import\s+(CoveringDesigns(?:\.[A-Za-z0-9_]+)*)\s*$',
                              source.read_text(), re.MULTILINE):
            visit(dep)
        ordered.append((module, source))

    visit(entry)
    project_build = root / '.lake/build/lib/lean'
    dependency_paths = [p for p in os.environ['LEAN_PATH'].split(os.pathsep)
                        if p and Path(p).resolve() != project_build]
    if any((Path(p) / 'CoveringDesigns').exists() for p in dependency_paths):
        raise SystemExit('Unexpected project artifacts in the remaining import path.')
    entries = []
    start = time.monotonic()
    with tempfile.TemporaryDirectory(prefix=prefix, dir=root / '.lake') as tmp:
        env = {**os.environ, 'LEAN_PATH': os.pathsep.join([tmp, *dependency_paths])}
        for module, source in ordered:
            output = Path(tmp) / (module.replace('.', '/') + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            command = [compiler, f'-M{memory_mib}', '-j1', '--root=' + str(root),
                       '-o', str(output), str(source)]
            before = time.monotonic()
            print('Checking ' + module, flush=True)
            timeout = (long_checks or {}).get(module, 60)
            subprocess.run(command, env=env, check=True, timeout=timeout)
            entries.append({'module': module, 'command': command,
                            'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                            'timeout_seconds': timeout,
                            'elapsed_seconds': time.monotonic() - before})
        command = [compiler, f'-M{memory_mib}', '-j1', audit]
        subprocess.run(command, env=env, check=True, timeout=30)
    record = {'scope': f'Fresh compilation of every project module imported by {entry}, followed by its exact statement and axiom audit.',
              'project_build_artifacts_excluded': True,
              'dependency_caches_reused': True,
              'compiler': compiler,
              'version': subprocess.check_output([compiler, '--version'], text=True).strip(),
              'modules': entries, 'audit_command': command,
              'elapsed_seconds': time.monotonic() - start}
    Path(record_path).write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'fresh_modules': len(entries),
                      'elapsed_seconds': record['elapsed_seconds'], 'audit_passed': True}), flush=True)


if __name__ == '__main__':
    recheck()
