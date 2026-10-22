#!/usr/bin/env python3
"""Install the pinned Lean dependencies from source archives, without Git.

Python 3.14+ matches the verification runtime and supplies safe extraction. For a local replay,
--reuse-existing links a previously installed dependency tree and its caches.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tarfile
import tempfile
import urllib.request


ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''):
            value.update(chunk)
    return value.hexdigest()


def install(root, reuse_existing=None):
    pins = json.loads((root / 'lean/dependencies.json').read_text())
    vendor = root / 'lean/vendor'
    vendor.mkdir(exist_ok=True)
    packages = pins['packages']
    for package in packages:
        for field in ('directory', 'archive'):
            name = package[field]
            if not isinstance(name, str) or not name or name in ('.', '..') or Path(name).name != name:
                raise ValueError(f'Invalid dependency {field}: {name!r}')
    if reuse_existing is not None:
        existing = reuse_existing.expanduser().resolve()
        provenance = json.loads((existing / 'dependencies-provenance.json').read_text())
        recorded = {item['name']: item for item in provenance['packages']}
        for package in packages:
            directory = existing / package['directory']
            if not directory.is_dir():
                raise ValueError(f'Missing installed dependency: {directory}')
            if package['name'] == 'mathlib':
                if (directory / 'lean-toolchain').read_text().strip() != pins['toolchain']:
                    raise ValueError('Existing Mathlib uses a different Lean toolchain')
                archive = existing / package['archive']
                if not archive.is_file() or sha(archive) != package['sha256']:
                    raise ValueError('Existing Mathlib archive does not match the pinned hash')
            elif recorded.get(package['name'], {}).get('sha256') != package['sha256']:
                raise ValueError(f'Existing dependency provenance differs: {package["name"]}')
        for package in packages:
            target = vendor / package['directory']
            source = existing / package['directory']
            if target.exists() or target.is_symlink():
                if target.resolve() != source.resolve():
                    raise ValueError(f'Installed dependency already occupies {target}')
            else:
                target.symlink_to(source, target_is_directory=True)
        print('Reused the pinned local dependency installation and caches.')
        return
    if sys.version_info < (3, 14):
        raise ValueError('Dependency installation and verification require Python 3.14 or later')
    for package in packages:
        target = vendor / package['directory']
        if target.exists() or target.is_symlink():
            raise ValueError(f'Dependency already exists; keep or remove it manually: {target}')
    with tempfile.TemporaryDirectory(prefix='.dependencies-', dir=vendor) as temporary:
        staging = Path(temporary)
        prepared = []
        for index, package in enumerate(packages):
            archive = staging / package['archive']
            print(f'Downloading pinned {package["name"]} source archive...', flush=True)
            with urllib.request.urlopen(package['url'], timeout=60) as response, archive.open('wb') as output:
                shutil.copyfileobj(response, output)
            if sha(archive) != package['sha256']:
                raise ValueError(f'Archive checksum mismatch: {package["name"]}')
            extraction = staging / str(index)
            extraction.mkdir()
            with tarfile.open(archive) as contents:
                contents.extractall(extraction, filter='data')
            roots = list(extraction.iterdir())
            if len(roots) != 1 or not roots[0].is_dir():
                raise ValueError(f'Unexpected archive layout: {package["name"]}')
            prepared.append((roots[0], vendor / package['directory']))
        for source, target in prepared:
            source.rename(target)
    print('Installed the pinned sources. Compile dependency artifacts before recorded verification.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-existing', type=Path,
                        help='reuse a pinned local vendor directory and its installed caches')
    args = parser.parse_args()
    try:
        install(ROOT, args.reuse_existing)
    except (OSError, ValueError, KeyError, tarfile.TarError) as error:
        parser.exit(1, f'Dependency setup failed: {error}\n')


if __name__ == '__main__':
    main()
