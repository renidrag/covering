"""Fingerprint project-owned inputs used by the Lean verification commands."""
import hashlib
import json
from pathlib import Path


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''):
            digest.update(chunk)
    return digest.hexdigest()


def snapshot():
    """Called from the repository root; build caches and explorations are excluded."""
    lean = Path('lean')
    paths = set((lean / 'CoveringDesigns').rglob('*.lean'))
    paths.update((lean / 'audits').glob('*.lean'))
    paths.update(lean / name for name in [
        'CoveringDesigns.lean', 'lean-toolchain', 'lakefile.toml',
        'lake-manifest.json',
        'vendor/dependencies-provenance.json'])
    for manifest in Path('coverings').glob('*/inputs.json'):
        paths.add(manifest)
        paths.update(Path(item['path']) for item in json.loads(manifest.read_text())['inputs'])
    return {str(path): sha(path) for path in sorted(paths)}


def changed_paths(before, after):
    return sorted(path for path in before.keys() | after.keys()
                  if before.get(path) != after.get(path))


def validate_snapshot(record, current):
    """Reject a successful process log if it cannot certify the current inputs."""
    captured = record.get('proof_input_sha256')
    if not captured:
        raise ValueError('The run has no proof-input snapshot; run scripts/audit_library.py --verify.')
    if record.get('proof_inputs_unchanged') is not True:
        raise ValueError('Proof inputs changed while the recorded command was running.')
    changes = changed_paths(captured, current)
    if changes:
        raise ValueError('The recorded run is stale for: ' + ', '.join(changes[:5]) +
                         '. Run scripts/audit_library.py --verify.')
