#!/usr/bin/env python3
"""Negative controls for the source-snapshot gate; no proof files are changed."""
import json
from lean_inputs import validate_snapshot


def main():
    current = {'Example.lean': 'current-source', 'Example.json': 'current-data'}
    valid = {'proof_input_sha256': current.copy(), 'proof_inputs_unchanged': True}
    validate_snapshot(valid, current)
    rejected = []
    cases = {
        'missing snapshot': {},
        'missing stability check': {'proof_input_sha256': current.copy()},
        'changed during command': {**valid, 'proof_inputs_unchanged': False},
        'stale source': {**valid, 'proof_input_sha256': {**current, 'Example.lean': 'old-source'}},
        'stale data': {**valid, 'proof_input_sha256': {**current, 'Example.json': 'old-data'}},
        'missing input': {**valid, 'proof_input_sha256': {'Example.lean': 'current-source'}},
        'removed input': {**valid, 'proof_input_sha256': {**current, 'Removed.lean': 'old-source'}},
    }
    for label, record in cases.items():
        try:
            validate_snapshot(record, current)
        except ValueError:
            rejected.append(label)
        else:
            raise SystemExit('Invalid record was accepted: ' + label)
    print(json.dumps({'current_record_accepted': True, 'invalid_records_rejected': rejected}, indent=2))


if __name__ == '__main__':
    main()
