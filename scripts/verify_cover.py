#!/usr/bin/env python3
"""Independent exhaustive set-based verifier; standard library only."""
import argparse
from collections import Counter
from itertools import combinations
import hashlib
import json
from pathlib import Path
import time


def verify(blocks, v, k, t):
    if any(len(b) != k or len(set(b)) != k for b in blocks):
        raise ValueError('Wrong block size or repeated point')
    if any(type(p) is not int or p < 0 or p >= v for b in blocks for p in b):
        raise ValueError('Invalid point')
    bs = [frozenset(b) for b in blocks]
    if len(set(bs)) != len(bs):
        raise ValueError('Duplicate blocks')
    mult = [sum(set(q) <= b for b in bs) for q in combinations(range(v), t)]
    result = {'v': v, 'k': k, 't': t, 'blocks': len(bs), 'distinct': True,
              'subsets': len(mult), 'covered': sum(m > 0 for m in mult),
              'uncovered': sum(m == 0 for m in mult),
              'multiplicity_histogram': dict(sorted(Counter(mult).items())),
              'degrees': [sum(p in b for b in bs) for p in range(v)]}
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('file')
    p.add_argument('--v', type=int, default=13)
    p.add_argument('--k', type=int, default=7)
    p.add_argument('--t', type=int, default=4)
    p.add_argument('--one-based', action='store_true')
    p.add_argument('--output')
    a = p.parse_args()
    start = time.perf_counter()
    raw = Path(a.file).read_bytes()
    if a.file.endswith('.json'):
        data = json.loads(raw)
        blocks = data['blocks'] if isinstance(data, dict) else data
    else:
        blocks = [[int(x) for x in line.split()] for line in raw.decode().splitlines()
                  if line.strip() and not line.lstrip().startswith('#')]
    if a.one_based:
        blocks = [[x-1 for x in b] for b in blocks]
    result = verify(blocks, a.v, a.k, a.t)
    result.update(input_file=a.file, input_sha256=hashlib.sha256(raw).hexdigest(),
                  elapsed_seconds=time.perf_counter()-start)
    text = json.dumps(result, indent=2) + '\n'
    if a.output:
        Path(a.output).parent.mkdir(parents=True, exist_ok=True)
        Path(a.output).write_text(text)
    print(text, end='')
    raise SystemExit(0 if result['uncovered'] == 0 else 1)
