"""Check the order-four Lean transcription against the retained positive control.

The finite incidence assertions are proved by Lean's kernel; this comparison
only checks deterministic transcription and preservation of the source model.
"""
import json
from pathlib import Path

SOURCE = Path('data/pair-family/controls/positive-controls.json')
LEAN = Path('lean/CoveringDesigns/TruncatedPlaneLoads/Examples.lean')
START = '-- BEGIN RETAINED ORDER-FOUR CORE\n'
END = '-- END RETAINED ORDER-FOUR CORE'

def seed_text():
    controls = json.loads(SOURCE.read_text())
    core = next(c for c in controls if c['name'] == 'q4-t1-h0')
    rows = ['{' + ', '.join(map(str, row['support'])) + '}' for row in core['supports']]
    assert len(rows) == 16 and all(row['multiplicity'] == 1 for row in core['supports'])
    return 'def coreEdge : Fin 16 → Finset (Fin 20) :=\n  ![' + ',\n    '.join(rows) + ']\n'

def check():
    actual = LEAN.read_text().split(START, 1)[1].split(END, 1)[0]
    assert actual == seed_text(), 'Order-four core transcription changed'
    controls = json.loads(SOURCE.read_text())
    pure = next(c for c in controls if c['name'] == 'q4-t1-h0')
    extended = next(c for c in controls if c['name'] == 'q4-t2-h1')
    expected = {tuple(r['support']): 1 if 0 in r['support'] else 2 for r in pure['supports']}
    expected.update({tuple([0] + list(range(4*i, 4*i+4))): 1 for i in range(1, 5)})
    assert {tuple(r['support']): r['multiplicity'] for r in extended['supports']} == expected
    assert (extended['v'], extended['k'], extended['occurrences']) == (32, 8, 20)
    print('Retained pure and extended controls match the Lean seed and prescription.')

if __name__ == '__main__':
    check()
