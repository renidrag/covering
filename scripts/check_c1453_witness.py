"""C14 historical witness integrity/transcription; Lean proves its covering claims."""
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re


def check(data_path=Path('data/c1453-historical-witness.json'),
          lean_path=Path('lean/CoveringDesigns/C14_5_3/Witness.lean')):
    data = json.loads(data_path.read_text())
    assert data['parameters'] == [14, 5, 3], 'C14 witness parameters'
    blocks = data['blocks_one_based']
    assert len(blocks) == 43, 'C14 witness block count'
    assert all(len(b) == 5 and len(set(b)) == 5 for b in blocks), 'C14 block sizes'
    assert all(type(x) is int and 1 <= x <= 14 for b in blocks for x in b), 'C14 labels'
    raw_hash = sha256(bytes(x for b in blocks for x in b)).hexdigest()
    assert raw_hash == '173772ab8d73847ff258f4f5ae2859d0fbe7e312483e1afc23d58c721bd22f93', \
        'C14 historical ordered block bytes changed'
    assert data['source_artefact']['encoding']['raw_sha256'] == raw_hash, 'C14 raw provenance'
    assert data['source_artefact']['licence'] == \
        'CC BY 4.0; Daniel M. Gordon / La Jolla Covering Repository.', 'C14 licence'
    assert len({frozenset(b) for b in blocks}) == 43, 'C14 repeated block'
    assert all(any(set(t) <= set(b) for b in blocks)
               for t in combinations(range(1, 15), 3)), 'C14 uncovered triple'
    text = lean_path.read_text().split('def knownBlocks43_14_5_3', 1)[1].split(
        '/-- Distinctness', 1)[0]
    lean_blocks = [[int(x) for x in re.findall(r'\d+', b)]
                   for b in re.findall(r'\{([^{}]+)\}', text)]
    assert lean_blocks == [[x-1 for x in b] for b in blocks], 'C14 Lean transcription'
