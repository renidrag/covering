"""Historical C(34,18,3) data integrity and transcription; Lean proves coverage."""
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re


def check(data_path=Path('data/c34183-historical-witness.json'),
          lean_path=Path('lean/CoveringDesigns/C34_18_3/Witness.lean')):
    data = json.loads(data_path.read_text())
    assert data['parameters'] == [34, 18, 3], 'C34 witness parameters'
    blocks = data['blocks_one_based']
    assert len(blocks) == 13, 'C34 witness block count'
    assert all(len(b) == len(set(b)) == 18 for b in blocks), 'C34 block sizes'
    assert all(type(x) is int and 1 <= x <= 34 for b in blocks for x in b), 'C34 labels'
    raw_hash = sha256(bytes(x for b in blocks for x in b)).hexdigest()
    assert raw_hash == '5f8cd4bcedf84fd8032fa2b324e073115f7baaa8729ef437149c7151d19dfa3f', \
        'C34 historical ordered block bytes changed'
    source = data['source_artefact']
    assert source['encoding']['raw_sha256'] == raw_hash, 'C34 raw provenance'
    assert source['encoding']['frame_sha256'] == \
        '878a46e477ed08a152692d3960b2f52740eaa858cab2b93c88780054bc4dcc8a', 'C34 frame provenance'
    assert source['artefact_id'] == 'artefact:a17c4aa7-0a69-59aa-acd4-1b6c694122ec', 'C34 artifact identity'
    assert source['construction_credit'] == 'LJCR; Multiple of (17,9,3) covering', 'C34 construction credit'
    assert source['repository_timestamp'] == '2009-01-20 19:36:43', 'C34 repository date'
    assert source['licence'] == \
        'CC BY 4.0; Daniel M. Gordon / La Jolla Covering Repository.', 'C34 licence'
    assert len({frozenset(b) for b in blocks}) == 13, 'C34 repeated block'
    assert {t for b in blocks for t in combinations(sorted(b), 3)} == \
        set(combinations(range(1, 35), 3)), 'C34 uncovered triple'
    text = lean_path.read_text().split('def knownBlocks13_34_18_3', 1)[1].split(
        '/-- Distinctness', 1)[0]
    lean_blocks = [[int(x) for x in re.findall(r'\d+', b)]
                   for b in re.findall(r'\{([^{}]+)\}', text)]
    assert lean_blocks == [[x - 1 for x in b] for b in blocks], 'C34 Lean transcription'
