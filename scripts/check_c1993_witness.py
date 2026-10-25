"""Belic witness integrity and exact transcription; Lean separately proves coverage."""
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import re


def check(data_path=Path('data/c1993-belic-witness.json'),
          lean_path=Path('lean/CoveringDesigns/C19_9_3/Witness.lean'),
          retained_path=Path('data/c1993-belic-17.blocks.txt')):
    data = json.loads(data_path.read_text())
    assert data['parameters'] == [19, 9, 3], 'C19 witness parameters'
    rows = data['blocks_one_based']
    assert len(rows) == 17, 'C19 block count'
    assert all(len(b) == len(set(b)) == 9 for b in rows), 'C19 block sizes'
    assert all(type(x) is int and 1 <= x <= 19 for b in rows for x in b), 'C19 labels'
    assert len({frozenset(b) for b in rows}) == 17, 'C19 repeated block'
    raw_hash = sha256(bytes(x for b in rows for x in b)).hexdigest()
    assert raw_hash == '53bd57d226f1d42fb579bbb4538e888d78ef6f55afe93c150b8c726e70ae2841'
    source = data['source_artefact']
    assert source['encoding']['raw_sha256'] == raw_hash, 'C19 raw provenance'
    assert source['encoding']['frame_sha256'] == \
        '33ead2adb4a97eb4a27a936ba6133759b5969690109a75b0b1fd278526241cbc'
    assert source['artefact_id'] == 'artefact:5cc550d0-d955-5916-9a63-2b40900c7f95'
    assert source['construction_credit'] == 'Rade Belic', 'C19 construction credit'
    assert source['repository_timestamp'] == '1997-06-11 00:00:00', 'C19 historical date'
    assert source['licence'] == 'CC BY 4.0; Daniel M. Gordon / La Jolla Covering Repository.'
    text = ''.join(' '.join(map(str, b)) + '\n' for b in rows)
    assert sha256(text.encode()).hexdigest() == source['retained_text_sha256'] == \
        'd18d3854fa404732347cc5ecdbde804c41a21d02664b0c15b0319b29a9bf9947'
    assert retained_path.read_bytes() == text.encode(), 'C19 original retained block list correspondence'
    covered = {t for b in rows for t in combinations(sorted(b), 3)}
    assert covered == set(combinations(range(1, 20), 3)), 'C19 uncovered triple'
    assert len(covered) == 969, 'C19 triple count'
    literal = lean_path.read_text().split('def knownBlocks17_19_9_3', 1)[1].split('/-- Distinctness', 1)[0]
    lean_rows = [[int(x) for x in re.findall(r'\d+', b)]
                 for b in re.findall(r'\{([^{}]+)\}', literal)]
    assert lean_rows == [[x - 1 for x in b] for b in rows], 'C19 Lean transcription'
    return {'blocks': 17, 'block_size': 9, 'points': 19, 'covered_triples': 969,
            'raw_sha256': raw_hash, 'lean_transcription': 'exact ordered shift by -1'}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
