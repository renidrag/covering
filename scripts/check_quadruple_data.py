#!/usr/bin/env python3
"""Independent literal-transcription and input-integrity checks.

This does not import the generator or assembly. It parses the deliberately
restricted decimal-list boundary, not arbitrary Lean syntax. Mathematical
validity and assembly equality are proved separately by Lean.
"""
from collections import Counter
from hashlib import sha256
from pathlib import Path
from itertools import combinations
from math import comb
import json
import re

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT/'coverings/12u-plus-1-4-3/inputs.json'
DECLARATION = re.compile(r'^def (\w+) : ([^\n]+?) := (.*?)(?=^(?:def|theorem|namespace|end|import|set_option|attribute|open)\b|\Z)',re.M|re.S)
LIST_BODY = re.compile(r'\[\s*(?:\{[0-9,\s]+\}\s*,?\s*)*\]')


def without_comments(text):
    """Whitespace-preserving nested-comment scan for this string-free format."""
    output=[];i=0;depth=0;line=False
    while i<len(text):
        pair=text[i:i+2]
        if line:
            output.append('\n' if text[i]=='\n' else ' ')
            if text[i]=='\n':line=False
            i+=1
        elif depth:
            if pair=='/-':depth+=1;output.append('  ');i+=2
            elif pair=='-/':depth-=1;output.append('  ');i+=2
            else:output.append('\n' if text[i]=='\n' else ' ');i+=1
        elif pair=='/-':depth=1;output.append('  ');i+=2
        elif pair=='--':line=True;output.append('  ');i+=2
        else:
            assert text[i] not in ['"','`'], 'strings/quotations are outside the restricted projection grammar'
            output.append(text[i]);i+=1
    assert depth==0, 'unterminated comment'
    return ''.join(output)


def parse_bindings(text):
    clean=without_comments(text)
    result={}
    for match in DECLARATION.finditer(clean):
        name,typ,body=match.groups()
        assert name not in result, 'duplicate declaration'
        result[name]=(typ.strip(),body.strip())
    return result


def parse_literals(text, points):
    """Extract only the documented literal declarations, rejecting aliases/wraps."""
    found={}
    for name,(typ,body) in parse_bindings(text).items():
        if not re.fullmatch(r'part\d+|piece\d+|rows',name):continue
        if name=='rows' and not body.startswith('['):continue
        match=re.fullmatch(r'List \(Finset \(Fin (\d+)\)\)',typ)
        assert match, 'literal declaration type'
        n=match.group(1)
        assert int(n)==points, 'projection point count'
        assert name not in found, 'repeated literal name'
        assert LIST_BODY.fullmatch(body), 'literal declaration has a nonliteral or trailing expression'
        rows=[list(map(int,re.findall(r'\d+',row))) for row in re.findall(r'\{([^{}]+)\}',body)]
        for row in rows:
            assert len(row)==len(set(row)), 'repeated point in projected row'
            assert all(0<=x<points for x in row), 'projected label out of range (Fin wrapping forbidden)'
        found[name]=rows
    assert found, 'no literal rows'
    return found


def compare_rows(actual, projected, points, count=None):
    for row in actual:
        assert isinstance(row,list) and all(type(x) is int for x in row), 'JSON integer labels'
        assert len(row)==len(set(row)), 'JSON repeated point'
        assert all(0<=x<points for x in row), 'JSON label range'
    a=Counter(tuple(sorted(row)) for row in actual)
    b=Counter(tuple(sorted(row)) for row in projected)
    assert all(n==1 for n in a.values()), 'JSON duplicate block'
    assert a==b, 'literal projection differs from authoritative block multiset'
    if count is not None:
        assert len(actual)==count and all(len(row)==4 for row in actual), 'witness shape/count'


def base_projection(text, points):
    declarations=parse_literals(text,points)
    bindings=parse_bindings(text)
    assert bindings['blocks']==(f'Family (Fin {points})','rows.toFinset'), 'base family boundary'
    if 'rows' in declarations:
        assert len(declarations)==1, 'ambiguous base rows'
        return declarations['rows']
    names=sorted(declarations,key=lambda n:int(n[4:]))
    assert bindings['rows']==(f'List (Finset (Fin {points}))',' ++ '.join(names)), 'base join'
    return [row for name in names for row in declarations[name]]


def check_cover(rows, points, count):
    """Independent direct incidence enumeration, without selectors or assembly."""
    compare_rows(rows, rows, points, count)
    incidences=Counter(triple for row in rows for triple in combinations(sorted(row),3))
    missing=[triple for triple in combinations(range(points),3) if triple not in incidences]
    assert not missing, f'uncovered triples: {missing[:5]}'
    return {'points':points,'distinct_blocks':len(rows),'required_triples':comb(points,3),
            'covered_triples':len(incidences),'missing_triples':len(missing),
            'triple_incidences':sum(incidences.values()),
            'triple_multiplicity_histogram':dict(sorted(Counter(incidences.values()).items()))}


def check_historical_witness(root, item):
    """Verify original zstd frame → one-based bytes → normalized block multiset."""
    try:
        from compression.zstd import decompress
    except ImportError as exc:
        raise RuntimeError('Python 3.14+ with standard-library compression.zstd is required; '
                           'the original compressed-witness check cannot be skipped') from exc
    record=json.loads((root/item['record']).read_text())
    data=json.loads((root/item['source']).read_text())
    assert all(type(data[key]) is int for key in ('v','k','t','block_count')), 'integer parameters'
    assert (data['schema'],data['v'],data['k'],data['t'],data['block_count'],data['point_labels']) == (
        'ordinary-cover-v1',25,4,3,600,'0..24'), 'witness parameters'
    compressed=(root/item['original']).read_bytes()
    assert len(compressed)==record['size_bytes']==1448, 'compressed length'
    assert sha256(compressed).hexdigest()==record['sha256'], 'compressed digest'
    enc=record['encoding']
    assert (enc['codec'],enc['layout'],enc['point_numbering'],enc['v'],enc['k'],enc['block_count']) == (
        'zstd','uint8-row-major','one_based',25,4,600), 'historical encoding'
    raw=decompress(compressed)
    assert len(raw)==enc['raw_bytes']==2400, 'raw length'
    assert sha256(raw).hexdigest()==enc['raw_sha256'], 'raw digest'
    assert all(1<=label<=25 for label in raw), 'historical label range'
    shifted=[[label-1 for label in raw[start:start+4]] for start in range(0,2400,4)]
    compare_rows(data['blocks'],shifted,25,600)
    assert data['blocks']==sorted(sorted(row) for row in shifted), 'canonical normalization'
    assert data['provenance']['artifact']==record['id'], 'artifact identity'
    assert data['provenance']['original_sha256']==record['sha256'], 'original provenance'
    assert data['provenance']['raw_sha256']==enc['raw_sha256'], 'raw provenance'
    result=check_cover(data['blocks'],25,600)
    return {**result,'original_to_normalized_equal':True,
            'original_sha256':sha256(compressed).hexdigest(),
            'raw_sha256':sha256(raw).hexdigest(),
            'normalized_sha256':sha256((root/item['source']).read_bytes()).hexdigest()}


def witness_projection(parts, joined, points):
    declarations={}
    for text in parts:
        for name,rows in parse_literals(text,points).items():
            assert name not in declarations, 'duplicate piece declaration'
            declarations[name]=rows
    names=[]
    bindings=parse_bindings(joined)
    for kind in 'ABCD':
        typ,body=bindings[f'file{kind}']
        assert typ==f'List (Finset (Fin {points}))', 'class join type'
        match=re.fullmatch(r'\[([^\]]*)\]\.flatten',body)
        assert match, 'class join grammar'
        tokens=re.sub(r'\s','',match.group(1)).split(',')
        assert all(re.fullmatch(r'piece\d+',x) for x in tokens), 'class join contains non-piece expression'
        names.extend(tokens)
    assert Counter(names)==Counter({name:1 for name in declarations}), 'missing/repeated/unknown joined piece'
    assert bindings['rows']==(f'List (Finset (Fin {points}))','fileA ++ fileB ++ fileC ++ fileD'), 'row join'
    assert bindings['blocks']==(f'Family (Fin {points})','rows.toFinset'), 'family boundary'
    return [row for name in names for row in declarations[name]]


def check(root=ROOT):
    manifest=json.loads((root/'coverings/12u-plus-1-4-3/inputs.json').read_text())
    for item in manifest['inputs']:
        assert sha256((root/item['path']).read_bytes()).hexdigest()==item['sha256'], item['path']
    results=[]
    historical={item['source']:check_historical_witness(root,item)
                for item in manifest.get('historical_witnesses',[])}
    covering_sizes={13:78,25:600,37:1998,49:4704,61:9150,73:15768,85:24990,97:37248}
    checked_coverings=set()
    for item in manifest['projections']:
        actual=json.loads((root/item['source']).read_text())['blocks']
        points=item['points']
        if item['kind'] in ('seed','cover'):
            projected=base_projection((root/item['lean']).read_text(),points)
        else:
            parts=[(root/path).read_text() for path in item['parts']]
            joined=(root/item['lean']).read_text()
            projected=witness_projection(parts,joined,points)
        compare_rows(actual,projected,points,item.get('blocks'))
        coverage={}
        if points in covering_sizes:
            coverage=check_cover(actual,points,covering_sizes[points])
            checked_coverings.add(points)
        results.append({'source':item['source'],'points':points,'blocks':len(actual),
                        'literal_multiset_equal':True,**coverage,**historical.get(item['source'],{})})
    assert checked_coverings==set(covering_sizes), 'missing distributed witness check'
    # The small matching list is retained as a transparent hand-written formula.
    factors=json.loads((root/manifest['factors']['source']).read_text())['factors']
    text=without_comments((root/manifest['factors']['lean']).read_text()).split('def factorRows',1)[1].split('def factors',1)[0]
    branches=re.findall(r'\| (?:[0-3]|_) => (\[[^\n]+\])',text)
    assert len(branches)==5, 'matching projection branches'
    projected=[[list(map(int,re.findall(r'\d+',row))) for row in re.findall(r'\{([^{}]+)\}',b)] for b in branches]
    assert projected==factors, 'matching data correspondence'
    return results


if __name__=='__main__':
    print(json.dumps({'passed':True,'projections':check()},indent=2))
