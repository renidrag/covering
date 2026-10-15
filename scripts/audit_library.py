#!/usr/bin/env python3
"""Compile the public proofs serially and audit their statements and dependencies.

Use --verify to check every project module in dependency order, with a time
limit and an optional memory guard for each Lean invocation. Without --verify, validate
existing records against the current inputs. Lean verifies the proofs; this
script records the checks and rejects stale records.
"""
import argparse
from datetime import datetime, timezone
import json
import math
import os
from pathlib import Path
import re

from lean_inputs import changed_paths, sha, snapshot, validate_snapshot

ROOT = Path('lean')
ORDINARY = {'propext', 'Classical.choice', 'Quot.sound'}
IMPORT = re.compile(r'^import\s+((?:CoveringDesigns|Explorations)(?:\.[A-Za-z0-9_]+)*)\s*$', re.M)
RUNNER_INPUTS = [Path('scripts') / name for name in (
    'audit_library.py', 'verify_c13_structural.py', 'lean_inputs.py',
    'run_logged.py', 'run_memory_guard.py', 'workflow.py',
    'covering_cli.py', 'record_io.py')] + [Path('covering')]
COMPONENTS = {
    '11-5-2': {
        'entry': 'CoveringDesigns.C11_5_2',
        'theorems': ['CoveringDesigns.stanton_classification',
                     'CoveringDesigns.stanton_classification_unique_on',
                     'CoveringDesigns.covering_number_11_5_2'],
        'milestones': ['CoveringDesigns.lower_bound_11_5_2',
                       'CoveringDesigns.stanton_representative_isCover',
                       'CoveringDesigns.stanton_representatives_not_isomorphic',
                       'CoveringDesigns.Audit11.classification_explicit',
                       'CoveringDesigns.StantonStructural.template_classification',
                       'CoveringDesigns.StantonStructural.exists_six_block_frame',
                       'CoveringDesigns.StantonStructural.SixBlockFrame.nonempty_templatePartition'],
        'independent_of': ['12-6-3', '13-7-4'],
        'scope': 'Exact minimum 7 and exactly two isomorphism types of minimum coverings.'},
    '12-6-3': {
        'entry': 'CoveringDesigns.C12_6_3',
        'theorems': ['CoveringDesigns.gppt_classification',
                     'CoveringDesigns.covering_number_12_6_3'],
        'milestones': ['CoveringDesigns.gppt_structural_reduction',
                       'CoveringDesigns.GPPTStructural.template_classification',
                       'CoveringDesigns.GPPTStructural.lower_bound_fifteen',
                       'CoveringDesigns.GPPTProjective.no_duplicate_isomorphicTemplateCompletion',
                       'CoveringDesigns.figure6_isCover'],
        'independent_of': ['13-7-4'],
        'scope': 'Exact minimum 15 and completeness of the 68-entry list, using the structural GPPT reduction and kernel-checked completion witnesses. Pairwise nonisomorphism is not asserted.'},
    '13-7-4': {
        'entry': 'CoveringDesigns.C13_7_4',
        'theorems': ['CoveringDesigns.covering_number_13_7_4'],
        'milestones': ['CoveringDesigns.lower_bound_30',
                       'CoveringDesigns.upper_bound_30',
                       'CoveringDesigns.C13Structural.minimum_pair_degree_seven',
                       'CoveringDesigns.C13Structural.bad_quadruple_excluded',
                       'CoveringDesigns.gppt_structural_reduction',
                       'CoveringDesigns.StantonStructural.template_classification'],
        'independent_of': ['GPPT catalogue and completion enumeration'],
        'scope': 'Exact minimum 30 by structural compatibility of minimum links, the five-point count, and the explicit thirty-block witness.'},
}


def source(module):
    return ROOT / (module.replace('.', '/') + '.lean')


def module_order(entries):
    """Topological order of project imports; external dependencies are installed."""
    ordered, seen, active = [], set(), set()

    def visit(module):
        if module in seen:
            return
        assert module not in active, f'Import cycle at {module}'
        path = source(module)
        assert path.is_file(), f'Missing local import: {path}'
        active.add(module)
        for dependency in IMPORT.findall(path.read_text()):
            visit(dependency)
        active.remove(module)
        seen.add(module)
        ordered.append(module)

    for entry in entries:
        visit(entry)
    return ordered


def closure(entry):
    return {source(module) for module in module_order([entry])}


def check_sources():
    closures = {key: closure(item['entry']) for key, item in COMPONENTS.items()}
    c11, c12, c13 = (closures[key] for key in ('11-5-2', '12-6-3', '13-7-4'))
    assert c11 <= c12, 'GPPT must import the standalone Stanton component'
    for key, info in COMPONENTS.items():
        forbidden = [COMPONENTS[other]['entry'] for other in info['independent_of'] if other in COMPONENTS]
        for path in closures[key]:
            module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
            assert not any(module == entry or module.startswith(entry + '.') for entry in forbidden), \
                f'{key} imports an independent component: {path}'
    assert source('CoveringDesigns.C12_6_3.Structural.Reduction') in c13
    assert source('CoveringDesigns.C11_5_2.Stanton') in c13
    catalogue_modules = {source('CoveringDesigns.C12_6_3.' + name) for name in (
        'Catalogue', 'CatalogueBridge', 'Classification',
        'Structural.CompletionEncoding', 'Structural.CompletionData',
        'Structural.CompletionSupport', 'Structural.CompletionChecks',
        'Structural.Completions')}
    structural = closure('CoveringDesigns.C12_6_3.Structural.Reduction')
    for name, paths in [('GPPT structural reduction', structural), ('C13', c13)]:
        unexpected = paths & catalogue_modules
        assert not unexpected, f'{name} imports catalogue/classification modules: {sorted(unexpected)}'
    paths = set().union(*closures.values()) | set((ROOT / 'audits').glob('*.lean'))
    for path in paths:
        text = path.read_text()
        assert not {'Explorations', 'Checked'}.intersection(path.parts), path
        assert not re.search(r'\b(?:sorry|admit)\b|^\s*(?:axiom|unsafe)\b', text, re.M), path
        assert not re.search(r'\b(?:native_decide|bv_decide|bv_check)\b|decide\s*\+native', text), path
    for path in (ROOT / 'CoveringDesigns/Foundations').glob('*.lean'):
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        assert not any({'C11_5_2', 'C12_5_2', 'C12_6_3', 'C13_7_4', 'Explorations'}.intersection(p.parts)
                       for p in closure(module)), path
    return closures


def check_manifests():
    for manifest in Path('coverings').glob('*/inputs.json'):
        for item in json.loads(manifest.read_text())['inputs']:
            assert sha(Path(item['path'])) == item['sha256'], item['path']


def audit_name(key):
    return COMPONENTS[key].get('audit_name', 'c' + key.split('-')[0] + '-audit')


def explicit_theorem(key):
    namespace = COMPONENTS[key].get('audit_namespace', 'CoveringDesigns.Audit' + key.split('-')[0])
    return namespace + '.covering_number_explicit'


def verification_plan(keys, memory_mib):
    """A shared serial compiler/audit plan for the library and C13 entry points."""
    entries = ['CoveringDesigns'] if len(keys) == len(COMPONENTS) else [COMPONENTS[k]['entry'] for k in keys]
    plan = {}
    for module in module_order(entries):
        output = ROOT / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
        plan['build-' + module] = ('build', ['lake', '-d', 'lean', 'env', 'lean',
                                            f'-M{memory_mib}', '-o', str(output), str(source(module))])
    for key in keys:
        suffix = key.replace('-', '_')
        name = audit_name(key)
        assert name not in plan, f'Duplicate audit name: {name}'
        plan[name] = ('audit',
            ['lake', '-d', 'lean', 'env', 'lean', f'-M{memory_mib}', str(ROOT / 'audits' / f'C{suffix}.lean')])
    if len(keys) == len(COMPONENTS):
        plan['all-audit'] = ('audit', ['lake', '-d', 'lean', 'env', 'lean',
                                    f'-M{memory_mib}', str(ROOT / 'audits/All.lean')])
    return plan


def record_path(prefix, name):
    return Path('results') / f'{prefix}-{name}.run.json'


def successful_run(prefix, name, kind, command, current, *, memory_guard=True):
    path = record_path(prefix, name)
    record = json.loads(path.read_text())
    assert record['returncode'] == 0 and not record['watchdog_timeout'], path
    assert record['command'] == command, f'Unexpected recorded command: {path}'
    memory_mib = int(next(arg[2:] for arg in command if arg.startswith('-M')))
    expected_guard = memory_mib if memory_guard else None
    assert record['memory_guard_mib'] == expected_guard, f'Unexpected memory guard: {path}'
    executed = record['executed_command']
    if memory_guard:
        assert executed[1:] == ['scripts/run_memory_guard.py', '--mib', str(memory_mib), *command], path
    else:
        assert executed == command, f'Unexpected unguarded command: {path}'
    assert not record.get('interrupted_signal'), f'Interrupted command: {path}'
    validate_snapshot(record, current)
    for script in RUNNER_INPUTS:
        assert record['source_hashes'].get(str(script)) == sha(script), f'Changed verification script: {script}'
    log = Path('results') / f'{prefix}-{name}.log'
    assert record['log_sha256'] == sha(log), f'Changed build/audit log: {log}'
    if kind == 'build':
        output = Path(command[command.index('-o') + 1])
        assert record.get('output_sha256', {}).get(str(output)) == sha(output), f'Changed compiled module: {output}'
    return {'record': str(path), 'log': str(log), 'log_sha256': sha(log),
            'command': command, 'elapsed_seconds': record['elapsed_seconds'],
            'memory_guard_mib': record['memory_guard_mib']}


def axioms(log, theorem):
    if re.search(r"'" + re.escape(theorem) + r"' does not depend on any axioms", log):
        return []
    match = re.search(r"'" + re.escape(theorem) + r"' depends on axioms: \[([^\]]*)\]", log)
    assert match, f'Theorem missing from successful audit: {theorem}'
    items = [a.strip() for a in match[1].split(',') if a.strip()]
    assert set(items) <= ORDINARY, f'Nonstandard axioms in {theorem}: {items}'
    return items


def verification_record(keys, prefix, plan, current, closures, lean_version, *, memory_guard=True):
    """Revalidate every command and theorem before constructing a summary."""
    records = {name: successful_run(prefix, name, kind, command, current, memory_guard=memory_guard)
               for name, (kind, command) in plan.items()}
    components = {}
    for key in keys:
        info = COMPONENTS[key]
        log = Path(records[audit_name(key)]['log']).read_text()
        explicit = explicit_theorem(key)
        checked = {t: axioms(log, t) for t in info['theorems'] + info['milestones'] + [explicit]}
        equality = 'CoveringDesigns.covering_number_' + key.replace('-', '_')
        assert set(checked[equality]) == set(checked[explicit]) == ORDINARY, equality
        components[key] = {**info, 'source_closure': sorted(map(str, closures[key])),
                           'axioms': checked[equality], 'audited_theorem_axioms': checked,
                           'native_assertion_count': 0}
    if 'all-audit' in records:
        log = Path(records['all-audit']['log']).read_text()
        for key in keys:
            assert set(axioms(log, 'CoveringDesigns.covering_number_' + key.replace('-', '_'))) == ORDINARY
    check_manifests()
    assert not changed_paths(current, snapshot()), 'Proof inputs changed while recording the audit'
    return {
        'recorded_utc': datetime.now(timezone.utc).isoformat(),
        'lean_version': lean_version,
        'components': components,
        'no_admissions_or_custom_mathematical_axioms': True,
        'no_native_assertions': True,
        'dependency_boundaries_checked': True,
        'proof_inputs_unchanged': True,
        'proof_input_sha256': current,
        'verification_script_sha256': {str(p): sha(p) for p in RUNNER_INPUTS},
        'verification_runs': records,
        'trust_scope': 'Each audited public covering-number theorem uses exactly propext, Classical.choice, and Quot.sound. Finite proof computations are checked by the Lean kernel.'}


def main(*, only_c13=False):
    """Compatibility entry points share the CLI's recorded workflow."""
    os.chdir(Path(__file__).resolve().parents[1])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', default=only_c13)
    parser.add_argument('--component', choices=list(COMPONENTS),
                        default='13-7-4' if only_c13 else None)
    parser.add_argument('--resume', nargs='?', const='latest',
                        help='reuse validated steps from the latest or named run')
    parser.add_argument('--build-timeout', type=float)
    parser.add_argument('--audit-timeout', type=float)
    parser.add_argument('--memory-mib', type=int)
    parser.add_argument('--memory-guard', action=argparse.BooleanOptionalAction, default=None)
    args = parser.parse_args()
    for value in (args.build_timeout, args.audit_timeout, args.memory_mib):
        if value is not None and (not math.isfinite(value) or value <= 0):
            parser.error('time and memory limits must be positive and finite')
    from covering_cli import main as cli_main

    target = args.component or 'all'
    command = ['verify' if args.verify or args.resume else 'audit', target]
    if args.resume:
        command.extend(['--resume', args.resume])
    for name in ('build_timeout', 'audit_timeout', 'memory_mib'):
        if getattr(args, name) is not None and command[0] == 'verify':
            command.extend(['--' + name.replace('_', '-'), str(getattr(args, name))])
    if args.memory_guard is not None and command[0] == 'verify':
        command.append('--memory-guard' if args.memory_guard else '--no-memory-guard')
    raise SystemExit(cli_main(command))


if __name__ == '__main__':
    main()
