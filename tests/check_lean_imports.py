"""Compare scanner regressions with the pinned Lean parser and compiler.

Run separately from the fake-compiler workflow tests:
./covering run --name lean-import-syntax --timeout 180 -- python3 tests/check_lean_imports.py
All Lean probe files and outputs stay in a temporary directory.
"""
import json
from pathlib import Path
import subprocess
import tempfile

from test_imports import audit, header_cases, import_spellings


PARSER = r'''
import Lean
open Lean

def main (args : List String) : IO Unit := do
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile args[0]!)
  for entry in (← IO.ofExcept json.getArr?) do
    let name ← IO.ofExcept <| entry.getObjValAs? String "name"
    let source ← IO.ofExcept <| entry.getObjValAs? String "source"
    let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext source name)
    let imports := if messages.hasErrors then #[] else
      (Elab.headerToImports header).map fun i => i.module.toString (escape := false)
    IO.println <| Json.compress <| Json.mkObj [
      ("name", toJson name), ("imports", toJson imports),
      ("hasErrors", toJson messages.hasErrors)]
'''


def lean(*args):
    result = subprocess.run(['lake', '-d', 'lean', 'env', 'lean', *map(str, args)],
                            capture_output=True, text=True, timeout=30)
    if result.returncode != 0 or result.stderr:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout


def main():
    cases = header_cases()
    with tempfile.TemporaryDirectory(prefix='covering-import-syntax-') as directory:
        root = Path(directory)
        parser = root / 'ParseHeaders.lean'
        parser.write_text(PARSER)
        data = root / 'cases.json'
        data.write_text(json.dumps([{'name': name, 'source': source}
                                   for name, source, _ in cases]))
        parsed = [json.loads(line) for line in lean('--run', parser, data).splitlines()]
        assert len(parsed) == len(cases)
        for (name, source, expected), result in zip(cases, parsed):
            assert result['name'] == name and not result['hasErrors'], result
            actual = [module for module in result['imports']
                      if module.split('.')[0] in {'CoveringDesigns', 'Explorations'}]
            assert actual == expected == audit.project_imports(source), (name, result, expected)
        print(f'{len(cases)} header cases agree with Lean.Parser.parseHeader', flush=True)

        # Compile actual imports of the existing component, not just invented
        # module names. No proof modules or their compiled outputs are edited.
        spellings = import_spellings('CoveringDesigns.C11_5_2')
        compiled = 0
        probe = root / 'CompileImports.lean'
        for name in ('plain', 'line_comment', 'trailing_block', 'leading_block',
                     'nested_blocks', 'multiline', 'escaped', 'adjacent_escaped',
                     'crlf', 'prelude'):
            probe.write_text(spellings[name] + '\n')
            lean(probe)
            compiled += 1
        probe.write_text('import CoveringDesigns.Foundations.Bounds import CoveringDesigns.C11_5_2\n')
        lean(probe)
        compiled += 1

        # This valid Lean spelling aliases an existing file but must fail the
        # project's audit policy before namespace filtering can discard it.
        alias = 'import «CoveringDesigns/C11_5_2»'
        probe.write_text(alias + '\n')
        lean(probe)
        try:
            audit.project_imports(alias)
        except ValueError:
            pass
        else:
            raise AssertionError('Escaped path alias bypassed the scanner')
        print(f'{compiled} ordinary import forms compiled; escaped path alias compiled and was rejected by the scanner',
              flush=True)


if __name__ == '__main__':
    main()
