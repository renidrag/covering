"""C18 registration, isolation and witness integrity; no mathematical claims."""
from pathlib import Path
import json
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import audit_library as audit


class C18103Integration(unittest.TestCase):
    def sources(self):
        return [audit.source("CoveringDesigns.C18_10_3"),
                *sorted((audit.ROOT / "CoveringDesigns/C18_10_3").glob("*.lean")),
                *[audit.source("CoveringDesigns." + p) for p in (
                    "BoundaryRank.RestrictedEquality", "BoundaryRank.SquareDuality",
                    "Foundations.SupportObstruction", "Foundations.SupportDifferences",
                    "Foundations.PairedSupportObstruction",
                    "Foundations.IncidencePacking")]]

    def test_every_public_theorem_has_full_contract_and_axiom_guard(self):
        names = set()
        for path in self.sources():
            stack = []
            for line in path.read_text().splitlines():
                if line.startswith("namespace "):
                    stack.append(line.split()[1])
                elif line.startswith("end "):
                    stack.pop()
                match = re.match(r"(?:@\[[^]]+\] )?theorem ([\w']+)", line)
                if match:
                    names.add(".".join(stack + [match[1]]))
        self.assertEqual(set(audit.COMPONENTS["18-10-3"]["theorems"]), names)
        text = audit.audit_source("18-10-3").read_text()
        for name in names:
            with self.subTest(theorem=name):
                if name == "CoveringDesigns.C18_10_3.core_equality":
                    contract = text.split("theorem core_equality_explicit", 1)[1].split(
                        "end CoveringDesigns.Audit18_10_3", 1)[0]
                    for premise in ("hl : Fintype.card ι = 16", "hb : Fintype.card κ = 11",
                                    "hrow :", "htotal : ∑ i, δ i = 18", "hgram :"):
                        self.assertIn(premise, contract)
                    self.assertIn("R.rank = 11 := by", contract)
                    self.assertIn("exact C18_10_3.core_equality R E δ hl hb hs hn hz hrow htotal hgram", contract)
                    self.assertIn("#guard_standard_axioms CoveringDesigns.Audit18_10_3.core_equality_explicit", text)
                else:
                    self.assertRegex(text, r"#check \(@" + re.escape(name) + r"\s*:")
                self.assertIn("#guard_standard_axioms " + name, text)
                self.assertIn("#print axioms " + name, text)
        self.assertIn("∃ C : Finset (Finset α)", text)
        self.assertIn("∀ T : Finset α, T.card = 3 → ∃ B ∈ C, T ⊆ B", text)

    def test_established_components_remain_independent(self):
        new = set(self.sources())
        for key, info in audit.COMPONENTS.items():
            if key not in ("18-10-3", "c18103-lifts"):
                with self.subTest(component=key):
                    self.assertFalse(audit.closure(info["entry"]) & new)
        paths = audit.closure("CoveringDesigns.C18_10_3")
        for key, info in audit.COMPONENTS.items():
            if key not in ("18-10-3", "c18103-lifts"):
                self.assertNotIn(audit.source(info["entry"]), paths)
        for name in ("BoundaryRank.Completion", "BoundaryRank.BinaryCompletion",
                     "C20_11_3.LowerBound", "C20_11_3.Witness"):
            self.assertNotIn(audit.source("CoveringDesigns." + name), paths)

    def test_covering_route_excludes_square_but_audit_retains_it(self):
        square = audit.source("CoveringDesigns.BoundaryRank.SquareDuality")
        retained = audit.source("CoveringDesigns.C18_10_3.SquareSupport")
        for name in ("CoveringDesigns.C18_10_3", "CoveringDesigns.C18_10_3.LowerBound"):
            paths = audit.closure(name)
            self.assertNotIn(square, paths)
            self.assertNotIn(retained, paths)
            self.assertIn(audit.source("CoveringDesigns.Foundations.PairedSupportObstruction"), paths)
        paths = audit.closure(audit.COMPONENTS["18-10-3"]["entry"])
        self.assertIn(square, paths)
        self.assertIn(retained, paths)

    def test_historical_witness_integrity_and_transcription(self):
        audit.check_c18103_witness()
        with tempfile.TemporaryDirectory() as tmp:
            data = json.loads(Path("data/c18103-historical-witness.json").read_text())
            data["blocks_one_based"][0].reverse()
            path = Path(tmp) / "witness.json"
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(AssertionError, "ordered block bytes"):
                audit.check_c18103_witness(data_path=path)
            source = audit.source("CoveringDesigns.C18_10_3.Witness").read_text()
            lean = Path(tmp) / "Witness.lean"
            lean.write_text(source.replace("{0, 1, 2, 3, 4, 9", "{0, 1, 2, 3, 5, 9", 1))
            with self.assertRaisesRegex(AssertionError, "Lean transcription"):
                audit.check_c18103_witness(lean_path=lean)


if __name__ == "__main__":
    unittest.main()
