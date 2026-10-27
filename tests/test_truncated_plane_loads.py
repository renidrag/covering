"""Integration boundaries for the abstract truncated-plane component."""
import unittest
from workflow_fixtures import audit


class TruncatedPlaneLoads(unittest.TestCase):
    def test_only_small_incidence_interfaces_are_imported(self):
        graph = audit.SourceGraph()
        root = 'CoveringDesigns.TruncatedPlaneLoads'
        allowed = {
            audit.source('CoveringDesigns.' + name) for name in (
                'Foundations.Basic', 'Foundations.Intersecting',
                'Foundations.Relabelling', 'Foundations.StandardAxioms',
                'Multicover.Basic')
        }
        for path in graph.closure(root):
            self.assertTrue(path in allowed or 'TruncatedPlaneLoads' in path.parts
                            or path.name == 'TruncatedPlaneLoads.lean', path)
        real = graph.closure(root + '.Converse')
        for part in ('Integer', 'Covering', 'Actual', 'Examples'):
            self.assertNotIn(audit.source(root + '.' + part), real)

    def test_retained_control_transcription(self):
        from check_truncated_plane_loads import check
        check()


if __name__ == '__main__':
    unittest.main()
