#!/usr/bin/env python3
"""Regression tests for fail-closed source inventory checks, not Lean proofs."""
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from preflight import check_inventory
from reproduce import ROOT, strip_comments


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='gaussian-four-inventory-')
        self.root = Path(self.tmp.name) / 'formalizations/gaussian-four-global-progress'
        for relative in json.loads((ROOT / 'SOURCE_BLOBS.json').read_text()):
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, target)

    def tearDown(self):
        self.tmp.cleanup()

    def test_valid_inventory(self):
        self.assertEqual(check_inventory(self.root, strip_comments)['status'], 'PASS')

    def test_unlisted_owned_source_rejected(self):
        (self.root / 'GaussianFour/Unlisted.lean').write_text('import GaussianFour.Profile\n')
        with self.assertRaisesRegex(RuntimeError, 'Unlisted owned Lean'):
            check_inventory(self.root, strip_comments)

    def test_unknown_owned_import_rejected(self):
        path = self.root / 'GaussianFour.lean'
        path.write_text(path.read_text() + '\nimport GaussianFour.MissingProof\n')
        with self.assertRaisesRegex(RuntimeError, 'Unlisted owned import'):
            check_inventory(self.root, strip_comments)

    def test_wrong_build_order_rejected(self):
        path = self.root / 'MODULES.json'
        modules = json.loads(path.read_text())
        path.write_text(json.dumps(dict(reversed(list(modules.items())))))
        with self.assertRaisesRegex(RuntimeError, 'Build order'):
            check_inventory(self.root, strip_comments)

    def test_audit_root_drift_rejected(self):
        path = self.root / 'ROOTS.txt'
        path.write_text('\n'.join(path.read_text().splitlines()[1:]) + '\n')
        with self.assertRaisesRegex(RuntimeError, 'disagree'):
            check_inventory(self.root, strip_comments)


if __name__ == '__main__':
    unittest.main()
