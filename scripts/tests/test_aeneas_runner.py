"""Focused orchestration regression; external provers are deliberately mocked."""
import json
from contextlib import ExitStack
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from aeneas_management import runner


class RegenerationTests(unittest.TestCase):
    def test_model_comparison_and_input_stability(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            profile = root / 'profile'
            profile.mkdir()
            (profile / 'generated').mkdir()
            (profile / 'generated/Model.lean').write_text('def checked := True\n')
            (profile / 'extract.json').write_text(json.dumps({'models': {'Model.lean': []}}))
            lean = root / 'lean'
            lean.mkdir()
            (lean / 'lakefile.toml').write_text('name = "fixture"\n')
            (root / 'source.lock.json').write_text('{}')
            config = {'target': 'test-host', 'extractions': [
                {'config': 'extract.json', 'models': {'Model.lean': 'generated/Model.lean'}}],
                'inventory': 'inventory.json', 'report': 'proofs.toml'}
            calls = []
            def run(argv, cwd, log, env):
                calls.append([str(a) for a in argv])
                if '--config' in argv:
                    output = Path(argv[argv.index('--output') + 1])
                    output.mkdir()
                    (output / 'Model.lean').write_text('def checked := True\n')
            with ExitStack() as stack:
                for name, value in {
                    'validate_runtime_environment': None, 'units': [],
                    'configuration': (profile, config, None),
                    'prepare': (root / 'tools', {'extraction_rust': 'fixture'}, lean),
                    'auxiliary_tools': [], 'fingerprint': {'input': 'stable'},
                    'commands': None,
                }.items():
                    stack.enter_context(patch.object(runner, name, return_value=value))
                stack.enter_context(patch.object(runner.tools, 'host', return_value='test-host'))
                stack.enter_context(patch.object(runner.tools, 'environment', return_value={}))
                stack.enter_context(patch.object(runner.tools, 'run', side_effect=run))
                stack.enter_context(patch.object(runner.source, 'check'))
                result = runner.verify(root, 'default')
            self.assertEqual(json.loads((result / 'result.json').read_text())['status'], 'passed')
            self.assertEqual((result / 'inputs-before.json').read_bytes(),
                             (result / 'inputs-after.json').read_bytes())
            self.assertTrue(any('--config' in c for c in calls))
            self.assertTrue(any('clean' in c for c in calls))
            self.assertTrue(any('--inventory' in c for c in calls))
