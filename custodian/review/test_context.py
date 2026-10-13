"""Complete-context transport checks; independent technical review is separate."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('review_transport', Path(__file__).with_name('review.py'))
R = importlib.util.module_from_spec(spec)
spec.loader.exec_module(R)

class ContextTest(unittest.TestCase):
    def test_large_review_uses_one_complete_retrievable_snapshot(self):
        with tempfile.TemporaryDirectory() as tmp:
            prompt = Path(tmp) / 'prompt'
            prompt.write_text('governing prompt')
            seen = []
            def reviewer(p, requirements, change, explanation='', retrieval=None):
                self.assertIsNotNone(retrieval)
                self.assertEqual((retrieval / 'requirements.txt').read_text(), 'requirements' * 100)
                self.assertEqual((retrieval / 'change.txt').read_text(), 'complete changes' * 100)
                self.assertEqual((retrieval / 'explanation.txt').read_text(), 'untrusted')
                seen.append(retrieval)
                return {'outcome': 'no_blocking_finding', 'findings': [], 'checked': [], 'summary': 'transport'}, 'stub'
            with patch.object(R, 'BATCH_LIMIT', 100), patch.object(R, 'call_reviewer', reviewer):
                result, _ = R.review(prompt, 'requirements' * 100, ['complete changes' * 100], 'untrusted')
            self.assertEqual(result['outcome'], 'no_blocking_finding')
            self.assertEqual(len(seen), 1)
            self.assertFalse(seen[0].exists())

    def test_related_source_never_partitions_or_truncates(self):
        with tempfile.TemporaryDirectory() as tmp:
            base, head = Path(tmp)/'base', Path(tmp)/'head'
            base.mkdir(); head.mkdir()
            (head/'producer').write_text('producer' * 100)
            (head/'consumer').write_text('consumer' * 100)
            with patch.object(R, 'BATCH_LIMIT', 1):
                batch = R.review_batches(base, head, ['producer'], ['consumer'])
            self.assertEqual(len(batch), 1)
            self.assertIn('producer'*100, batch[0])
            self.assertIn('consumer'*100, batch[0])

if __name__ == '__main__':
    unittest.main()
