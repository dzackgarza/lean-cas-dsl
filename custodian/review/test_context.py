"""Complete-context transport checks; independent technical review is separate."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('review_transport', Path(__file__).with_name('review.py'))
R = importlib.util.module_from_spec(spec)
spec.loader.exec_module(R)

class ContextTest(unittest.TestCase):
    def test_large_review_uses_one_complete_retrievable_snapshot(self):
        requirements = 'requirements' * R.BATCH_LIMIT
        change = 'complete changes' * R.BATCH_LIMIT
        with R.materialized_context(requirements, change, 'untrusted') as retrieval:
            self.assertEqual((retrieval / 'requirements.txt').read_text(), requirements)
            self.assertEqual((retrieval / 'change.txt').read_text(), change)
            self.assertEqual((retrieval / 'explanation.txt').read_text(), 'untrusted')
            self.assertEqual({p.name for p in retrieval.iterdir()},
                             {'requirements.txt', 'change.txt', 'explanation.txt'})
        self.assertFalse(retrieval.exists())

    def test_related_source_never_partitions_or_truncates(self):
        with tempfile.TemporaryDirectory() as tmp:
            base, head = Path(tmp)/'base', Path(tmp)/'head'
            base.mkdir(); head.mkdir()
            (head/'producer').write_text('producer' * 100)
            (head/'consumer').write_text('consumer' * 100)
            batch = R.review_batches(base, head, ['producer'], ['consumer'])
            self.assertEqual(len(batch), 1)
            self.assertIn('producer'*100, batch[0])
            self.assertIn('consumer'*100, batch[0])

if __name__ == '__main__':
    unittest.main()
