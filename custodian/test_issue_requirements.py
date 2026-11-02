"""Issue-context boundary checks; no live GitHub access or acceptance claim."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import issue_requirements as I
from controller import Controller


def issue(number=24, count=0):
    return {'id': number, 'number': number, 'html_url': I.WEB + str(number),
            'title': 'Fixed mathematical obligation', 'body': 'Actual issue body',
            'user': {'login': 'owner'}, 'created_at': 't0', 'updated_at': 't1', 'comments': count}


def comment(identifier, number=24):
    return {'id': identifier, 'html_url': I.WEB + str(number) + '#issuecomment-' + str(identifier),
            'issue_url': I.API + str(number), 'body': 'Actual comment ' + str(identifier),
            'user': {'login': 'owner'}, 'created_at': 't0', 'updated_at': 't1'}


class PointerRevision:
    commit = '1' * 40
    def files(self):
        return ['AGENTS.md']
    def read(self, path):
        return b'Local prose must never become the requirement.\n[Owner](https://github.com/dzackgarza/lean-cas-dsl/issues/24)\n'


class IssueRequirementsTest(unittest.TestCase):
    def test_all_pages_and_authorship_are_kept_without_local_prose(self):
        responses = [issue(count=101), [comment(i) for i in range(100)], [comment(100)]]
        with patch.object(I, 'fetch_json', side_effect=responses) as fetch:
            documents = I.load_documents(I.revision_pointers(PointerRevision()))
        self.assertEqual(fetch.call_args_list[-1].args[0], I.API + '24/comments?per_page=100&page=2')
        snapshot = json.loads(documents[I.WEB + '24'])
        self.assertEqual(len(snapshot['comments']), 101)
        self.assertEqual(snapshot['comments'][-1]['user']['login'], 'owner')
        self.assertIn('Actual issue body', I.render_documents(documents))
        self.assertNotIn('Local prose', I.render_documents(documents))

    def test_absent_unavailable_or_incomplete_context_never_falls_back(self):
        with self.assertRaises(ValueError):
            I.load_documents({'plan': '`b0-authority` copied local rules'})
        pointers = I.revision_pointers(PointerRevision())
        with patch.object(I, 'fetch_json', side_effect=OSError('GitHub unavailable')):
            with self.assertRaisesRegex(OSError, 'GitHub unavailable'):
                I.load_documents(pointers)
        with patch.object(I, 'fetch_json', side_effect=[issue(count=1), []]):
            with self.assertRaisesRegex(ValueError, 'incomplete'):
                I.load_documents(pointers)

    def test_worker_gets_only_explicit_role_sources_never_review_discussions(self):
        class NoReviewAccess(PointerRevision):
            def files(self):
                raise AssertionError('worker dispatch must not read global review pointers')
        for role, repository in (('formalization', 'lean-categories'), ('leaf', 'lean-cas-dsl-leaf-contracts')):
            url = 'https://github.com/dzackgarza/' + repository + '/issues/7#issuecomment-123'
            api = 'https://api.github.com/repos/dzackgarza/' + repository + '/issues/'
            selected = dict(comment(123), html_url=url, issue_url=api + '7', body='Independent role requirement')
            accepted = dict.fromkeys(('mathematics', 'contract', 'acceptance', 'public_metadata'), object())
            controller = Controller(NoReviewAccess(), accepted, Path('unused'), 'unused',
                                    {'existing-assignment': {'role': role, 'sources': [url]}})
            with patch.object(I, 'fetch_json', return_value=selected) as fetch:
                worker = controller.assign('existing-assignment')
            fetch.assert_called_once_with(api + 'comments/123')
            self.assertIn(b'Independent role requirement', worker.assignment.requirement)
            self.assertNotIn(b'Actual issue body', worker.assignment.requirement)
            self.assertNotIn(b'Local prose', worker.assignment.requirement)
            self.assertEqual(worker.assignment.role, role)
            with self.assertRaises(KeyError):
                controller.assign('unassigned')

    def test_legacy_or_missing_assignment_source_fails_before_any_fetch(self):
        for entry in ('leaf', {'role': 'leaf', 'sources': []}, {'role': 'formalization'}):
            controller = Controller(PointerRevision(), {}, Path('unused'), 'unused', {'assigned': entry})
            with patch.object(I, 'fetch_json', side_effect=AssertionError('no fallback source')):
                with self.assertRaisesRegex(ValueError, 'independently supplied'):
                    controller.assign('assigned')

    def test_prompt_is_exact_captured_comment_and_missing_comment_fails(self):
        with patch.object(I, 'fetch_json', side_effect=[issue(count=1), [comment(12)]]):
            documents = I.load_documents(I.revision_pointers(PointerRevision()))
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pointer = root / 'prompt.md'
            pointer.write_text('[Prompt](' + I.WEB + '24#issuecomment-12)\n')
            with patch.object(I, 'fetch_json', side_effect=AssertionError('must reuse captured discussion')):
                prompt = I.materialize_prompt(pointer, documents, root / 'out')
            self.assertEqual(prompt.read_text(), 'Actual comment 12')
            pointer.write_text('[Prompt](' + I.WEB + '24#issuecomment-13)\n')
            with self.assertRaises(ValueError):
                I.materialize_prompt(pointer, documents, root / 'missing')

    def test_issue_comment_changes_request_identity(self):
        assignments = {'assigned': {'role': 'kernel', 'sources': [I.WEB + '24#issuecomment-1']}}
        first = Controller(PointerRevision(), {}, Path('unused'), 'unused', assignments)
        with patch.object(I, 'fetch_json', side_effect=[comment(1), issue(count=1), [comment(1)]]):
            request = first.request('assigned', {}, {})
        self.assertEqual(request['assignment'], assignments['assigned'])
        edited = comment(1)
        edited['body'] = 'Corrected obligation'
        second = Controller(PointerRevision(), {}, Path('unused'), 'unused', assignments)
        with patch.object(I, 'fetch_json', side_effect=[edited, issue(count=1), [edited]]):
            newer = second.request('assigned', {}, {})
        self.assertNotEqual(request['request_id'], newer['request_id'])
        with self.assertRaisesRegex(ValueError, 'revision-derived snapshot'):
            second.advance(request, Path('unused'), Path('unused'))


if __name__ == '__main__':
    unittest.main()
