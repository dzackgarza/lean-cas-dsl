"""CI must inspect every original result, including nonfailing computation gaps."""

import copy
import unittest

from ci_kernel_candidate import check_fixed_controls, check_fixed_execution


class FixedExecutionTests(unittest.TestCase):
    def setUp(self):
        self.expected = {'original.one': {'file': '/fixed/one.cas'},
                         'original.two': {'file': '/fixed/two.cas'}}
        self.rows = [{'id': identity, 'file': source['file'], 'kind': 'holds',
                      'fails': False, 'question': 'complete question ' + identity,
                      'proposition': 'complete proposition ' + identity, 'dispatches': []}
                     for identity, source in self.expected.items()]

    def test_complete_original_results(self):
        self.assertEqual(check_fixed_execution(self.rows, self.expected), [])

    def test_zero_exit_nonfailing_gaps_are_not_completion(self):
        for kind in ['gap', 'unavailable', 'wrong', 'invalid', 'internal', 'malformed', 'ambiguous']:
            rows = copy.deepcopy(self.rows)
            rows[0].update(kind=kind, fails=False)
            self.assertTrue(check_fixed_execution(rows, self.expected), kind)

    def test_missing_duplicate_reordered_or_additional_results_fail(self):
        for rows in [[], self.rows[:1], self.rows + self.rows[:1], list(reversed(self.rows)),
                     [*self.rows, {'id': '(statement) failed binding', 'kind': 'internal'}]]:
            self.assertTrue(check_fixed_execution(rows, self.expected))

    def test_reading_source_and_dispatch_records_are_required(self):
        for key, value in [('file', '/different/source.cas'), ('question', ''),
                           ('proposition', None), ('dispatches', None), ('fails', True)]:
            rows = copy.deepcopy(self.rows)
            rows[0][key] = value
            self.assertTrue(check_fixed_execution(rows, self.expected), key)


class FixedControlTests(unittest.TestCase):
    def rx10(self):
        return {'observations': [
            {'condition': condition, 'expectedKind': condition, 'kind': condition,
             'id': 'original.rx10', 'source': 'original fixed source', 'sourceLine': 11,
             'question': 'complete original question', 'proposition': 'complete proposition',
             'sameIndependentTypedQuestion': True, 'callableReused': True,
             'sessionControls': {'kind': 'holds'}}
            for condition in ['holds', 'gap', 'unavailable', 'malformed', 'wrong', 'internal']]}

    def test_rx10_requires_all_six_exact_outcomes(self):
        document = self.rx10()
        self.assertEqual(check_fixed_controls('rx10', document), [])
        malformed = self.rx10()
        malformed['observations'].append(None)
        self.assertTrue(check_fixed_controls('rx10', malformed))
        for index in range(6):
            missing = self.rx10()
            missing['observations'].pop(index)
            self.assertTrue(check_fixed_controls('rx10', missing))
            wrong = self.rx10()
            wrong['observations'][index]['kind'] = 'different'
            self.assertTrue(check_fixed_controls('rx10', wrong))

    def test_rx10_cannot_hide_changed_question_or_unconsumed_callable(self):
        for index, key, value in [(1, 'question', 'changed'), (2, 'proposition', ''),
                                  (4, 'callableReused', False), (0, 'callableReused', False),
                                  (0, 'sessionControls', {'kind': 'internal'}),
                                  (3, 'sameIndependentTypedQuestion', False)]:
            document = self.rx10()
            document['observations'][index][key] = value
            self.assertTrue(check_fixed_controls('rx10', document), (index, key))

    def test_rx09_requires_the_original_admission_boundary(self):
        row = {'control': 'RX09', 'kind': 'invalid', 'stage': 'admission',
               'prerequisites': 4, 'dispatches': [],
               'actualAttempt': {'terms': []}, 'independentObligation': {'terms': []}}
        self.assertEqual(check_fixed_controls('rx09', [row]), [])
        for key, value in [('kind', 'internal'), ('stage', 'parse'), ('prerequisites', 3),
                           ('dispatches', [{}]), ('actualAttempt', None),
                           ('independentObligation', None)]:
            self.assertTrue(check_fixed_controls('rx09', [{**row, key: value}]), key)

    def test_rx05_rejects_incomplete_environment_and_typed_comparison_reports(self):
        self.assertTrue(check_fixed_controls('rx05', []))
        environments = [{'environment': name, 'selectedInventory': {}, 'typedReceiver': {},
                         'resolutionKind': 'resolved' if index < 2 else 'ambiguous',
                         'typedRequest': {}, 'candidates': [{}],
                         'registryApplicableCandidates': [{}], 'completeRegistryInventoryRetained': True}
                        for index, name in enumerate(['present', 'present-reversed', 'absent', 'absent-reversed'])]
        row = {'control': 'RX05', 'environments': environments, 'crossEnvironmentChecks': {
            'presentResolutionMetadataEqual': True, 'presentCompleteTypedRequestsEquivalent': True,
            'absentCompleteCandidatesEquivalentAsMultisets': True,
            'registryApplicableInventoriesEquivalentAsMultisets': True}}
        self.assertEqual(check_fixed_controls('rx05', [row]), [])
        malformed = copy.deepcopy(row)
        malformed['environments'].append(None)
        self.assertTrue(check_fixed_controls('rx05', [malformed]))
        for key in row['crossEnvironmentChecks']:
            bad = copy.deepcopy(row)
            bad['crossEnvironmentChecks'][key] = False
            self.assertTrue(check_fixed_controls('rx05', [bad]), key)
        bad = copy.deepcopy(row)
        bad['environments'][2]['candidates'] = []
        self.assertTrue(check_fixed_controls('rx05', [bad]))


if __name__ == '__main__':
    unittest.main()
