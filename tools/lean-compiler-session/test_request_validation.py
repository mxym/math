"""Regression tests: expanded valid closures and rejected malformed requests."""
import unittest
from request_validation import validate_request, MAX_MODULES

class RequestValidation(unittest.TestCase):
    def test_more_than_old_cap_is_valid(self):
        modules = [f'Proof.M{i}' for i in range(220)]
        validate_request({'serial': 1, 'modules': modules,
                          'files': {m.replace('.', '/')+'.lean': '-- valid\n' for m in modules}})

    def test_limits_and_paths(self):
        invalid = [None, {'serial': -1}, {'serial': True},
            {'serial': 1, 'files': {'../escape.lean': ''}},
            {'serial': 1, 'files': {'/absolute.lean': ''}},
            {'serial': 1, 'files': {'A.lean': 4}},
            {'serial': 1, 'files': {'A.lean': 'a'*300001}},
            {'serial': 1, 'modules': ['Bad;command']},
            {'serial': 1, 'modules': ['A', 'A']},
            {'serial': 1, 'modules': [f'A{i}' for i in range(MAX_MODULES+1)]}]
        for request in invalid:
            with self.subTest(request_type=str(type(request))):
                with self.assertRaises(ValueError):
                    validate_request(request)

    def test_recovery_after_invalid(self):
        with self.assertRaises(ValueError):
            validate_request({'serial': 2, 'modules': ['../bad']})
        validate_request({'serial': 3, 'modules': ['A'], 'files': {'A.lean': ''}})
        validate_request({'serial': 4, 'stop': True})

if __name__ == '__main__':
    unittest.main()
