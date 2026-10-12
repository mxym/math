#!/usr/bin/env python3
"""Reproduce the historical schema weakness and its public-derivative fix."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import check_cubic_certificate as public_f6
import check_rank_one_f8_certificate as public_f8
import independent_check as independent


def mutations(data):
    cases = []
    def add(name, change):
        changed = copy.deepcopy(data)
        change(changed)
        cases.append((name, changed))
    add('boolean_allowed_state', lambda d: d['allowed_states'].__setitem__(0, True))
    add('float_norm', lambda d: d['generator_norms'].__setitem__(0, 2.0))
    add('float_allowed_count', lambda d: d['summary'].__setitem__('allowed_count', float(d['summary']['allowed_count'])))
    return cases


def main():
    report = {'schema': 'all arithmetic metadata must be exact JSON integers', 'certificates': []}
    for filename, variant, public in [
        ('cubic_f6_certificate.json', 'F6', public_f6),
        ('cubic_rank_one_f8_certificate.json', 'F8', public_f8),
    ]:
        raw = (ROOT / filename).read_bytes()
        data = json.loads(raw)
        cases = mutations(data)
        accepted_historically = []
        with tempfile.TemporaryDirectory(prefix='cubic-original-checkers-') as tmp:
            tmp = Path(tmp)
            for script in ('check_cubic_certificate.py', 'check_rank_one_f8_certificate.py'):
                (tmp / script).write_bytes((ROOT / 'original-verifiers' / script).read_bytes())
            code = "import json,sys; import " + ('check_cubic_certificate' if variant == 'F6' else 'check_rank_one_f8_certificate') + " as checker; checker.verify(json.load(sys.stdin))"
            for name, corrupt in cases:
                outcome = subprocess.run([sys.executable, '-B', '-c', code],
                    input=json.dumps(corrupt).encode(), capture_output=True, cwd=tmp,
                    env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
                if outcome.returncode != 0:
                    raise ValueError('historical control unexpectedly failed: ' + name)
                accepted_historically.append(name)
        rejected_public = []
        rejected_independent = []
        for name, corrupt in cases:
            for checker, rejected in [(public.verify, rejected_public),
                    (lambda d: independent.verify(d, variant), rejected_independent)]:
                try:
                    checker(corrupt)
                except (ValueError, KeyError, TypeError):
                    rejected.append(name)
                else:
                    raise ValueError('strict checker accepted metadata corruption: ' + name)
        report['certificates'].append({'variant': variant,
            'original_author_checker_accepted': accepted_historically,
            'public_author_derivative_rejected': rejected_public,
            'independent_checker_rejected': rejected_independent})
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
