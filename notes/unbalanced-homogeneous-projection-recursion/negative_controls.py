#!/usr/bin/env python3
"""Smoke-test that obviously false parameter changes are rejected.

These adversarial tests are *not* independent mathematical verification.
"""
from fractions import Fraction as F
import checker


def rejected(name, attribute, corrupt):
    original = getattr(checker, attribute)
    try:
        setattr(checker, attribute, corrupt)
        try:
            checker.main()
        except RuntimeError as exc:
            print(f'REJECTED {name}: {str(exc)[:100]}')
        else:
            raise RuntimeError(f'negative control ACCEPTED: {name}')
    finally:
        setattr(checker, attribute, original)


if __name__ == '__main__':
    rejected('false pi lower bound', 'PI_LO', F(22, 7))
    rejected('false winning benchmark', 'RATE_LO', F(2))
    rejected('overstrong 1.040 competitor ceiling', 'THRESH', F(26, 25))
    print('PASS: all three negative controls were rejected')
