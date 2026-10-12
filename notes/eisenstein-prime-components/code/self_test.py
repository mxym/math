#!/usr/bin/env python3
"""Deliberate corruption tests of independently loaded certificate data."""
import contextlib
import copy
import io

import check


def expect_failure(label, target, modifier, verifier):
    original = check.filedata

    def corrupted(name):
        data = original(name)
        if name == target:
            data = copy.deepcopy(data)
            modifier(data)
        return data

    check.filedata = corrupted
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            try:
                verifier()
            except ValueError:
                pass
            else:
                raise RuntimeError(f'{label}: tampering went undetected')
        print(f'TAMPER REJECTED: {label}')
    finally:
        check.filedata = original


if __name__ == '__main__':
    expect_failure(
        'empty negative walk',
        'lower_cycles_1_180.json.gz',
        lambda data: data[0].update(steps=[]),
        check.check_negative,
    )
    expect_failure(
        'negative walk modified displacement',
        'lower_cycles_1_180.json.gz',
        lambda data: data[1]['steps'].append(6),
        check.check_negative,
    )
    expect_failure(
        'missing endpoint vertex',
        'endpoint_63.json.gz',
        lambda data: data['components'][0].pop(),
        lambda: check.check_endpoint(63, 93312, 16536, 74),
    )
    expect_failure(
        'missing exceptional-closure vertex',
        'exceptional_closure_6.json.gz',
        lambda data: data['points'].pop(),
        lambda: check.check_closure(6, 6, check.UNIT_STEPS, 54, 48),
    )
    expect_failure(
        'invalid composite replacement walk',
        'composite_replacement_cycles.json.gz',
        lambda data: data[0]['steps'].append(6),
        check.check_composite_rigidity,
    )
    for prime, yes in [((2,0), True), ((3,1), True),
                       ((4,1), True), ((3,0), False), ((0,0), False)]:
        got = check.irreducible_by_divisors(prime)
        check.demand(got == yes, f'wrong primality on {prime}')
    print('ALL TAMPER AND IRREDUCIBILITY TESTS PASSED')
