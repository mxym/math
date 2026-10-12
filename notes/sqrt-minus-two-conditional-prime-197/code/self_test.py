#!/usr/bin/env python3
"""Adversarial exact-certificate rejection for conditional prime-polynomial reduction.

These tests do not rely on or assume Schinzel's Hypothesis H.
"""
import contextlib
import copy
import io
import json
import check_polynomials as C


def reject(label,original,edit):
    damaged=copy.deepcopy(original)
    edit(damaged)
    with contextlib.redirect_stdout(io.StringIO()):
        try:C.verify(damaged)
        except (ValueError,TypeError,KeyError):pass
        else:raise RuntimeError('malformed certificate was accepted: '+label)
    print('REJECTED:',label)


if __name__=='__main__':
    data=json.loads((C.DIR/'schinzel_affine_family.json').read_text())
    reject('missing small prime',data,
           lambda d:d['prime_local_shifts'].pop())
    reject('wrong prime index',data,
           lambda d:d['prime_local_shifts'][0].__setitem__(0,4))
    reject('inconsistent CRT horizontal coordinate',data,
           lambda d:d.update(horizontal_offset=str(int(d['horizontal_offset'])+1)))
    reject('inconsistent CRT vertical coordinate',data,
           lambda d:d.update(vertical_offset=str(int(d['vertical_offset'])+1)))
    reject('incorrect full modulus',data,
           lambda d:d.update(modulus=str(int(d['modulus'])*2)))
    reject('potentially reducible quadratic specialization',data,
           lambda d:d.update(vertical_offset='0'))
    reject('wrong form count',data,
           lambda d:d.update(number_of_forms=198))
    print('ALL CONDITIONAL-CERTIFICATE MUTATION TESTS PASSED')
