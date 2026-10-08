#!/usr/bin/env python3
"""Adversarial mutation tests for certified literal integer path checks."""
import copy
import json
import check


def reject(data,label,edit):
    damaged=copy.deepcopy(data)
    edit(damaged)
    try:check.check(damaged)
    except (ValueError,KeyError,TypeError):print('REJECTED:',label)
    else:raise RuntimeError('malformed certificate accepted: '+label)

if __name__=='__main__':
    original=json.loads((check.ROOT/'obstructions.json').read_text())
    reject(original,'missing prime obstruction',lambda d:d['prime_omissions'].pop())
    reject(original,'duplicate prime obstruction',lambda d:d['prime_omissions'][1].update(missing=0))
    reject(original,'invalid literal move',lambda d:d['prime_omissions'][0]['steps'].__setitem__(0,99))
    reject(original,'truncated period voltage',lambda d:d['prime_omissions'][2]['steps'].pop())
    reject(original,'altered ramified-square witness',lambda d:d['ramified_square']['steps'].pop())
    print('ALL NEGATIVE MUTATION TESTS PASSED')
