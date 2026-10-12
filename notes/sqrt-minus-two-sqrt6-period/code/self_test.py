#!/usr/bin/env python3
"""Deliberate tamper tests; no Python assertions or nonstandard packages."""
import copy
import contextlib
import io
import json
import check_exact as C


def rejected(label,verify,obj,edit):
    damaged=copy.deepcopy(obj)
    edit(damaged)
    with contextlib.redirect_stdout(io.StringIO()):
        try:verify(damaged)
        except (ValueError,TypeError,KeyError):pass
        else:raise RuntimeError('tampering not detected: '+label)
    print('REJECTED:',label)


if __name__=='__main__':
    neg=C.load('lower_cycles.json.gz')
    pos=C.load('positive_q1122.json.gz')
    exc=json.loads((C.HERE/'exceptional_closure.json').read_text())
    rejected('missing lower period',C.check_all_negative,neg,
             lambda d:d.pop())
    rejected('broken q=1 voltage path',C.check_all_negative,neg,
             lambda d:d[0]['steps'].pop())
    rejected('out-of-range negative move',C.check_all_negative,neg,
             lambda d:d[1]['steps'].__setitem__(0,99))
    rejected('missing quotient vertex',C.check_positive,pos,
             lambda d:d['components'][0].pop())
    rejected('duplicate quotient point',C.check_positive,pos,
             lambda d:d['components'][0].append(d['components'][0][0]))
    rejected('missing exceptional vertex',C.check_exceptional_closure,exc,
             lambda d:d.pop())
    rejected('false exceptional primality',C.check_exceptional_closure,exc,
             lambda d:d[0].__setitem__(0,999))
    for p,want in [((0,0),False),((1,0),False),((0,1),True),
                   ((1,1),True),((3,1),True),((3,2),True),
                   ((4,0),False),((6,0),False),((2,1),False)]:
        C.require(C.exact_irreducible(p)==want,
                  'incorrect trial-factor primality '+str(p))
    print('ALL TAMPER TESTS PASSED')
