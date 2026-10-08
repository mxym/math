#!/usr/bin/env python3
"""Deliberately mutate actual certificate data; all mutations must be rejected."""
import contextlib
import copy
import io
import json
import check_exact as chk


def must_reject(label,data,change):
    altered=copy.deepcopy(data)
    change(altered)
    with contextlib.redirect_stdout(io.StringIO()):
        try:chk.check(altered,exhaustive=False)
        except (ValueError,KeyError,TypeError):pass
        else:raise RuntimeError('FAILED TO REJECT: '+label)
    print('REJECTED:',label)


if __name__=='__main__':
    data=json.loads((chk.HERE/'certificate.json').read_text())
    must_reject('positive component deletion',data,
                lambda z:z['positive_components'][0].pop())
    must_reject('duplicate positive vertex',data,
                lambda z:z['positive_components'][0].append(z['positive_components'][0][0]))
    must_reject('exceptional closure deletion',data,
                lambda z:z['exceptional_closure'].pop())
    must_reject('wrong exceptional point',data,
                lambda z:z['exceptional_closure'][0].__setitem__(0,999))
    must_reject('missing maximal failure proof',data,
                lambda z:z['maximal_failure_cycles'].pop())
    must_reject('shortened voltage cycle',data,
                lambda z:z['maximal_failure_cycles'][0]['steps'].pop())
    must_reject('wrong omitted ideal',data,
                lambda z:z['maximal_failure_cycles'][1]['missing'].__setitem__(0,2))
    must_reject('missing smaller period',data,
                lambda z:z['lower_period_cycles'].pop())
    must_reject('invalid intermediate step',data,
                lambda z:z['maximal_failure_cycles'][2]['steps'].__setitem__(0,0))
    for p,expected in [((0,0),False),((1,0),False),((2,0),False),
                       ((0,1),True),((1,1),True),((1,-1),True),
                       ((3,1),True),((3,2),True),((3,-2),True),
                       ((2,1),False),((4,0),False),((3,0),False)]:
        chk.require(chk.exact_irreducible(p)==expected,'irreducible predicate error '+str(p))
    print('ALL TAMPER TESTS PASSED')
