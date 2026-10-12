#!/usr/bin/env python3
"""Negative mutation tests. These must fail in normal and optimized Python."""
import contextlib
import copy
import io
import json

import check_exact as chk


def must_reject(label, data, edit):
    altered=copy.deepcopy(data)
    edit(altered)
    with contextlib.redirect_stdout(io.StringIO()):
        try:
            chk.check_certificate(altered,exhaustive=False)
        except (ValueError,KeyError,TypeError):
            pass
        else:
            raise RuntimeError('Tampering not rejected: '+label)
    print('REJECTED:',label)


if __name__=='__main__':
    with open(chk.HERE/'certificate.json',encoding='utf-8') as f:
        data=json.load(f)
    must_reject('missing positive vertex',data,
        lambda z:z['positive'][0]['components'][0].pop())
    must_reject('altered positive membership',data,
        lambda z:z['positive'][2]['components'][1][0].__setitem__(0,200))
    must_reject('shortened negative voltage',data,
        lambda z:z['maximal_failures'][0]['steps'].pop())
    must_reject('wrong maximal omitted pair',data,
        lambda z:z['maximal_failures'][1]['omitted'][0].__setitem__(0,2))
    must_reject('missing lower-period proof',data,
        lambda z:z['lower_periods'].pop())
    must_reject('forbidden intermediate negative step',data,
        lambda z:z['maximal_failures'][2]['steps'].__setitem__(0,0))
    for z,expected in [((0,0),False),((1,0),False),((0,1),True),
                       ((1,1),True),((3,1),True),((3,2),True),
                       ((2,0),False),((1,2),False),((6,0),False)]:
        chk.require(chk.irreducible(z)==expected,'irreducibility test '+str(z))
    print('ALL TAMPER TESTS PASSED')
