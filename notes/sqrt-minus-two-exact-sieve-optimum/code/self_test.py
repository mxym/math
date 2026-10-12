#!/usr/bin/env python3
"""Small independent negative controls for the six-level exact verifier.

These controls intentionally do not re-run the expensive full six-layer audit.
Both ordinary Python and Python -O must reject the malformed inputs.
"""
import check_exact as C


def reject(label,fn):
    try:fn()
    except (ValueError,TypeError,KeyError):print('REJECTED:',label)
    else:raise RuntimeError('tampering went undetected: '+label)


def check_final_threshold_enforced():
    prev_moduli=C.MODULI;prev_target=C.TARGET
    C.MODULI=(2,);C.TARGET=0
    try:
        stat={'shift':[0],'large':[0],'peak':[0],'witness':None}
        C.scan_one_parent(0,[(0,0),(1,0)],stat)
    finally:
        C.MODULI=prev_moduli;C.TARGET=prev_target

if __name__=='__main__':
    groups,closure=C.pinned_inputs()
    old=C.PARENT_SHA
    C.PARENT_SHA='0'*64
    try:reject('wrong complete-parent hash',C.pinned_inputs)
    finally:C.PARENT_SHA=old
    reject('missing new exceptional prime',lambda:C.verify_extra_prime_factors(
        [p for p in closure if p!=[7,3]]))
    reject('duplicate component vertex',lambda:C.adjacency([(0,0),(0,0)]))
    reject('oversized last-stage component',check_final_threshold_enforced)
    e=C.adjacency([(0,0),(1,0),(5,0)])
    seen=sorted(len(part) for part in C.components_of([0,1,2],e))
    C.demand(seen==[1,2],'BFS missed an adjacency')
    seen=sorted(len(part) for part in C.components_of([0,2],e))
    C.demand(seen==[1,1],'BFS ignored vertex deletion')
    print('ALL NEGATIVE AND CONNECTIVITY CONTROLS PASSED')
