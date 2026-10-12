#!/usr/bin/env python3
"""Verify that invalid log bounds, orbit constants and candidate data are rejected.

Each test introduces a deliberate in-memory corruption. No source/certificates
are modified; exceptions rather than Python 'assert' control acceptance.
"""
from fractions import Fraction as F
import check as A
import check_canonical_rational as B


def reject(name,module,attribute,replacement,callback):
    saved=getattr(module,attribute)
    try:
        setattr(module,attribute,replacement)
        try:
            callback()
        except RuntimeError as exc:
            print('REJECTED '+name+': '+str(exc)[:125])
        else:
            raise RuntimeError('corrupt input accepted: '+name)
    finally:
        setattr(module,attribute,saved)


if __name__=='__main__':
    reject('false pi lower bound',A,'PILO',F(22,7),A.check)
    reject('false binary orbit G5 bound',A,'G5_bounds',lambda:(F(1),F(2)),A.check)
    old_log=A.log_bounds
    reject('false required log upper enclosure',A,'log_bounds',
           lambda x:(F(0),F(2)) if F(x)==F(159,74) else old_log(x),A.check)
    reject('false original central-binomial multiplier',B,'comb',lambda n,k:1,B.check)
    reject('missing canonical infinite-series terms',B,'J',0,B.check)
    print('PASS: all five adversarial corruptions rejected')
