#!/usr/bin/env python3
"""Adversarial controls for the nonnegative-power dual and binary-tail no-go."""
from fractions import Fraction as F
import check as A
import check_binary_tail as B


def rejects(label,mod,name,replacement,callback):
    old=getattr(mod,name)
    try:
        setattr(mod,name,replacement)
        try:
            callback()
        except RuntimeError as e:
            print('REJECTED '+label+': '+str(e)[:140])
        else:
            raise RuntimeError('corrupted certificate accepted: '+label)
    finally:
        setattr(mod,name,old)


if __name__=='__main__':
    rejects('too-large claimed dual floor',A,'T_FLOOR',F(1,20),A.weighted_log_bound)
    rejects('corrupted all-degree dual weights',A,'WEIGHTS',(F(1),F(1),F(1)),
            lambda: [A.require(A.dual_column(2*k)<1,'dual column') for k in range(1,7)])
    rejects('false binomial sample geometry',A,'SAMPLES',((5,F(6)),(13,F(10)),(36,F(1))),
            A.audit_attainable_sample_states)
    rejects('false rational pi lower bound',B,'PI_LO',F(22,7),B.pi_check)
    rejects('false exact binary orbit improvement threshold',B,'G_bounds',(lambda d,*args:(F(0),F(0))),B.check)
    print('PASS: all five hostile corruptions rejected')
