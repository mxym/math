#!/usr/bin/env python3
"""Adversarial certificate controls: reject bad source, constants and split maximum."""
from fractions import Fraction as F
from pathlib import Path
import tempfile
import check_depth2 as verifier


def reject(name,change,action,restore):
    change()
    try:
        try:
            action()
        except RuntimeError as exc:
            print('REJECTED '+name+': '+str(exc)[:160])
        else:
            raise RuntimeError('corrupt certificate incorrectly accepted: '+name)
    finally:
        restore()


if __name__=='__main__':
    oldpi=verifier.PI_LO
    reject('false pi enclosure',lambda:setattr(verifier,'PI_LO',F(22,7)),
           verifier.check_analytic_tails,
           lambda:setattr(verifier,'PI_LO',oldpi))
    oldq=verifier.Q5
    reject('corrupted depth-one optimum',lambda:setattr(verifier,'Q5',F(1)),
           verifier.check_analytic_tails,
           lambda:setattr(verifier,'Q5',oldq))
    oldhash=verifier.NEW_HASH
    reject('changed parent Pareto data',lambda:setattr(verifier,'NEW_HASH','0'*64),
           verifier.pinned_two_layer_states,
           lambda:setattr(verifier,'NEW_HASH',oldhash))
    with tempfile.TemporaryDirectory() as tmp:
        lines=verifier.FIN.read_text().splitlines()
        items=lines[1].split('\t')
        items[-1]='2' # First split (r,s)=(1,1) really has Q=1.
        lines[1]='\t'.join(items)
        bad=Path(tmp)/'corrupted_finite.tsv'
        bad.write_text('\n'.join(lines)+'\n')
        reject('false finite split rational maximum',lambda:None,
               lambda:verifier.check_all_finite_pairs(path=bad),lambda:None)
    print('PASS: all four hostile proof-data controls rejected')
