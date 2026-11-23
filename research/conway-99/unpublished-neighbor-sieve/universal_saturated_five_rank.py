#!/usr/bin/env python3
"""Integer-only checks for two exceptional partitions in the universal 5-current dimension bound."""
from collections import Counter
import numpy as np
from connected_saturated_five_rank import ks,cyc,diag,survivors
from eight_tail_five_code import wlab,f2

def main():
    c8=Counter(); profiles=[]
    for K in ks(8):
        Z,v=diag(cyc(K)[1]);b=v.count(0);c8[b]+=1
        if b!=1: continue
        profiles.append(v[-2])
        assert v[-2]==2
    assert c8=={0:14,1:4,2:1} and len(profiles)==4
    c10=Counter(); planes=0; specials=[]
    for K in ks(10):
        _,v=diag(cyc(K)[1]);b=v.count(0);c10[b]+=1
        if b<2:continue
        specials.append(v);W=wlab(K)
        for Y in survivors(K,3):
            assert not f2(Y,W)
            planes+=1
    assert c10=={0:59,1:21,2:1}
    assert specials==[(1,1,1,2,0,0)] and planes==12
    print('Connected 8-tail radical census:',sorted(c8.items()),'and one-dimensional radical quotient determinant representatives:',sorted(profiles))
    print('Connected 10-tail census:',sorted(c10.items()),'exceptional diagonal',specials,'rank-three F2 contradictions',planes)

if __name__=='__main__':main()
