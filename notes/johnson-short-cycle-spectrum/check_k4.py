#!/usr/bin/env python3
"""Exact certificates for the S_n action on 4-sets, 11 <= n <= 25.

No optimizer / floating point / third-party modules. Support tuple (a,b,c,d)
denotes counts of cycles of lengths 1, 2, 3, 4; the remaining vertices
are either absent or form one cycle of length >= 5.
"""
from fractions import Fraction as Q
from math import factorial
from transfer import moment, short_types, test

# Literal rational basis specifications: two nonidentity positive supports,
# three negative supports; the identity is always the first positive support.
SUPPORTS = {
    11: (((0,1,3,0),(7,0,0,1)),((0,4,1,0),(4,0,1,1),(9,1,0,0))),
    12: (((0,0,4,0),(8,0,0,1)),((0,6,0,0),(4,0,0,2),(10,1,0,0))),
    13: (((0,0,3,1),(9,0,0,1)),((0,5,1,0),(4,0,3,0),(11,1,0,0))),
    14: (((0,1,4,0),(10,0,0,1)),((0,7,0,0),(5,0,3,0),(12,1,0,0))),
    15: (((0,0,5,0),(11,0,0,1)),((0,6,1,0),(6,0,3,0),(13,1,0,0))),
    16: (((0,0,4,1),(12,0,0,1)),((0,8,0,0),(6,0,2,1),(14,1,0,0))),
    17: (((0,0,4,0),(13,0,0,1)),((0,7,1,0),(6,0,1,2),(15,1,0,0))),
    18: (((0,0,6,0),(13,0,0,0)),((0,9,0,0),(6,0,4,0),(16,1,0,0))),
    19: (((0,0,5,1),(14,0,0,0)),((0,8,1,0),(7,0,4,0),(17,1,0,0))),
    20: (((0,0,5,0),(15,0,0,0)),((0,10,0,0),(8,0,4,0),(18,1,0,0))),
    21: (((0,0,7,0),(16,0,0,0)),((0,9,1,0),(8,0,3,1),(19,1,0,0))),
    22: (((0,0,6,1),(17,0,0,0)),((0,11,0,0),(8,0,2,2),(20,1,0,0))),
    23: (((0,0,6,0),(18,0,0,0)),((0,10,1,0),(9,0,2,2),(21,1,0,0))),
    24: (((0,0,8,0),(18,0,0,0)),((0,12,0,0),(9,0,5,0),(22,1,0,0))),
    25: (((1,0,8,0),(19,0,0,0)),((0,11,1,0),(10,0,5,0),(23,1,0,0))),
}
TARGETS = {
    11:'1629/4549', 12:'131/357', 13:'6817/18427', 14:'3106/8153',
    15:'1345/3493', 16:'3591/9187', 17:'29846/75821', 18:'211/523',
    19:'445133/1091945', 20:'4147/9871', 21:'352459/826455',
    22:'28029/64307', 23:'5926/13479', 24:'3441/7621', 25:'42843/94103',
}


def solve(A,b):
    """Gauss-Jordan over the rationals, raising if the basis is singular."""
    d=len(b)
    assert len(A)==d and all(len(row)==d for row in A)
    a=[[Q(v) for v in A[i]]+[Q(b[i])] for i in range(d)]
    for j in range(d):
        pivot=next(i for i in range(j,d) if a[i][j])
        a[j],a[pivot]=a[pivot],a[j]
        factor=a[j][j]
        a[j]=[u/factor for u in a[j]]
        for i in range(d):
            if i!=j:
                factor=a[i][j]
                a[i]=[a[i][h]-factor*a[j][h] for h in range(d+1)]
    return [a[i][-1] for i in range(d)]


def class_size(n,t):
    r=n-sum(j*a for j,a in enumerate(t,1))
    assert r==0 or r>=5
    denominator=1
    for j,a in enumerate(t,1):
        denominator *= j**a*factorial(a)
    if r: denominator *= r  # one residual r-cycle
    assert factorial(n)%denominator==0
    return factorial(n)//denominator


def certify(n):
    identity=(n,0,0,0)
    P=(identity,)+SUPPORTS[n][0]
    M=SUPPORTS[n][1]
    assert len(set(P+M))==6 and identity not in M
    B=[]
    for t in P:
        f=moment(n,4,t)
        B.append([1,0,*f[:4]])
    for t in M:
        f=moment(n,4,t)
        B.append([0,1,*(-v for v in f[:4])])
    weights=solve(list(zip(*B)),[1,1,0,0,0,0])
    dual=solve(B,[1,0,0,0,0,0])
    assert all(w>0 for w in weights)
    assert sum(weights[:3])==sum(weights[3:])==1
    C=Q(TARGETS[n])
    assert weights[0]==dual[0]+dual[1]==C
    low,high=-dual[1],dual[0]
    assert high-low==C
    def h(t):
        f=moment(n,4,t)
        return int(t==identity)-sum(dual[j+2]*f[j] for j in range(4))
    assert all(h(t)==high for t in P)
    assert all(h(t)==low for t in M)
    count=0
    for t in short_types(n,4):
        val=h(t)
        assert low<=val<=high, (n,t,val,low,high)
        count+=1
    for j in range(5):
        lhs=sum(weights[i]*moment(n,4,P[i])[j] for i in range(3))
        rhs=sum(weights[i+3]*moment(n,4,M[i])[j] for i in range(3))
        assert lhs==rhs,(n,j,lhs,rhs)
    # Central class measures realize an actual positive-radius sharp example.
    # Q-law is supported on three disjoint nonidentity conjugacy classes.
    delta=min(Q(class_size(n,t),2*factorial(n)*w)
              for t,w in zip(M,weights[3:]))
    assert delta>0
    assert all(Q(1,factorial(n))-delta*w/class_size(n,t)>0
               for t,w in zip(M,weights[3:]))
    return count,C


def main():
    assert set(SUPPORTS)==set(TARGETS)==set(range(11,26))
    test()  # independent direct permutation/subset regressions for all k<=5
    for n in range(11,26):
        states,C=certify(n)
        print('PASS n=%d short-cycle states=%d C=%s'%(n,states,C),flush=True)
    print('ALL FIFTEEN EXACT RANK-FIVE CERTIFICATES PASSED.',flush=True)


if __name__=='__main__':main()
