#!/usr/bin/env python3
"""Independent direct polynomial-coefficient GF(2) rank, not cyclotomic/rational reduction."""
import argparse
from itertools import combinations


def check(n):
    # Primitive polynomials are not assumed correct: build and check the full nonzero cycle.
    modulus={3:0xb,5:0x25,7:0x83,9:0x211,11:0x805}[n]
    q=1<<n; N=q-1; D=min(N, q//4+4)
    alog=[]; g=1
    for _ in range(N):
        alog.append(g); g <<= 1
        if g>=q: g ^= modulus
    assert g==1 and set(alog)==set(range(1,q))
    log=[None]*q
    for i,t in enumerate(alog): log[t]=i
    def mul(a,b):return alog[(log[a]+log[b])%N] if a and b else 0
    def power(a,j):return alog[(log[a]*j)%N] if a else 0
    def trace(a):
        t=0; b=a
        for _ in range(n): t^=b; b=mul(b,b)
        assert t in (0,1); return t
    T=[trace(a) for a in range(q)]
    mask=[sum(T[mul(a,1<<j)]<<j for j in range(n)) for a in range(q)]
    xp=[[power(a,i) for i in range(D+1)] for a in range(q)]
    vals=min(q-1,4*D+4)
    points=[0]+alog[:vals]; piv={}; rows=0; target=n*(D-1)
    for x,y in combinations(points,2):
        den=xp[x][6]^xp[y][6]; assert den
        u=alog[(log[x^y]-log[den])%N]; block=[]
        for i in range(1,D+1): block.append(mask[mul(u,xp[x][i]^xp[y][i])])
        assert T[mul(u,xp[x][5]^xp[y][5])]==1
        for bit in range(n):
            C=1<<bit
            assert (((block[0]&mul(C,C)).bit_count()+(block[2]&C).bit_count())&1)==0
        row=0
        for v in reversed(block): row=row<<n|v
        rows+=1
        while row:
            k=row.bit_length()-1
            if k not in piv: piv[k]=row; break
            row^=piv[k]
        if len(piv)==target: break
    assert len(piv)==target,(n,len(piv),target)
    print(f'n={n:2} degree={D:3} unknown_bits={D*n:4} direct_rank={len(piv):4} nullity={n:2} pairs_used={rows:6} PASS',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('n',nargs='*',type=int,choices=None)
    for k in p.parse_args().n or [3,5,7,9]: check(k)
