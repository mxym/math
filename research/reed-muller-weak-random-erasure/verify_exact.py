#!/usr/bin/env python3
from fractions import Fraction as F
from math import comb

def rank(rows):
    B={}
    for x in rows:
        while x:
            i=x.bit_length()
            if i not in B:
                B[i]=x
                break
            x^=B[i]
    return len(B)

def poly(p,counts):
    n=len(counts)-1
    return sum(c*p**j*(1-p)**(n-j) for j,c in enumerate(counts))

cases=0
for m in range(1,4):
    M=1<<m
    full=(1<<M)-1
    for r in range(m+1):
        G=[sum(1<<x for x in range(M) if x&a==a)
           for a in range(M) if a.bit_count()<=r]
        K=len(G)
        assert rank(G)==K
        D=[K-rank(v&(full^E) for v in G) for E in range(1<<M)]
        GD=[0]*(M+1)
        BF=[0]*(M+1)
        H=[[0]*M for _ in range(M)]
        for E,v in enumerate(D):
            j=E.bit_count()
            GD[j]+=v
            BF[j]+=v>0
            witness=[]
            for i in range(M):
                b=1<<i
                if not E&b:
                    inc=D[E|b]-v
                    assert inc in (0,1)
                    H[i][j]+=inc
                else:
                    witness.append(v-D[E^b])
            assert bool(v)==any(witness)
        assert all(h==H[0] for h in H[1:])
        for j in range(M):
            assert (j+1)*GD[j+1]-(M-j)*GD[j]==M*H[0][j]
        assert sum(F(c,M*comb(M-1,j)) for j,c in enumerate(H[0]))==F(K,M)
        for p in (F(0),F(1,12),F(1,3),F(2,3),F(1)):
            assert poly(p,BF)<=M*p*poly(p,H[0])
        cases+=1
print(f"linear-system nullity: {cases} small Reed-Muller codes; exact area, derivative and block union bound PASS")
