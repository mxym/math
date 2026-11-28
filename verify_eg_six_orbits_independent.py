#!/usr/bin/env python3
"""Independent K3,3 check by half-power Laurent traces; no full length-16 DFS."""
from collections import Counter,defaultdict
from itertools import combinations
A=[(i,j)for i in range(6)for j in range(6)if (i<3)!=(j<3)]
F=[(1,4),(1,5),(2,4),(2,5)]
v={a:tuple((a==e)-(a[::-1]==e)for e in F)for a in A}
nb={a:[b for b in A if b[0]==a[1] and b!=a[::-1]]for a in A}
def zadd(a,b):return tuple(x+y for x,y in zip(a,b))
def short(M=None):
    Z=(0,)*4;dp={(a,a,Z):1 for a in A};out=[]
    for depth in range(1,9):
        d=Counter()
        for (a,b,x),c in dp.items():
            for h in nb[b]:
                y=zadd(x,v[h])
                if M:y=tuple(i%M for i in y)
                d[a,h,y]+=c
        dp=d
        if depth not in (2,4,8):continue
        # trace of the square of this Laurent Hashimoto half-power
        zero=sum(c*dp.get((b,a,tuple((-j)%M if M else -j for j in x)),0)
                 for (a,b,x),c in dp.items())
        total=Counter()
        for (a,b,x),c in dp.items():total[a,b]+=c
        ct=sum(c*total[b,a]for (a,b),c in total.items())
        assert zero==0;out.append(ct)
    assert out==[72,648,133128]
def long():
    middles=tuple(3+int(t)for t in '0101012010201212');a=0;x=(0,)*4;vertices=[]
    for j,z in enumerate(middles):
        vertices.extend([(a,x),(z,zadd(x,v[a,z]))])
        b=1-a
        x=zadd(zadd(x,v[a,z]),v[z,b]);a=b
    assert (a,x)==vertices[0] and len(set(vertices))==32
    width=32*(1+65+65**2+65**3);M=width+1
    for mod in [5,M]:
        ids={(i,tuple(a%5 for a in x)if mod==5 else sum(65**j*a for j,a in enumerate(x))%M)for i,x in vertices}
        assert len(ids)==32
    assert all(65**i>32*sum(65**j for j in range(i))for i in range(4))
if __name__=='__main__':
    short();short(5);long()
    print('PASS K3,3 formal and mod-5 half-power traces; 32-cycle in both finite examples')
