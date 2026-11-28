#!/usr/bin/env python3
"""Direct Fourier check of spread witness and exhaustive 4-bit modular cases."""
from itertools import permutations,product
from collections import Counter

def walsh(f):
    a=[1-2*x for x in f]
    s=1
    while s<len(a):
        for j in range(0,len(a),2*s):
            for k in range(j,j+s):
                u,v=a[k],a[k+s];a[k],a[k+s]=u+v,u-v
        s*=2
    return a

# F4 encoded in basis (1, omega), by explicit multiplication.
table=((0,0,0,0),(0,1,2,3),(0,2,3,1),(0,3,1,2))
line=[0]*16
for a,b in product(range(4),repeat=2):
    if a or b:line[a|(b<<2)]=(4 if not b else table[a][table[b].index(1)])
ang=lambda x:table[2][x&3]|(table[2][x>>2]<<2)
assert all((ang(ang(ang(x)))==x and (ang(x)==x)==(x==0)) for x in range(16))

count=0
for order in permutations(range(5)):
    at={v:j for j,v in enumerate(order)}
    f=lambda u,v: int((not u)!=(not v)) if not (u and v) else int(
        line[u] in (order[at[line[v]]],order[(at[line[v]]+1)%5]))
    ff=[f(x&15,x>>4) for x in range(256)]
    assert set(map(abs,walsh(ff)))=={16}
    assert all(ff[u|(v<<4)]==ff[u|(ang(v)<<4)] for u,v in
               product(range(16),repeat=2))
    assert walsh(ff[:16])==[-14]+[2]*15
    count+=1
assert count==120

# Conjugation by fixed sums and even-sum decomposition in each triple.
# Inputs with each 4-bit row repeated three times are exactly fixed.
def decode12(x):
    t=[[(x>>(i+4*j))&1 for j in range(3)] for i in range(4)]
    u=sum((sum(y)%2)<<i for i,y in enumerate(t))
    v=[(row[0]^(u>>i&1))|((row[1]^(u>>i&1))<<1) for i,row in enumerate(t)]
    return u,v
def F12(x):
    u,v=decode12(x)
    return f(u,v[0]|(v[1]<<2))^int(bool(v[2]))^int(bool(v[3]))
def step4(x):
    return (x>>4)|((x&15)<<8)
# On sum-zero bits (a,b,a+b), the shift sends (a,b)->(b,a+b)=omega*(a+b*omega).
assert all(F12(x)==F12(step4(x)) for x in range(4096))
W12=walsh([F12(x) for x in range(4096)])
assert set(map(abs,W12))=={64}
assert all((W12[j*0x111]-w)%3==0 for j,w in enumerate([-14]+[2]*15))
assert [F12(u*0x111) for u in range(16)]==[0]+[1]*15
assert any(F12(x)!=F12((x>>1)|((x&1)<<11)) for x in range(4096))

def ro4(x):
    return (x>>1)|((x&1)<<3)

C=Counter();CC=Counter()
for mask in range(1<<16):
    tt=[mask>>i&1 for i in range(16)]
    W=walsh(tt)
    bent=all(abs(x)==4 for x in W)
    p3=all(x%3 for x in W)
    p5=all(x%5 in (1,4) for x in W)
    assert p5==bent
    if p3:
        assert bent or sorted(map(abs,W))==[2]*15+[14]
        C["bent" if bent else "flip"]+=1
        if all(tt[i]==tt[ro4(i)] for i in range(16)):
            CC["bent" if bent else "flip"]+=1
            if not bent:
                freq=next(j for j,x in enumerate(W) if abs(x)==14)
                assert freq in (0,15)
                mismatches=[j for j,e in enumerate(tt)
                            if e!=((W[freq]<0)^((j&freq).bit_count()%2))]
                assert mismatches in ([0],[15])
assert C=={"bent":896,"flip":512} and CC=={"bent":8,"flip":8}
print("INDEPENDENT PASS:",count,"spread witnesses, 4096 subgroup-lifted inputs")
print("INDEPENDENT PASS: 65536 four-bit tables; mod3 896 bent+512 flips;",
      "cyclic 8+8; mod5 exactly 896 bent")
