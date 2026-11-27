#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
from math import comb

def influences(f,d):
    return [F(sum(f[v]!=f[v|(1<<i)] for v in range(1<<d) if not v>>i&1),1<<(d-1))
            for i in range(d)]

gadgets=0
for b in range(1,9):
    for j in range(1,(1<<(b-1))+1):
        G=[int(y<j) for y in range(1<<b)]
        p=F(j,1<<b)
        II=influences(G,b)
        for i,I in enumerate(II):
            assert I<=min(2*p,F(1,1<<(b-1-i)))
        L=next(t for t in range(b+1) if j*(1<<t)>=1<<b)
        assert sum(II)<=2*p*(L+2)
        gadgets+=1
print(f"fair-bit gadget: {gadgets} dyadic biases; individual influences and geometric sum PASS")

composition=0
for b in range(1,4):
    for j in range(1,(1<<(b-1))+1):
        p=F(j,1<<b)
        G=[int(y<j) for y in range(1<<b)]
        II=influences(G,b)
        mask=(1<<b)-1
        # Threshold at two out of three independent blocks.
        f=[int(sum(G[(y>>(i*b))&mask] for i in range(3))>=2) for y in range(1<<(3*b))]
        assert influences(f,3*b)==[2*p*(1-p)*I for I in II]*3
        composition+=1
print(f"independent composition: {composition} threshold experiments verify all pivotal products")

def direct(C,M):
    # Codewords are represented by support masks; no generator rank is used.
    dim=(len(C)).bit_length()-1
    assert len(C)==1<<dim
    B=[0]*(M+1)
    H=[[0]*M for _ in range(M)]
    for E in range(1<<M):
        size=E.bit_count()
        B[size]+=any(w and w&E==w for w in C)
        for i in range(M):
            bit=1<<i
            if not E&bit:
                H[i][size]+=any(w&bit and w&(E|bit)==w for w in C)
    for row in H:
        area=sum(F(v,M*comb(M-1,j)) for j,v in enumerate(row))
        assert area==F(dim,M)
    assert H.count(H[0])==M
    for p in (F(0),F(1,7),F(4,5),F(1)):
        block=sum(v*p**j*(1-p)**(M-j) for j,v in enumerate(B))
        h=sum(v*p**j*(1-p)**(M-1-j) for j,v in enumerate(H[0]))
        assert block<=M*p*h
    return H[0]

# Length-seven Hamming code: columns of its parity-check matrix are 1..7.
C=[]
for w in range(128):
    parity=0
    for i in range(7):
        if w>>i&1:
            parity^=i+1
    if parity==0:
        C.append(w)
assert direct(C,7)[:3]==[0,0,3]
assert direct([0,255],8)==[0,0,0,0,0,0,0,1]
print("support-witness enumeration: Hamming and repetition EXIT area / block union bound PASS")

# In disjoint duplicated pairs, coordinate transitivity alone gives h(p)=p.
# The target-bit stabilizer cannot move the paired partner to a different pair.
dup=[sum((3<<(2*i)) for i in range(4) if v>>i&1) for v in range(16)]
assert direct(dup,8)==[0]+[comb(6,j) for j in range(7)]
print("transitivity-only negative control: h(p)=p for duplicated-bit code")
