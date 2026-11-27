#!/usr/bin/env python3
"""Exact Bernstein and word-category replay for DuchiFourProjectionInequality.md."""
from fractions import Fraction as Q
from itertools import product, permutations
from collections import Counter
from math import comb, isqrt

N = (4, 2, 3)
IDX = list(product(*(range(d+1) for d in N)))
power = {(1,0,0):18, (2,0,0):18, (3,0,0):6,
         (0,0,1):18, (0,0,2):18, (0,0,3):6,
         (0,1,1):48, (2,1,0):48, (0,2,2):48, (1,1,1):-228}
coef = {idx: sum(Q(2*c)*Q(comb(idx[0],r[0]),comb(4,r[0]))
                          *Q(comb(idx[1],r[1]),comb(2,r[1]))
                          *Q(comb(idx[2],r[2]),comb(3,r[2]))
                  for r,c in power.items()) for idx in IDX}
for (i,j,k), v in coef.items():
    pred = (0,9,24,48,84)[i]+(0,12,36,84)[k]+16*j*k+8*j*comb(i,2)+32*(j==2)*comb(k,2)-19*i*j*k
    assert v == pred and v >= 0
reconstructed = Counter()
for idx,c in coef.items():
    for ex in product(*(range(i,d+1) for i,d in zip(idx,N))):
        z = c
        for i,d,e in zip(idx,N,ex):
            z *= comb(d,i)*comb(d-i,e-i)*(-1)**(e-i)
        reconstructed[ex] += z
assert all(reconstructed[i] == 2*power.get(i,0) for i in IDX)

W = list(product(range(4), repeat=4))
D4 = list(permutations(range(4)))
def pattern(w):
    seen = {}
    return tuple(seen.setdefault(x,len(seen)) for x in w)
counts = Counter(map(pattern,W))
assert len(counts)==15 and all(v == len(list(permutations(range(4),max(k)+1))) for k,v in counts.items())

def matmul(a,b):
    n=len(a)
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)) for i in range(n))

def diag(d):
    return tuple(tuple(Q(x if i==j else 0) for j in range(len(d))) for i,x in enumerate(d))

def ray(t):
    u=((1-t*t)/(1+t*t), 2*t/(1+t*t))
    return tuple(tuple(x*y for y in u) for x in u)

def sqrtq(t):
    x,y=isqrt(t.numerator),isqrt(t.denominator)
    assert x*x==t.numerator and y*y==t.denominator
    return Q(x,y)

def rankone_or_identity_norm(a):
    if a==diag([1]*len(a)):
        return Q(1)
    for i,j,k,l in product(range(len(a)),repeat=4):
        assert a[i][j]*a[k][l]==a[i][l]*a[k][j]
    return sqrtq(sum(x*x for row in a for x in row))

def verify(blocks):
    for scale, matrices in blocks:
        assert scale>=0 and all(matmul(p,p)==p and p==tuple(zip(*p)) for p in matrices)
    def value(w):
        values=[]
        for scale,matrices in blocks:
            a=matrices[w[0]]
            for i in w[1:]:
                a=matmul(a,matrices[i])
            values.append(scale**4*rankone_or_identity_norm(a))
        return max(values)
    scores={w:value(w) for w in W}
    R=sum(scores.values())/256
    S=sum(scores[w] for w in D4)/24
    D=sum(scores[(i,)*4] for i in range(4))/4
    p={}
    for k in counts:
        p[k]=sum(v for w,v in scores.items() if pattern(w)==k)/counts[k]
    group = lambda s: p[tuple(map(int,s))]
    q1,q2,q3=map(group,("0001","0010","0101"))
    H,J,L=map(group,("0102","0120","0012"))
    assert group("0001")==group("0011")==group("0111")
    assert group("0010")==group("0100")==group("0110")
    assert group("0012")==group("0112")==group("0122") and group("0102")==group("0121")
    assert 256*R==4*D+36*q1+36*q2+12*q3+72*L+48*H+24*J+24*S
    assert R-S >= (D-S)/64 >= 0
    return R,S,D

I,Z=diag([1,1]),diag([0,0])
rays=[ray(Q(i,31)) for i in range(-4,5)]
for t in range(8):
    p=(I,rays[t],rays[t+1],rays[8-t])
    q=(rays[8-t],Z,I,rays[t+1])
    assert verify([(Q(1),p),(Q(3+t,7),q)])[0]>0
assert verify([(Q(1),[diag([k==i for k in range(4)]) for i in range(4)])])==(Q(1,64),0,1)
assert verify([(Q(2),[rays[0]]*4),(Q(1),[I,Z,I,Z])])==(16,16,16)
assert verify([(Q(1),[Z]*4)])==(0,0,0)
print("PASS: 60 exact Bernstein coefficients and their power reconstruction; 15 word patterns; 11 exact full 256-word cases.")
