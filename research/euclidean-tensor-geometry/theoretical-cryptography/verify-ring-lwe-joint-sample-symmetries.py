#!/usr/bin/env python3
"""Exact finite checks for ring-lwe-joint-sample-symmetries.md."""

from fractions import Fraction as F
from itertools import permutations,product
from math import gcd


def signed_basis(j,d):
    return (j%d,(-1)**(j//d))


def expected_signed(d):
    answers=set()
    for r in range(d):
        for l in range(1,2*d):
            if gcd(l,2*d)!=1:
                continue
            for e in (-1,1):
                images=[signed_basis(r+l*j,d) for j in range(d)]
                answers.add((tuple(p for p,s in images),tuple(e*s for p,s in images)))
    return answers


def shift(v,k,q):
    d=len(v)
    ans=[0]*d
    for j,a in enumerate(v):
        t,e=signed_basis(j+k,d)
        ans[t]=(e*a)%q
    return tuple(ans)


def mul(a,b,q):
    d=len(a)
    c=[0]*d
    for j,a_j in enumerate(a):
        sa=shift(b,j,q)
        for i,x in enumerate(sa):
            c[i]+=a_j*x
    return tuple(x%q for x in c)


def action(a,p,sign,q):
    out=[0]*len(a)
    for j,x in enumerate(a):
        out[p[j]]=x*sign[j]%q
    return tuple(out)


def orbit(a,q):
    return frozenset(tuple(x*c%q for x in shift(a,k,q))
                     for k in range(2*len(a)) for c in range(1,q) if gcd(c,q)==1)


def is_unit(a,q):
    return any(mul(a,s,q)==(1,)+(0,)*(len(a)-1)
               for s in product(range(q),repeat=len(a)))


def full_frames():
    tested=units=0
    for q,d in ((3,1),(3,2),(3,3),(3,4),(5,3),(9,2),(15,2)):
        V=list(product(range(q),repeat=d))
        U={a for a in V if is_unit(a,q)}
        cosets={orbit(a,q) for a in U}
        lab={}
        for i,coset in enumerate(cosets):
            for a in coset:
                assert a in U and a not in lab
                lab[a]=i
        assert set(lab)==U
        found=set()
        for p in permutations(range(d)):
            for s in product((-1,1),repeat=d):
                if all(len({lab.get(action(a,p,s,q)) for a in C})==1 and
                       all(action(a,p,s,q) in lab for a in C) for C in cosets):
                    found.add((p,s))
                tested+=1
        assert found==expected_signed(d),(q,d,len(found))
        units+=len(U)
    return tested,units


def binomial_witness():
    tested=0
    for d in range(3,7):
        q=3
        a=(1,q-1)+(0,)*(d-2)
        # This directly checks the modular orbit argument for the sole
        # unit a=1-X; no enumeration of labels or statistical inference.
        old=[shift(a,j,q) for j in range(d)]
        assert mul(a,(1,)*d,q)==(2,)+(0,)*(d-1)
        found=set()
        for p in permutations(range(d)):
            for s in product((-1,1),repeat=d):
                img=[action(v,p,s,q) for v in old]
                if all(v in orbit(img[0],q) for v in img[1:]):
                    found.add((p,s))
                tested+=1
        assert found==expected_signed(d),(d,len(found))
    return tested


def alphabet_cycles():
    examples=0
    for q in (3,5,7,9):
        expected={tuple((a+e*j)%q for j in range(q)) for e in (-1,1) for a in range(q)}
        got=set()
        for p in permutations(range(q)):
            if all((p[(j+1)%q]-p[j])%q in (1,q-1) for j in range(q)):
                got.add(p)
            examples+=1
        assert got==expected
    return examples


def toy_posterior():
    count=0
    for a,b,c in product(range(1,5),repeat=3):
        # A finite statistical experiment on output space {0,1}, with
        # three uniform labels. Exhaust arbitrary rational two-state kernels.
        p=tuple((F(x,5),1-F(x,5)) for x in (a,b,c))
        mu=tuple(sum(r[j] for r in p)/3 for j in (0,1))
        eta=tuple(tuple(r[j]/(3*mu[j]) for r in p) for j in (0,1))
        for x,y in product(range(5),repeat=2):
            M=((F(x,4),1-F(x,4)),(F(y,4),1-F(y,4)))
            sim=tuple(tuple(sum(r[i]*M[i][j] for i in (0,1)) for j in (0,1)) for r in p)
            for perm in permutations(range(3)):
                tar=tuple(p[w] for w in perm)
                eta_1=tuple(tuple(v[w] for w in perm) for v in eta)
                loss=lambda s,v:sum((int(k==s)-z)**2 for k,z in enumerate(v))
                risk_0=sum(p[s][i]*loss(s,eta[i])/3 for s,i in product(range(3),range(2)))
                risk_tar=sum(tar[s][j]*loss(s,eta_1[j])/3 for s,j in product(range(3),range(2)))
                risk_sim=sum(sim[s][j]*loss(s,eta_1[j])/3 for s,j in product(range(3),range(2)))
                distance=lambda u,v:sum((z-w)**2 for z,w in zip(u,v))
                transport=sum(mu[i]*M[i][j]*distance(eta[i],eta_1[j]) for i,j in product(range(2),repeat=2))
                gap=sum(mu[i]*min(distance(eta[i],v) for v in eta_1) for i in range(2))
                tv=max(sum(abs(sim[s][j]-tar[s][j]) for j in range(2))/2 for s in range(3))
                assert risk_tar==risk_0 and risk_sim-risk_0==transport
                assert gap<=transport<=2*tv
                count+=1
    return count


if __name__=="__main__":
    print("PASS signed stabilizers / unit coverage for full finite frame cases:",full_frames())
    print("PASS signed stabilizers from one cyclic binomial orbit:",binomial_witness())
    print("PASS finite alphabet-cycle permutations:",alphabet_cycles())
    print("PASS exact rational posterior-gap cases:",toy_posterior())
