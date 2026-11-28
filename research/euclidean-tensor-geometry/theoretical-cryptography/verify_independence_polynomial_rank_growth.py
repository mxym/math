#!/usr/bin/env python3
"""Exact finite controls for the proof and a connected cograph witness."""
from fractions import Fraction as Q
from math import comb
from hashlib import sha256


def choose(n,k):
    return comb(n,k) if 0<=k<=n else 0


def ratio_and_curvature():
    t=u=0
    for r in range(2,21):
        for s in range(r):
            for d in range(r-s+1):
                delta=r-s-d
                for k in range(s,r+1):
                    a=choose(d,k-s)
                    upper=Q(k,r)**s*Q(r-k,r-s)**delta
                    assert Q(a,comb(r,k))<=upper
                    t+=1
        for j in range(1,r):
            a=comb(r,j)
            z=Q(comb(r,j+1)+comb(r,j-1)-2*a,a)
            assert z==Q((2*j-r)**2-r-2,(j+1)*(r-j+1))
            u+=1
    print("binomial control cases:",t,u)


def upper_witness():
    r,k,part=4096,147,5
    t=(part+1)**k
    m=t.bit_length()
    assert (1<<(m-1))<t<(1<<m)
    s=r-m
    assert m>=k and s>0
    J=[comb(k,j)*part**j for j in range(k+1)]
    pts=(1992,2022,2032)
    def coef(i):
        return choose(r,i)+sum(a*choose(s,i-j) for j,a in enumerate(J))-choose(s,i)+int(i==1)
    values=list(map(coef,pts))
    assert min(values[0],values[-1])>values[1]
    assert values[0]>max(coef(pts[0]-1),coef(pts[0]+1))
    assert values[1]<min(coef(pts[1]-1),coef(pts[1]+1))
    assert values[2]>max(coef(pts[2]-1),coef(pts[2]+1))
    print("connected example order",r+part*k+1,"independence",r,
          "three strict-valley indices",*pts)
    print("coefficient SHA256:",
          *(sha256(str(v).encode()).hexdigest() for v in values))


if __name__=="__main__":
    ratio_and_curvature()
    upper_witness()
    print("PASS")
