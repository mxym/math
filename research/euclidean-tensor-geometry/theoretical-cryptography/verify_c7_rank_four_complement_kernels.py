#!/usr/bin/env python3
"""Exact Fourier-positive certificates for complement kernels in F_7^4."""
import base64
from fractions import Fraction as F
import gzip
from itertools import combinations, product
import json
from pathlib import Path
import sys

D=(0,1,6)
M1=(1,1,1,2,3)
M2=(1,1,2,2,3)
SCALE=10**7
C=10**9
P=(2*C,1246979603,-445041868,-1801937736,-1801937736,-445041868,1246979603)
TARGET=F(12227,2000)


def require(ok, why):
    if not ok:raise AssertionError(why)


def verify_cosines():
    def poly(x):return x**3+x*x-2*x-1
    for i in (1,2,3):
        lo=F(P[i],C); hi=F(P[i]+1,C)
        require(poly(lo)*poly(hi)<0,("cosine root bracket",i))
    require(P[3]+1<P[2] and P[2]+1<P[1],"cosine order")
    t=F(331767,100000)
    require((F(2)+F(P[1]+1,C))/4<(t/(7-t))**2,"theta upper root test")
    require(t**8/7**4<TARGET,"strict target comparison")


def sign(v):
    return min(v,tuple(-x%7 for x in v))


def support(M):
    return sorted({sign(v) for v in product(D,repeat=4)
                   if any(v) and (-sum(x*y for x,y in zip(v,M[1:])))%7 in D})


def echelon(k):
    for piv in combinations(range(4),k):
        free=tuple(i for i in range(4) if i not in piv)
        slots=[(r,j) for r,h in enumerate(piv) for j in free if j>h]
        for c in product(range(7),repeat=len(slots)):
            R=[[int(j==i) for j in range(4)] for i in piv]
            for (r,j),x in zip(slots,c):R[r][j]=x
            yield tuple(map(tuple,R)),piv,free


def quotient(S,K):
    R,piv,free=K
    return sorted({sign(tuple((v[j]-sum(v[i]*r[j] for i,r in zip(piv,R)))%7
                              for j in free)) for v in S})


def witness(Q,W):
    require(len(W)==len(Q) and all(type(x) is int and x>=0 for x in W),"weight encoding")
    require(any(Q[0]),"zero collision in candidate witness")
    dim=len(Q[0])
    require(F(SCALE+2*sum(W),SCALE)>=TARGET,"objective too small")
    for v in product(range(7),repeat=dim):
        a=SCALE*C+sum(w*P[sum(x*y for x,y in zip(v,q))%7] for q,w in zip(Q,W))
        require(a>=0,("negative certified Fourier coefficient",v))


def check_case(data):
    M=tuple(data["M"])
    S=support(M)
    line= {tuple(map(int,k.split(","))):w for k,w in data["line"].items()}
    two={tuple(map(tuple,r)):w for r,w in data["two"]}
    require(len(two)==len(data["two"]),"duplicate two-plane")
    nonzero_block=set(); ruled=set(); bad=set()
    for K in echelon(1):
        r=K[0][0]
        Q=quotient(S,K)
        if not any(Q[0]):
            nonzero_block.add(r)
        elif r in line:
            witness(Q,line[r]);ruled.add(r)
        else:
            bad.add(r)
    require(ruled==set(line), "unused line witness")
    used=set()
    for K in echelon(2):
        r,s=K[0]
        # In echelon order each projective line has one of these normalized reps.
        lines={tuple((x+u*y)%7 for x,y in zip(r,s)) for u in range(7)}|{s}
        if not lines<=bad: continue
        Q=quotient(S,K)
        if not any(Q[0]):continue
        require(K[0] in two,"some surviving plane has no witness")
        witness(Q,two[K[0]])
        used.add(K[0])
    require(used==set(two),"unused plane witness")
    stats=(len(S),len(nonzero_block),len(ruled),len(bad),len(used))
    require(stats=={M1:(16,16,384,0,0),M2:(17,17,216,167,8)}[M],
            ("kernel census",M,stats))
    print("quotient labels",M,": sign-pairs/blocked lines/fourier lines/remaining lines/planes",
          stats)


def check(data):
    verify_cosines()
    require(data["format"]=="c7-rank-four-complement-kernels-v1","certificate version")
    require(data["weights_denominator"]==SCALE,"weight denominator")
    parts=[json.loads(gzip.decompress(base64.b64decode(x,validate=True)))
           for x in data["parts_gzip_base64"]]
    require([tuple(x["M"]) for x in parts]==[M1,M2],"shape order")
    for case in parts:check_case(case)
    print("PASS: integer Fourier certificates and all necessary kernel sizes")


if __name__=="__main__":
    path=sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name(
        "c7_rank_four_complement_kernel_certificate.json")
    check(json.loads(Path(path).read_text(encoding="utf-8")))
