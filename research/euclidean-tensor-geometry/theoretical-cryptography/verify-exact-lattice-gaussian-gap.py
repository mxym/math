#!/usr/bin/env python3
"""Finite exact tests for the geometric companion directions (Python 3 only)."""
from fractions import Fraction as F
from itertools import product
from math import exp, pi


class Metric:
    def __init__(self,name,G):
        self.name=name
        self.G=tuple(tuple(F(c) for c in row) for row in G)
        self.d=len(G)
        lo=min(self.G[i][i]-sum(abs(self.G[i][j]) for j in range(self.d) if j!=i)
               for i in range(self.d))
        assert lo>0
        self.lo=lo  # Gershgorin lower bound in coefficient coordinates.
        max_initial=max(self.quad(v) for v in product((0,1),repeat=self.d))
        bound=1
        while lo*bound*bound<=max_initial:
            bound+=1
        res={}
        for v in self.box(bound):
            mod=tuple(x%2 for x in v)
            h=self.quad(v)
            if mod not in res or h<res[mod][0]:
                res[mod]=(h,[v])
            elif h==res[mod][0]:
                res[mod][1].append(v)
        self.vor=[v for h,vs in res.values() for v in vs if any(v)]
        assert len(res)==2**self.d
        self.B2=max(map(self.quad,self.vor))
        self.lambda2=min(map(self.quad,self.vor))
        # Exact check every relevant vector lies in twice the origin Voronoi
        # cell. Outside this box Cauchy already implies the inequalities.
        b=1
        while lo*b*b<=self.B2:
            b+=1
        for v in self.vor:
            for w in self.box(b):
                assert abs(self.dot(v,w))<=self.quad(w)

    def dot(self,u,v):
        return sum(a*self.G[i][j]*b for i,a in enumerate(u) for j,b in enumerate(v))

    def quad(self,u):
        return self.dot(u,u)

    def box(self,b):
        return product(range(-b,b+1),repeat=self.d)

    def choose(self,k):
        assert any(k)
        if next(x for x in k if x)<0:
            return tuple(-x for x in self.choose(tuple(-x for x in k)))
        candidates=[v for v in self.vor if self.dot(k,v)>=self.quad(v)]
        assert candidates
        return min(candidates,key=lambda v:(self.quad(v),v))


def plus(k,amount,v):
    return tuple(x+amount*y for x,y in zip(k,v))


def pairing(M,k,b,e):
    v=M.choose(k)
    alpha=plus(k,e,v)
    zeta=plus(k,e-2-b,v)
    assert tuple(x-y for x,y in zip(alpha,zeta))==tuple((2+b)*x for x in v)
    gap=(M.quad(alpha)-M.quad(zeta))/(2+b)
    assert gap >= (2*e-b)*M.quad(v)>0
    tail=gap-(e*e-(e-b)**2)*M.quad(v)/(1+b)
    assert tail>=(2*e-b)*M.quad(v)/(1+b)>0
    return v,alpha,zeta,gap


def geometry(M,b,e):
    assert 0<=b<1 and b/2<e<F(1,2) and abs(e-b)<F(1,2)
    assert e*e*M.B2<M.lambda2
    count=0
    for k in M.box(5 if M.d<3 else 3):
        if not any(k):
            continue
        v,al,ze,gap = pairing(M,k,b,e)
        assert M.lambda2<=M.quad(v)<=M.B2
        assert M.choose(tuple(-x for x in k))==tuple(-x for x in v)
        for w in M.box(2):
            assert M.quad(plus(w,-e,v))-e*e*M.quad(v)>=(1-2*e)*M.quad(w)
            ed=e-b
            assert M.quad(plus(w,-ed,v))-ed*ed*M.quad(v)>=(1-2*abs(ed))*M.quad(w)
            count+=2
    print(f"PASS {M.name}: lambda^2={M.lambda2}, B^2={M.B2}, "
          f"{len(M.vor)} shortest mod-2 representatives, {count} exact column inequalities")


def numerical_operator(M,b,e,t):
    ids=tuple(j for j in M.box(2) if any(j))
    delta=t*t/(1+float(b))
    P=[pairing(M,k,b,e) for k in ids]
    actual_T=[]
    for j in ids:
        row=[]
        for v,al,ze,gap in P:
            shift=e*e*M.quad(v)
            z1=delta*float(M.quad(plus(j,-1,al))-shift)
            z2=t*t*float(gap)+delta*float(M.quad(plus(j,-1,ze))-shift)
            row.append(exp(-pi*z1)-exp(-pi*z2))
        actual_T.append(row)
    R=[[z-int(i==j) for j,z in enumerate(row)] for i,row in enumerate(actual_T)]
    norm=max(sum(abs(row[j]) for row in R) for j in range(len(ids)))
    assert norm<1/2
    # Scale the rhs by its largest possible lattice Gaussian term.
    h=[exp(-pi*delta*float(M.quad(j)-M.lambda2)) for j in ids]
    y=[0.0]*len(ids)
    for _ in range(70):
        y=[-hj-sum(a*b for a,b in zip(row,y)) for hj,row in zip(h,R)]
    residual=max(abs(hj+sum(a*b for a,b in zip(row,y))) for hj,row in zip(h,actual_T))
    assert residual<1e-12
    assert max(abs(y1-y2) for y1,y2 in zip(y,reversed(y)))<1e-12
    c_bound=sum(abs(yi)*exp(-pi*delta*float(M.lambda2-e*e*M.quad(p[0])))
                for yi,p in zip(y,P))
    assert 2*c_bound<1
    print(f"PASS {M.name}: normalized finite norm={norm:.6g}, rhs-relative residual={residual:.3g}")


if __name__=="__main__":
    axes=[
        (Metric("line",((1,),)),F(7,8),F(15,32),8),
        (Metric("triangular",((1,F(1,2)),(F(1,2),1))),F(3,4),F(7,16),8),
        (Metric("skew plane",((2,F(3,4)),(F(3,4),5))),F(3,4),F(7,16),7),
        (Metric("long rectangle",((1,0),(0,25))),F(1,4),F(3,20),6),
        (Metric("skew 3-space",((3,1,F(-1,2)),(1,4,F(1,2)),(F(-1,2),F(1,2),2))),
         F(1,2),F(5,16),5)]
    assert axes[1][0].B2==axes[1][0].lambda2
    for M,b,e,t in axes:
        geometry(M,b,e)
        numerical_operator(M,b,e,t)
