#!/usr/bin/env python3
"""Exact actual-matrix diagnostics for the written weighted-cycle theorem.

These finite rational checks supplement, and do not replace, the all-n proof.
Only Python's standard library is needed.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import prod
from collections import defaultdict
import hashlib,itertools,json

ROOT=Path(__file__).resolve().parent
def require(ok,message):
    if not ok:raise ValueError(message)
def permanent(A):
    n=len(A);require(all(len(row)==n for row in A),'Matrix not square')
    if not n:return 1
    sums=[0]*n;out=0;old=0
    for k in range(1,1<<n):
        mask=k^(k>>1);changed=mask^old;j=changed.bit_length()-1
        sign=1 if mask&(1<<j) else -1
        for i in range(n):sums[i]+=sign*A[i][j]
        out+=(-1)**(n-mask.bit_count())*prod(sums);old=mask
    return out
def laplacian(n,edges,diagonal=None):
    A=[[0]*n for _ in range(n)]
    for i,j,w in edges:
        require(0<=i<n and 0<=j<n and i!=j and w>=0,'Invalid graph edge')
        A[i][i]+=w;A[j][j]+=w;A[i][j]-=w;A[j][i]-=w
    if diagonal is not None:
        require(len(diagonal)==n and all(x>=0 for x in diagonal),'Invalid diagonal addition')
        for i,x in enumerate(diagonal):A[i][i]+=x
    return A
def sub(A,S):return [[A[i][j] for j in S] for i in S]
def squared(A):return [[x*x for x in row] for row in A]
def defect(A):return prod(A[i][i] for i in range(len(A)))*permanent(A)-permanent(squared(A))
def matchings(n):
    return [mask for mask in range(1<<n)
            if not (mask & (((mask<<1)&((1<<n)-1))|(mask>>(n-1))))]
def matching_sum(c,power=1,signed=False):
    n=len(c)
    return sum((-1)**m.bit_count()*prod(c[i]**power for i in range(n) if m&(1<<i))
               if signed else prod(c[i]**power for i in range(n) if m&(1<<i))
               for m in matchings(n))
def cycle_values(w):
    n=len(w);d=[w[i-1]+w[i] for i in range(n)];H=prod(d)
    require(H>0,'Cycle diagnostic requires positive degrees')
    c=[Q(w[i]*w[i],d[i]*d[(i+1)%n]) for i in range(n)]
    a=Q(prod(w),H);epsilon=2*a
    L=laplacian(n,[(i,(i+1)%n,w[i]) for i in range(n)])
    P=Q(permanent(L),H);R=Q(permanent(squared(L)),H*H)
    Z=matching_sum(c);Z2=matching_sum(c,power=2);Zm=matching_sum(c,signed=True)
    require(P==Z+2*(-1)**n*a,'Actual permanent does not equal cycle formula')
    require(R==Z2+2*a*a,'Actual Hadamard-square permanent does not equal cycle formula')
    require(Zm==epsilon,'Signed matching formula does not equal singular determinant')
    if n%2:
        odd=2*sum(prod(c[i] for i in range(n) if m&(1<<i)) for m in matchings(n) if m.bit_count()%2)
        require(P==odd,'Actual odd-cycle permanent does not equal odd matching sum')
        require(defect(L)>=2*prod(w)**2,'Quantitative original-matrix bound failed')
        if n>=5:require(sum(c)>=1 and P>=2,'Triangle-free normalized lower bound failed')
    return L,c,a,P,R,Z,Z2

def choice_distribution(w):
    n=len(w);d=[w[i-1]+w[i] for i in range(n)];out=defaultdict(Q)
    for choices in range(1<<n):
        probability=prod(Q(w[i] if choices&(1<<i) else w[i-1],d[i]) for i in range(n))
        m=sum(1<<i for i in range(n) if choices&(1<<i) and not choices&(1<<((i+1)%n)))
        out[m]+=probability
    require(sum(out.values())==1,'Neighbor-choice probability not normalized')
    require(all(m in matchings(n) for m in out),'Mutual choices not a matching')
    return out
def moment_check(w,c,a,Z,Z2):
    distribution=choice_distribution(w);n=len(w);epsilon=2*a
    require(distribution[0]==epsilon,'Empty matching has wrong probability')
    for S in matchings(n):
        containment=sum(p for F,p in distribution.items() if F&S==S)
        require(containment==prod(c[i] for i in range(n) if S&(1<<i)),'Disjoint matching containment law failed')
    first=sum(p*2**F.bit_count() for F,p in distribution.items())
    overlap=sum(p*q*2**(F&G).bit_count() for F,p in distribution.items() for G,q in distribution.items())
    require(first==Z and overlap==Z2,'Exact mutual-choice moments differ from matching polynomials')
    require(Z-Z2>=epsilon*(Z-1),'Independent-copy loss inequality failed')
    return len(distribution)

def triangle_polynomial():
    # Universal integer-polynomial comparison in three independent weights.
    def add(a,b):
        c=a.copy()
        for m,v in b.items():c[m]=c.get(m,0)+v
        return {m:v for m,v in c.items() if v}
    def scale(a,c):return {m:v*c for m,v in a.items() if v*c}
    def mul(a,b):
        c={}
        for i,x in a.items():
            for j,y in b.items():
                m=tuple(u+v for u,v in zip(i,j));c[m]=c.get(m,0)+x*y
        return {m:v for m,v in c.items() if v}
    z={};a={(1,0,0):1};b={(0,1,0):1};c={(0,0,1):1}
    L=[[add(a,c),scale(a,-1),scale(c,-1)],
       [scale(a,-1),add(a,b),scale(b,-1)],
       [scale(c,-1),scale(b,-1),add(b,c)]]
    def per(A):
        out={}
        for p in itertools.permutations(range(3)):out=add(out,mul(mul(A[0][p[0]],A[1][p[1]]),A[2][p[2]]))
        return out
    lhs=add(mul(mul(mul(L[0][0],L[1][1]),L[2][2]),per(L)),scale(per([[mul(x,x) for x in row] for row in L]),-1))
    pairs=add(add(mul(a,b),mul(b,c)),mul(c,a))
    pair_squares=add(add(mul(mul(a,a),mul(b,b)),mul(mul(b,b),mul(c,c))),mul(mul(c,c),mul(a,a)))
    rhs=scale(mul(pairs,pair_squares),2)
    require(lhs==rhs,'Universal weighted triangle polynomial identity failed')
    return len(lhs)

def main():
    cycles=[];principal_count=0;moment_count=0
    for n in [3,4,5,6,7,9,11,13]:
        ws=[[1]*n,[1+(i*i+3*i)%11 for i in range(n)],
            [1<<(3*i%17) for i in range(n)]]
        for w in ws:
            L,c,a,P,R,Z,Z2=cycle_values(w)
            if n<=9:moment_count+=moment_check(w,c,a,Z,Z2)
            subsets=range(1<<n) if n<=7 else [0,1,(1<<n)-1,(1<<(n-1))-1,1|(1<<(n-1)),sum(1<<i for i in range(0,n,2))]
            for mask in subsets:
                S=[i for i in range(n) if mask&(1<<i)]
                require(defect(sub(L,S))>=0,'Actual ambient-degree principal strong bound failed');principal_count+=1
            cycles.append({'n':n,'conductances':w,'actual_permanent':str(permanent(L)),
                           'actual_square_permanent':str(permanent(squared(L))),
                           'quantitative_defect':str(defect(L))})
    # A weighted triangle and weighted five-cycle joined at vertex zero.
    edges=[(0,1,2),(1,2,7),(2,0,13),(0,3,1),(3,4,29),(4,5,3),(5,6,101),(6,0,5)]
    # Add a weighted K_{2,3} block at the same vertex, beyond cactus graphs.
    mixed=edges+[(u,v,2+(u+1)*(v+3)) for u in [0,7] for v in [8,9,10]]
    for n,E in [(7,edges),(11,mixed)]:
        for alpha in [[0]*n,[i*i%7 for i in range(n)]]:
            A=laplacian(n,E,alpha)
            subsets=range(1<<n) if n<=7 else [0,1,(1<<n)-1,(1<<(n-1))-1,7,1|(1<<7)|(1<<8)|(1<<9)|(1<<10)]
            for mask in subsets:
                S=[i for i in range(n) if mask&(1<<i)]
                require(defect(sub(A,S))>=0,'Actual weighted block or diagonal-addition diagnostic failed');principal_count+=1
    # Explicit zero-conductance/isolated-vertex cases are separate from the
    # positive-degree normalized cycle identities.
    zero_cases=0
    for n,w in [(3,[0,0,0]),(5,[0,1,2,0,7]),(7,[0,0,2,3,0,0,11])]:
        E=[(i,(i+1)%n,a) for i,a in enumerate(w)]
        for alpha in [[0]*n,[i%3 for i in range(n)]]:
            A=laplacian(n,E,alpha)
            for mask in range(1<<n):
                S=[i for i in range(n) if mask&(1<<i)]
                require(defect(sub(A,S))>=0,'Zero-conductance or isolated-vertex principal case failed')
                principal_count+=1;zero_cases+=1
    monomials=triangle_polynomial()
    # Negative controls reject two common semantic/parity mistakes.
    L,c,a,P,R,Z,Z2=cycle_values([1]*4)
    require(P!=Z-2*a,'Wrong odd-cycle sign accepted for even cycle')
    H=sub(cycle_values([1]*5)[0],[0,1])
    require(permanent(squared(H))>permanent(H),'Wrong induced-degree product accepted in ambient principal problem')
    out={'schema':1,'status':'PASS_EXACT_ACTUAL_WEIGHTED_CYCLE_DIAGNOSTICS',
         'cycle_cases':len(cycles),'principal_cases':principal_count,'zero_conductance_principal_cases':zero_cases,
         'mutual_choice_distribution_sizes_total':moment_count,'universal_triangle_polynomial_monomials':monomials,
         'negative_controls_rejected':['wrong_even_cycle_sign','induced_instead_of_ambient_principal_degrees'],
         'cases':cycles,'source_sha256':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in ['PAPER.md','check.py']},
         'scope':'Finite exact actual-matrix and probability diagnostics plus universal triangle identity; the all-n weighted theorem is the complete written proof. No Lean or peer review.'}
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
