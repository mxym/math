#!/usr/bin/env python3
"""Independent exact finite replay of four eventually optimal 3-subset branches.

Uses only Python standard library integers/Fractions, and reconstructs primal
and dual via independent 5x5 rational Gaussian elimination. No SymPy, solver,
floating-point optimizer, or import from the symbolic positivity checker.

THIS DOES NOT PROVE INFINITELY MANY n; the polynomial sign theorem is in
the paper and its separately replayable symbolic sign certificate.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json

def F(n,x,y,z):
    N=n*(n-1)*(n-2)//6
    M1=(n-2)*(2*n+(n-3)*x)//2
    M2=(n-2)*(x*(x-1)//2)+(x+1)*(n-x)+(n-4)*y
    M3=x*(x-1)*(x-2)//6+x*y+z
    out=(N-M1+M2-M3,M1-2*M2+3*M3,M2-3*M3,M3)
    assert min(out)>=0 and sum(out)==N,(n,x,y,z,out)
    return out

def profiles(n):
    for x in range(n+1):
        for y in range((n-x)//2+1):
            for z in range((n-x-2*y)//3+1):
                r=n-x-2*y-3*z
                if r==0 or r>=4:
                    yield (x,y,z)

def candidate(n):
    m,r=divmod(n,4)
    assert n>=48 and m>=12
    K=(3*m-2,3*m-1,3*m-1,3*m)[r]
    Y=(2*m,2*m-1,2*m+1,2*m)[r]
    Z=(0,1,0,1)[r]
    E=(m-3,m-2,m-2,m-2)[r]
    E3=(m+1,m+1,m,m)[r]
    P=((n,0,0),(K,0,0),(0,Y,Z))
    R=((n-2,1,0),(E,0,E3))
    for x,y,z in P+R:
        left=n-x-2*y-3*z
        assert left==0 or left>=4
    assert len(set(P+R))==5
    return m,r,P,R

def exact_solve(A,b):
    size=len(A)
    assert len(b)==size
    v=[[Q(v) for v in row]+[Q(rhs)] for row,rhs in zip(A,b)]
    for col in range(size):
        pivot=next((t for t in range(col,size) if v[t][col]),None)
        assert pivot is not None,'Degenerate primal or dual contact system'
        v[col],v[pivot]=v[pivot],v[col]
        d=v[col][col]
        v[col]=[x/d for x in v[col]]
        for other in range(size):
            if other==col:continue
            mul=v[other][col]
            if mul:v[other]=[a-mul*b for a,b in zip(v[other],v[col])]
    ans=[row[-1] for row in v]
    assert all(sum(Q(v)*a for v,a in zip(row,ans))==b[i] for i,row in enumerate(A))
    return ans

def formula(m,r):
    if r==0:
        return Q((2*m-1)*(18*m**4-3*m**3+30*m*m-19*m-38),
                 2*(m+2)*(18*m**4+33*m**3-48*m*m-19*m-4))
    if r==1:
        return Q(72*m**5+66*m**4+11*m**3-2*m*m-149*m-34,
                 (m+2)*(72*m**4+246*m**3-103*m*m-336*m+37))
    if r==2:
        return Q(2*m*(18*m**5+45*m**4+82*m**3+37*m*m-22*m-16),
                 (m+3)*(2*m+1)*(3*m*m+5*m-4)*(6*m*m+11*m+2))
    return Q(12*m**6+47*m**5+75*m**4+24*m**3-68*m*m-68*m-10,
             (m+3)*(12*m**5+65*m**4+78*m**3-42*m*m-70*m-10))

def check_one(n):
    m,r,P,R=candidate(n)
    T=P+R
    f=[F(n,*p) for p in T]
    A=[[1,1,1,0,0],[0,0,0,1,1]]
    A += [[f[i][j]*(1 if i<3 else -1) for i in range(5)] for j in range(3)]
    w=exact_solve(A,[1,1,0,0,0])
    B=[list(f[i][:3])+([1,0] if i<3 else [0,1]) for i in range(5)]
    coeff=exact_solve(B,[1,0,0,0,0])
    lam=coeff[:3]
    high,low=coeff[3:]
    assert all(a>0 for a in w)
    assert high==1
    assert high-low==w[0]==formula(m,r)
    assert all(sum(w[i]*f[i][j] for i in range(3))==
               sum(w[i]*f[i][j] for i in range(3,5)) for j in range(4))
    count=0
    for profile in profiles(n):
        moment=F(n,*profile)
        h=Q(int(profile==P[0]))-sum(lam[i]*moment[i] for i in range(3))
        assert low<=h<=high,(n,profile,low,h,high)
        count+=1
    return count,w[0]

def check_published():
    p=Path(__file__).resolve().parents[1]/'certificates'/'three_subset_n24_120.json'
    docs=json.loads(p.read_text(encoding='utf-8'))['degrees']
    assert [r['n'] for r in docs]==list(range(24,121))
    checked=0
    for d in docs:
        n=d['n']
        if n<48:continue
        m,r=divmod(n,4)
        assert formula(m,r)==Q(d['C']),('formula finite conflict',n,d['C'],formula(m,r))
        checked+=1
    print('PASS ALL',checked,'PREVIOUSLY CERTIFIED DEGREES n=48..120')

def main():
    check_published()
    cases=[48,49,50,51,79,80,81,82,83,119,120,121,122,123,124,161,162,163,164,201,202,203,204]
    total=0
    for n in cases:
        num,value=check_one(n)
        total+=num
        print('PASS n=%d EXACT_C=%s full_cycle_types=%d'%(n,value,num),flush=True)
    print('INDEPENDENT FRACTIONAL PRIMAL-DUAL REPLAY PASSED',
          len(cases),'DEGREES,',total,'ALL CYCLE TYPE INEQUALITIES')

if __name__=='__main__':
    main()
