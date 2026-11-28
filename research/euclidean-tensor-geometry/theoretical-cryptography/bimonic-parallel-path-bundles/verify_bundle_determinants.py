"""Fixed finite Sylvester examples and integer parameter checks."""
from fractions import Fraction as Q
from itertools import product
from math import prod

def mul_linear(coeff,a):
    p=[0]*(len(coeff)+1)
    for i,c in enumerate(coeff):
        p[i]+=c
        p[i+1]-=a*c
    return p

def polynomial(roots):
    p=[1]
    for a in roots: p=mul_linear(p,a)
    return p

def evalp(coeff,t):
    b=0
    for a in coeff: b=b*t+a
    return b

def det(A):
    a=[list(map(Q,row)) for row in A]
    v=Q(1)
    for i in range(len(a)):
        j=next((j for j in range(i,len(a)) if a[j][i]!=0),None)
        if j is None: return 0
        if i!=j: a[i],a[j]=a[j],a[i]; v=-v
        z=a[i][i]
        v*=z
        for k in range(i+1,len(a)):
            s=a[k][i]/z
            for l in range(i,len(a)): a[k][l]-=s*a[i][l]
    return v

def res(P,Q0):
    m,k=len(P)-1,len(Q0)-1
    return det([[0]*i+P+[0]*(k-1-i) for i in range(k)]+
               [[0]*i+Q0+[0]*(m-1-i) for i in range(m)])

tests=0
for r,t in product(range(2,8),range(-3,10)):
    roots=[i*(t-5)+11 for i in range(1,r+1)]
    P=[polynomial(roots[:j]+roots[j+1:]) for j in range(r)]
    for z in (0,1,2,3):
        B=list(map(sum,zip(*[[x*z**j for x in V] for j,V in enumerate(P[1:])])))
        assert B[0]>0
        v=res(P[0],B)
        assert v==prod(evalp(B,a) for a in roots[1:])
        if z==1: assert (v==0)==(t==5)
        tests+=1

# Both small candidate parameters can fail before one works.
for t in range(-100,101):
    P=[1,-2*t-1,t*(t+1)]
    vals=[res(P,[1+l,-t-1+l*(-t+1)]) for l in (0,1,2)]
    assert vals[:2]==[0,0] and vals[-1]!=0

# The 3-path example has three distinct intersection source values.
for t in (Q(0),Q(5,2),Q(5),Q(6),Q(7),Q(-1)):
    a,b,c=2*t+1,3*t-4,t+1
    A,B,C=polynomial([a,b]),polynomial([b,c]),polynomial([c,a])
    assert res(A,B)==res(B,C)==res(C,A)==0
    val=res(A,[x+y for x,y in zip(B,C)])
    assert val==-(a-b)**2*(a-c)*(b-c)
    assert (val==0)==(t in (0,Q(5,2),5))

print("PASS bundle determinants: %d leave-one-out evaluations; 201 sharp parameter-grid cases; 6 three-path specializations." % tests)
