#!/usr/bin/env python3
"""Exact universal Cramer identities for all four triple-action primal families.

Polynomials over Q are coefficient lists in m. Determinants are expanded by
all 120 Leibniz terms. No CAS, solver, floating point or assert is used.
"""
from fractions import Fraction as F
from itertools import permutations
import json


def need(ok, message):
    if not ok: raise RuntimeError(message)


def trim(p):
    p=list(p)
    while len(p)>1 and p[-1]==0: p.pop()
    return tuple(p)


def add(a,b):
    return trim(tuple((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                      for i in range(max(len(a),len(b)))))


def scale(a,c): return trim(tuple(c*x for x in a))
def sub(a,b): return add(a,scale(b,-1))
def const(x): return (F(x),)


def mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return trim(out)


def coeff(a,j): return a[j] if j<len(a) else F(0)


def determinant(A):
    out=const(0)
    for p in permutations(range(5)):
        parity=sum(p[i]>p[j] for i in range(5) for j in range(i+1,5))%2
        term=const((-1)**parity)
        for i in range(5): term=mul(term,A[i][p[i]])
        out=add(out,term)
    return out


def orbitals(n,x,y,z):
    n1=sub(n,const(1));n2=sub(n,const(2))
    N=scale(mul(mul(n,n1),n2),F(1,6))
    M1=scale(mul(n2,add(scale(n,2),mul(sub(n,const(3)),x))),F(1,2))
    M2=add(add(scale(mul(mul(n2,x),sub(x,const(1))),F(1,2)),
                mul(add(x,const(1)),sub(n,x))),mul(sub(n,const(4)),y))
    M3=add(add(scale(mul(mul(x,sub(x,const(1))),sub(x,const(2))),F(1,6)),
                mul(x,y)),z)
    return [sub(add(sub(N,M1),M2),M3),
            add(sub(M1,scale(M2,2)),scale(M3,3)),sub(M2,scale(M3,3)),M3]


def verify(r):
    m=(F(0),F(1));n=(F(r),F(4));zero=const(0)
    K=(sub(n,add(m,const(2 if r<2 else 3))),zero,zero)
    H=(zero,add(scale(m,2),const(-1 if r==1 else 1 if r==2 else 0)),
       const(1 if r%2 else 0))
    E=(sub(m,const(3 if r==0 else 2)),zero,add(m,const(1 if r<2 else 0)))
    types=[(n,zero,zero),K,H,(sub(n,const(2)),const(1),zero),E]
    moments=[orbitals(n,*t) for t in types]
    A=[[const(1 if i<3 else 0) for i in range(5)],
       [const(0 if i<3 else 1) for i in range(5)]]
    A += [[scale(moments[i][j],1 if i<3 else -1) for i in range(5)]
          for j in range(3)]
    rhs=[const(1),const(1),zero,zero,zero]
    D=determinant(A)
    need(len(D)==10 and coeff(D,9)==-192,'wrong determinant leading term')
    numerators=[]
    for j in range(5):
        matrix=[list(row) for row in A]
        for i in range(5): matrix[i][j]=rhs[i]
        numerators.append(determinant(matrix))
    # Complete polynomial Cramer identities, not merely leading coefficients.
    for i in range(5):
        lhs=const(0)
        for j in range(5): lhs=add(lhs,mul(A[i][j],numerators[j]))
        need(lhs==mul(D,rhs[i]),'Cramer polynomial identity failed')
    PI,PK,PH,QT,QE=numerators
    need(coeff(PI,9)==-192 and coeff(QT,9)==-192,'probability limits')
    need(len(PK)==9 and coeff(PK,8)==-768,'p_K leading numerator')
    need(len(PH)==9 and coeff(PH,8)==-96,'p_H leading numerator')
    need(len(QE)==9 and coeff(QE,8)==-256,'q_E leading numerator')
    need(len(sub(D,PI))==9 and coeff(sub(D,PI),8)==-864,'1-p_I coefficient')
    need(len(sub(D,QT))==9 and coeff(sub(D,QT),8)==-256,'1-q_T coefficient')
    need(add(add(PI,PK),PH)==D and add(QT,QE)==D,'normalization identities')
    # Distinct concrete classes and nonnegative short-cycle counts for m>=6.
    for x,y,z in types:
        remainder=sub(sub(sub(n,x),scale(y,2)),scale(z,3))
        need(remainder==zero or (coeff(remainder,1)>=0 and
             coeff(remainder,0)+6*coeff(remainder,1)>=4),'class not realizable')
        for p in (x,y,z):
            need(len(p)<=2 and coeff(p,1)>=0 and coeff(p,0)+6*coeff(p,1)>=0,
                 'negative short-cycle count')
    need(len(set(types))==5,'class supports not distinct as polynomials')
    ordered=[types[i][0] for i in (0,3,1,4,2)]
    for a,b in zip(ordered,ordered[1:]):
        difference=sub(a,b)
        need(coeff(difference,1)>=0 and
             coeff(difference,0)+6*coeff(difference,1)>0,
             'support fixed-point counts collide for m>=6')
    return {'residue':r,'D_m9':str(coeff(D,9)),'D_m8':str(coeff(D,8)),
        'PI_m9':str(coeff(PI,9)),'PI_m8':str(coeff(PI,8)),
        'PK_m8':str(coeff(PK,8)),'PH_m8':str(coeff(PH,8)),
        'QT_m9':str(coeff(QT,9)),'QT_m8':str(coeff(QT,8)),
        'QE_m8':str(coeff(QE,8)),
        'determinant_coefficients_low_to_high':list(map(str,D)),
        'numerators_coefficients_low_to_high':[list(map(str,p)) for p in numerators],
        'identities':'all five polynomial equations and both mass sums checked',
        'limits':['9/2','4','1/2','4/3']}


def main():
    report={'schema':'triple-primal-cramer-polynomials-v1','status':'PASS',
        'arithmetic':'fractions.Fraction; full polynomial coefficient comparison',
        'rows':[verify(r) for r in range(4)],
        'scope':'universal polynomial identities and asymptotic coefficients; eventual positivity follows analytically from positive leading ratios'}
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
