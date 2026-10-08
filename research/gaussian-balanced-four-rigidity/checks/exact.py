#!/usr/bin/env python3
"""Exact finite diagnostics, not a proof of Gaussian rigidity or root uniqueness."""
from fractions import Fraction as Q
import itertools
import json

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def determinant(rows):
    a=[[Q(x) for x in row] for row in rows]
    n=len(a); det=Q(1)
    for k in range(n):
        pivot=next((j for j in range(k,n) if a[j][k]),None)
        if pivot is None:
            return Q(0)
        if pivot!=k:
            a[k],a[pivot]=a[pivot],a[k];det=-det
        p=a[k][k];det*=p
        for j in range(k+1,n):
            factor=a[j][k]/p
            for l in range(k,n):
                a[j][l]-=factor*a[k][l]
    return det

def main():
    counts={}
    n=0
    for c in [Q(0),Q(1,8),Q(1),Q(3)]:
        for a,b in itertools.product([Q(1,4),Q(1),Q(3)],repeat=2):
            need(Q(1,4)+c*a*b>0,'same-sign missing facet');n+=1
    counts['radon_same_sign']=n

    n=0
    for t in [Q(0),Q(1,4),Q(1),Q(2)]:
        for excess in [Q(0),Q(1,3),Q(1),Q(2)]:
            s=t+excess
            for x in [Q(-3),Q(-1),Q(0),Q(1),Q(3)]:
                y=-t-s-x
                F=t*t+s*s+x*x+y*y
                need(F>=4*t*t,'projection bound');n+=1
    counts['projection_cases']=n

    n=0
    for T in [Q(0),Q(1,9),Q(1),Q(3)]:
        for slack in [Q(0),Q(1,7),Q(2)]:
            F=4*T+slack
            B=F+2*T
            need(F+4*T<=4*B/3,'interior elimination');n+=1
    counts['interior_elimination']=n

    n=0
    for a,b,c in itertools.product([Q(1,4),Q(1,2),Q(1),Q(2)],repeat=3):
        if a<=b:
            continue
        lhs=a**4*(b*b+c*c)-b**4*(a*a+c*c)
        rhs=(a*a-b*b)*(a*a*b*b+c*c*(a*a+b*b))
        need(lhs==rhs and rhs>0,'disphenoid comparison');n+=1
    counts['disphenoid_cross_product']=n

    n=0
    for c,h in itertools.product([Q(1,10),Q(1,4),Q(1,2),Q(9,10)],
                                 [Q(0),Q(1,2),Q(1),Q(3,2)]):
        mat=[[Q(0) for _ in range(9)] for _ in range(9)]
        for i in range(3):
            for j in range(3):mat[i][j]=c if i==j else -(c+1)/2
            mat[3+2*i][3+2*i]=-h
            mat[3+2*i][4+2*i]=1
            mat[4+2*i][3+2*i]=c-1
            mat[4+2*i][4+2*i]=-h
        det=determinant(mat)
        expected=-(3*c+1)**2/4*(1+h*h-c)**3
        need(det==expected and det!=0,'nine-variable linearized determinant');n+=1
    counts['nine_variable_systems']=n

    need(1-Q(9,16)+Q(9,16)**2/2-Q(9,16)**3/6-Q(9,16)==Q(29,8192),
         'strict Taylor margin')
    need(Q(3,8)*Q(87,128)-Q(1,4)==Q(5,1024),'quantile margin')
    counts['profile_margins']=2
    need(Q(1,4)-Q(1,4)==0,'wrong-sign control did not exhibit zero weight')
    need(not (Q(0)+4*1<=4*Q(2)/3),'removing projection premise unexpectedly sound')
    need(not (Q(6)+4*1<=4*Q(1)/3),'removing merge premise unexpectedly sound')
    # c=1, h=0 collapses the antisymmetric block: the hypothesis c<1 matters.
    need((Q(1)-1-Q(0)**2)==0,'local-isolation endpoint control')
    print(json.dumps({'status':'PASS','scope':'finite exact algebraic diagnostics only',
        'cases':counts,'total_cases':sum(counts.values()),'negative_controls':4,
        'gaussian_endpoint_certified':False,'global_root_exclusion':False},indent=2,sort_keys=True))

if __name__=='__main__':
    main()
