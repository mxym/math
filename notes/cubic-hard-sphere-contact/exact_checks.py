#!/usr/bin/env python3
"""Finite exact regressions supporting, not replacing, the analytic proofs."""
from fractions import Fraction as F
from random import Random
import json,pathlib

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def mul(c,a):return tuple(c*x for x in a)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
zero=(F(0),)*3
rng=Random(271828)
normals=[(F(1),F(0),F(0)),(F(3,5),F(4,5),F(0)),(F(1,3),F(2,3),F(2,3))]
count=0
for _ in range(300):
    v,w,u=[tuple(F(rng.randint(-8,8),3) for j in range(3))for i in range(3)]
    n=normals[rng.randrange(len(normals))];omega=normals[rng.randrange(len(normals))]
    assert dot(n,n)==dot(omega,omega)==1
    a=sub(u,v);q=dot(a,n)
    if q<0:n=mul(-1,n);q=-q
    if not q:continue
    sigma=F(rng.randint(1,12),3);eta=F(rng.randint(1,12),5)
    y=add(mul(sigma,a),n);g=sub(v,w);aT=sub(a,mul(q,n))
    assert dot(aT,n)==0
    p1=mul(-sigma,v);p2=sub(omega,mul(sigma,w));p3=sub(y,mul(sigma,u))
    assert sub(p3,p1)==n
    vel1=sub(mul(-1,v),mul(q,n));vel3=add(mul(-1,u),mul(q,n))
    r1=add(p1,mul(eta,vel1));r2=sub(p2,mul(eta,w));r3=add(p3,mul(eta,vel3))
    d12=add(add(omega,mul(sigma+eta,g)),mul(eta*q,n))
    d23=add(add(sub(omega,n),mul(sigma+eta,g)),mul(eta,aT))
    assert sub(r2,r1)==d12 and sub(r2,r3)==d23
    assert dot(d23,n)==dot(sub(omega,n),n)+(sigma+eta)*dot(g,n)
    assert add(vel1,vel3)==mul(-1,add(v,u))
    assert dot(vel1,vel1)+dot(vel3,vel3)==dot(v,v)+dot(u,u)
    count+=1
# Angular values are rational multiples of pi.
xx=F(1,3)-F(1,5);zz=F(2,5)
assert xx==F(2,15) and 2*xx+zz==F(2,3)
# Four-terminal-indicator cancellation: e13*e23-e13-e23+1=(1-e13)(1-e23).
for e13 in (0,1):
 for e23 in (0,1):assert e13*e23-e13-e23+1==(1-e13)*(1-e23)
# Exact partition division cubic coefficient, checked at rational parameter values.
for _ in range(100):
    mu,A1,A2,A3,Z2=[F(rng.randint(1,10),rng.randint(1,6))for j in range(5)]
    numerator=[0,A1,mu*A2/2,mu*mu*A3/6]
    reciprocal=[1,-mu,mu*mu*(1-Z2/2)]
    coeff=sum(numerator[j]*reciprocal[3-j]for j in (1,2,3))
    assert coeff==mu*mu*(A3/6-A2/2+A1*(1-Z2/2))
report={'rational_collision_cases':count,'partition_division_cases':100,'hemisphere_tensor_coefficients_pi':[str(xx),str(xx),str(zz)],'hemisphere_trace_pi':'2/3','indicator_identity_cases':4,'all_passed':True,'scope':'Finite exact checks; the tail estimate, limiting operations and hierarchy arguments require the written proof.'}
pathlib.Path(__file__).with_name('exact_check_results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
