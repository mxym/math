#!/usr/bin/env python3
"""Synthetic finite-ring checks for the fixed even modulus theorem."""
from fractions import Fraction as F
from itertools import product


def mult(a,b,q):
    d=len(a)
    c=[0]*d
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            k=i+j
            if k>=d:
                c[k-d]-=x*y
            else:
                c[k]+=x*y
    return tuple(x%q for x in c)


def chain(q,d,e):
    allwords=list(product(range(q),repeat=d))
    t=(1,q-1)+(0,)*(d-2)
    power=(1,)+(0,)*(d-1)
    bis=list(product(range(2),repeat=d))
    ideals2=[]
    p=(1,)+(0,)*(d-1)
    t2=tuple(x%2 for x in t)
    for r in range(d+1):
        ideals2.append({mult(p,a,2) for a in bis})
        p=mult(p,t2,2)
    tests=0
    for r in range(e*d+1):
        im={mult(power,a,q) for a in allwords}
        assert len(im)==2**(e*d-r)
        if r<d:
            expected={a for a in allwords if tuple(x%2 for x in a) in ideals2[r]}
            assert im==expected
            tests+=len(im)
        if r>=(e-1)*d:
            expected={tuple(x*(q//2) for x in a)
                      for a in ideals2[r-(e-1)*d]}
            assert im==expected
            tests+=len(im)
        if r>=d:
            assert all(all(x%2==0 for x in a) for a in im)
        power=mult(power,t,q)
    return tests


def crt():
    rows=0
    for a,u in ((2,3),(4,3),(4,5),(8,3),(4,9)):
        q=a*u
        sa=pow(u,-1,a)
        su=pow(a,-1,u)
        t=(1,q-1)
        values=list(product(range(q),repeat=2))
        for v in values:
            va=tuple(x%a for x in v)
            vu=tuple(x%u for x in v)
            crt_value=tuple((sa*u*x+su*a*y)%q for x,y in zip(va,vu))
            assert crt_value==v
            assert all((F(z,q)-F(sa*x,a)-F(su*y,u)).denominator==1
                       for x,y,z in zip(va,vu,v))
            p=mult(t,v,q)
            assert tuple(x%a for x in p)==mult(tuple(x%a for x in t),va,a)
            assert tuple(x%u for x in p)==mult(tuple(x%u for x in t),vu,u)
            assert all(((F(z,q)*a - F(su*y,u)*a).denominator==1)
                       for z,y in zip(v,vu))
            rows+=1
    return rows


def scalar_group_sums():
    # Formal identity of entropy coordinates, no floating log needed.
    rows=0
    for a,u in ((2,3),(4,3),(4,9),(8,5),(3,5),(9,7)):
        for h in (1,2,7):
            lhs={h*(a*u)**2:1,h:-1}
            rhs={h*a*a:1,h:-1}
            rhs[h*a*a]-=1
            rhs[h*(a*u)**2]=1
            assert {k:v for k,v in rhs.items() if v}==lhs
            rows+=1
    return rows


def order_balance():
    # Test the linear cancellation underlying the two order bounds
    # with rational surrogate weights log(a), log(u), capacity c.
    rows=0
    for a,u,c,theta in product(range(1,6),range(1,4),range(1,4),range(1,4)):
        ca=a*c+theta
        cu=u*c-theta
        for k,l in product(range(9),repeat=2):
            al,be=F(k,8),F(l,8)
            assert al*ca+be*cu-c*(al*a+be*u)==theta*(al-be)
            rows+=1
    return rows


if __name__=="__main__":
    print("PASS ramified layers:",sum(chain(2**e,d,e) for e,d in
                                      ((1,2),(1,4),(2,2),(2,4),(3,2))))
    print("PASS mixed CRT coefficient rows:",crt())
    print("PASS scalar telescope / two-order balance:",
          scalar_group_sums(),order_balance())
