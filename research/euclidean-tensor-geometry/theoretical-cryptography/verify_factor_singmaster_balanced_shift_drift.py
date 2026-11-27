#!/usr/bin/env python3
"""Exact optional replay for equal row/column shifts (d=2..256 by default)."""
from fractions import Fraction as F
from math import isqrt, prod, comb
import argparse

def exact_constants():
    for m in range(1, 513):
        j = [F(v, 2) for v in range(1 - (m % 2), m, 2) if v]
        assert sum(x*x for x in j) == F(m*(m*m-1), 24)
        assert sum(x**4 for x in j) == F(m*(m*m-1)*(3*m*m-7), 480)
    assert F(7,8)**2>F(3,4)
    assert F(53,32)*F(11,16)>1
    assert F(13,18)*F(64,63)<1
    assert F(1,2)+F(1,64)<F(3,4)
    assert (2+F(1,64))/(1-F(1,64))**2<3
    assert (2+F(1,16))/(1-F(1,64))**2<3
    assert (F(1,2)+F(1,16))/(1-F(1,64))**2<F(3,4)
    assert F(13,18)<1
    assert F(7,32)+F(1,24*64)+F(3,256*4)<F(1,4)
    assert F(49,96)+1+F(12,24)<3
    assert F(49,160)+F(1,16)+F(3,24)<F(1,2)
    assert F(1,24*16)+F(1,2*16**2)<F(1,24)
    assert (5+F(1,64))/24<F(21,100)
    assert F(21,100)+F(1,24*64)+F(3,64)<F(13,50)
    assert 9*F(13,50)+(F(1,256)+2*F(13,50))/(1-F(1,64))**2<3
    assert F(49,160)+F(13,50)**2+F(1,8)<F(1,2)
    assert F(5,24)-F(1,128)>F(1,5)
    assert F(21,100)+F(1,24*64)+F(1,128)<F(11,50)
    assert F(11,50*64)<F(1,256)
    assert (4-F(2,64)-F(3,256))/5>F(79,100)
    assert (4*F(11,50)+F(1,256))/(1-F(1,256))**2<F(9,10)
    assert (3-F(1,64))**2-2/(1-F(1,256))**2>F(34,5)
    assert (3+F(9,640))**2-2<F(36,5)
    assert F(1,5)-F(1,6*64)>F(19,100)
    assert (3-F(10,64))/480>F(59,10000)
    assert F(59,10000)*F(34,5)/2>F(1,50)
    assert F(11,50)**2/(2*(1-F(1,256)))<F(1,40)
    assert F(79,100)*F(63,64*24)>F(4,125)
    assert F(65,1920*63)<F(1,1000)
    assert F(1,15*63)<F(1,500)
    assert F(19,200)-F(36,5*320)-F(1,1000)-F(1,40)-F(3,80)>0
    assert F(1,10)+F(1,500)-2*F(1,50)-F(4,125)==F(3,100)
    assert F(1,24)/F(1,2)+F(3,100)/F(1,2)**2<F(5,24)
    assert F(1,24)/F(7,10)+F(3,100)/F(7,10)**2<F(1,8)
    for d in range(1,25):
        # Distance from E* to the first strictly higher permitted E.
        scale=1 if d%2 else 4
        translate=F(1,4) if d%2 else F(0)
        A=(F(5*d*d+1,24)-translate)*scale
        gap=F(A.numerator//A.denominator+1,scale)+translate-F(5*d*d+1,24)
        assert gap>=(F(1,8) if d%6 in (2,4) else F(5,24))

def signed_bracket_checks():
    # For fixed z, the exact centered product can be evaluated purely in E.
    # This probes the real branch without assuming any integer collision exists.
    checked=0
    for d in (8,9,11,16,25,64,128,256):
        J=[F(v,2) for v in range(1-(d%2),d,2) if v]
        for z in sorted({F(8*d),F(16*d+1,2),max(F(8*d),F(d*d,2)),F(d*d)+F(1,2)}):
            lhs=prod(z*z-F(2*j+1,2)**2 for j in range(d))
            lo=F(5*d*d+1,24)+F(d*d-1,24)/z
            hi=lo+F(3*d**4,100)/(z*z)
            def value(e):
                p=z*z-e
                factors=[(p-j*j)**2-j*j*(z-F(1,2))**2 for j in J]
                assert p>0 and min(factors)>0
                return (p if d%2 else 1)*prod(factors)
            assert value(lo)>lhs>value(hi)
            checked+=1
    assert comb(15,5)==comb(14,6)==3003
    return checked

def row(d, u, k):
    return prod(range(u+k-d+1,u+k+1))*prod(range(k+1,k+d+1))

def fast(d):
    rows = compares = 0
    sol=[]
    # z = u-d+1/2 is below the indicated strictly open cutoff.
    cutoff10 = 160*d*d if d<8 else max(80*d,(7 if d%6 in (2,4) else 5)*d*d)
    last_u = (cutoff10-6)//10+d
    for u in range(2*d,last_u+1):
        # z = u-d+1/2, x-y = z-1/2.
        rows += 1
        if u<9*d:
            l,h=0,u-d # from y-d/2 <= z
            lhs=prod(range(u-2*d+1,u+1))
            while l<=h:
                k=(l+h)//2
                rhs=row(d,u,k)
                compares+=1
                if lhs==rhs:
                    sol.append((u+k,k,comb(u+k,k)))
                    break
                if lhs<rhs: h=k-1
                else: l=k+1
            continue
        Z=2*u-2*d+1
        Z2=Z*Z
        D=6*Z2
        M=(5*d*d+1)*Z2+2*(d*d-1)*Z
        if d>=8:
            L=M//D+1
            H=(25*M+72*d**4-1)//(25*D)
        else:
            W=288*d**4
            L=max(-4*d*d+1,-(-(M-W)//D))
            H=min(4*d*d-1,(M+W)//D)
        if H<L:
            continue
        C=Z-1
        def last_k(p):
            assert p>=0
            return ((isqrt(C*C+4*p)-C)//2-d-1)//2
        a=max(0,last_k(Z2-H-1)+1)
        b=min(u-d,last_k(Z2-L))
        if a>b:
            continue
        lhs=prod(range(u-2*d+1,u+1))
        while a<=b:
            k=(a+b)//2
            rhs=row(d,u,k)
            compares+=1
            if lhs==rhs:
                sol.append((u+k,k,comb(u+k,k)))
                break
            if lhs<rhs: b=k-1
            else: a=k+1
    return rows,compares,sol

def direct(d):
    got=[]
    for n in range(2*d, 32*d*d):
        for k in range(n-2*d+1):
            if comb(n,k)==comb(n-d,k+d):
                got.append((n,k,comb(n,k)))
    return sorted(got)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--max-shift',type=int,default=256)
    ns=p.parse_args()
    assert ns.max_shift>=2
    exact_constants()
    print('exact real-branch signed brackets:',signed_bracket_checks(),flush=True)
    total=tests=0
    found=[]
    for d in range(2,ns.max_shift+1):
        rows,compares,sol=fast(d)
        total+=rows
        tests+=compares
        for item in sol:
            n,k,value=item
            assert 2*d<=n<32*d*d and 0<=k<=n-2*d
            assert comb(n,k)==comb(n-d,k+d)==value
            found.append((d,*item))
        if d<=4:
            assert sorted(sol)==direct(d)
    nonedge = [r for r in found if r[3]>1 and 2<=r[2]<=r[1]//2 and 2<=r[2]+r[0]<=(r[1]-r[0])//2]
    print('tested shifts 2..',ns.max_shift,'rows',total,'exact product comparisons',tests)
    print('all solutions beyond value 1:',[r for r in found if r[3]>1])
    print('collisions in the two left half-triangles, ignoring k=0,1:',nonedge)

