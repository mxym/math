#!/usr/bin/env python3
"""Eisenstein-integer determinant enumeration and exact proof thresholds."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations

Z=(0,0)
O=(1,0)
W=(0,1)


def add(a,b):
    return (a[0]+b[0],a[1]+b[1])


def neg(a):
    return (-a[0],-a[1])


def mul(a,b):
    x,y=a
    z,w=b
    return (x*z-y*w,x*w+y*z-y*w)


def length2(a):
    x,y=a
    return x*x-x*y+y*y


def det(R):
    a,b,c=R[0]
    x,y,z=R[1]
    u,v,w=R[2]
    first=mul(a,add(mul(y,w),neg(mul(z,v))))
    second=mul(b,add(mul(x,w),neg(mul(z,u))))
    third=mul(c,add(mul(x,v),neg(mul(y,u))))
    return add(add(first,neg(second)),third)


def main():
    t=add(O,W)
    assert length2(t)==1 and mul(mul(t,t),t)==neg(O)
    V=[]
    for wj in (O,W,mul(W,W)):
        V.append((Z,O,neg(mul(t,wj))))
    for wj in (O,W,mul(W,W)):
        V.append((neg(wj),Z,O))
    for wj in (O,W,mul(W,W)):
        V.append((O,neg(wj),Z))
    freq=Counter()
    for ijk in combinations(range(9),3):
        d=length2(det([V[i] for i in ijk]))
        freq[d]+=1
        assert (d==0)==(len({i//3 for i in ijk})==1)
    assert dict(freq)=={0:3,1:18,3:54,4:9}
    e=F(1,100000)
    D=F(1,10000)
    p=F(1,2)+e
    assert 7*(F(1,2)-11*D)>3
    assert 36*D < F(1,72)
    assert 24*D < F(1,100)
    assert e+2*e**2<=2*e
    assert D-2*e>e/3
    assert p*(1-e)-F(1,2)>e/3
    assert p*(1-p)>F(49,100)**2
    assert F(99,100)**2<=1-F(1,100)
    assert 2*F(7,10)**2<1
    assert F(49,100)*F(99,100)*F(7,10)>F(1,4)
    assert F(1,4)-F(3,2)*F(1,10)==F(1,10)
    assert e/100>(e/3)**2
    print("baseline: 84 exact Eisenstein determinants; norm-square counts 0:3, 1:18, 3:54, 4:9")
    print("uniform gap: near-ray and far-region rational guard inequalities PASS")


if __name__=='__main__':
    main()
