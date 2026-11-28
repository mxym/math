#!/usr/bin/env python3
"""Exact rational checks and logarithm enclosures for the Potts entropy curves."""
from fractions import Fraction as F
from functools import lru_cache

if not __debug__:
    raise RuntimeError("run without -O")


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def neg(a):
    return -a[1], -a[0]


def mul(a, b):
    ab = [x*y for x in a for y in b]
    return min(ab), max(ab)


def scale(t, a):
    return mul((t,t),a)


def div(a, b):
    assert b[0]>0
    return mul(a, (1/b[1],1/b[0]))


def series(r):
    assert 1 <= r <= 2
    t=(r-1)/(r+1)
    s=sum(2*t**(2*j+1)/F(2*j+1) for j in range(30))
    return s, s+2*t**61/(61*(1-t*t))


LN2 = series(F(2))


@lru_cache(maxsize=1024)
def logarithm(r):
    assert r>0
    exp=0
    while r<1: r*=2; exp-=1
    while r>=2: r/=2; exp+=1
    return add(series(r), scale(exp,LN2))


def psi(a,z):
    w,t=1+z,1-z/a
    return scale(F(1,a+1),add(scale(w,logarithm(w)),scale(a*t,logarithm(t))))


def derivative(a,z):
    return scale(F(1,a+1),logarithm((1+z)/(1-z/a)))


def P(a,z):
    return (1+z)*(a-z)


def inflect(a,l,z):
    R=l*l*P(a,z)/P(a,l*z)
    return add(scale(R,derivative(a,z)),neg(scale(l,derivative(a,l*z))))


def tangent(a,l,z):
    T=mul(psi(a,z),scale(l,derivative(a,l*z)))
    U=mul(psi(a,l*z),derivative(a,z))
    return add(T,neg(U))


def root(a,l,f):
    lo,hi=F(a,10**4),F(a)*(1-F(1,10**4))
    assert f(a,l,lo)[0]>0 and f(a,l,hi)[1]<0
    while hi-lo>F(1,10**13):
        t=(lo+hi)/2
        x,y=f(a,l,t)
        if x>0:lo=t
        elif y<0:hi=t
        else:raise AssertionError("logarithm enclosure did not decide midpoint")
    return lo,hi


def via_scaled_box(x, y, d=10**9):
    return x*d//1, -(-y*d//1)


def sample(a,l):
    b1,b2=root(a,l,inflect)
    t1,t2=root(a,l,tangent)
    assert 0<b1<b2<t1<t2<a
    xi=(psi(a,b1)[0],psi(a,b2)[1])
    tau=(psi(a,t1)[0],psi(a,t2)[1])
    vol=(min(psi(a,l*t1)[0],psi(a,l*t2)[0]),
         max(psi(a,l*t1)[1],psi(a,l*t2)[1]))
    eta=div(vol,tau)
    assert eta[0]>l*l
    return via_scaled_box(*xi), via_scaled_box(*tau), via_scaled_box(*eta)


def multiply(X,Y):
    p=[F(0)]*(len(X)+len(Y)-1)
    for i,x in enumerate(X):
        for j,y in enumerate(Y):
            p[i+j]+=x*y
    return p


def arithmetic():
    n=0
    for a in range(1,12):
        b=a-1
        for l in {F(-1,a),F(-1,2*a),F(0),F(1,3),F(2,3),F(1)}:
            A=multiply([b,-2],[a,b*l,-l*l])
            B=multiply([a,b,-1],[b*l,-2*l*l])
            assert [x-y for x,y in zip(A,B)]==[
                (1-l)*a*b,-2*(1-l)*a*(1+l),-(1-l)*b*l,F(0)]
            if l==-F(1,a):
                z=F(a,3)
                assert l*l*P(a,z)/P(a,l*z)==(1+z)/(a*a+z)
            q=a+1
            eps=(1-l)/q
            for k in range(1,q):
                M=(k+1)*eps+l
                assert M>0 or l==1
                r=l/M
                assert r>=-F(1,k) and r<=1
                t=F(1,3*(k+1))
                v=(1-t)/k
                assert (eps+l*t)/M==(1-r)/(k+1)+r*t
                assert (eps+l*v)/M==(1-r)/(k+1)+r*v
            n+=1
    return n


def main():
    print('exact symbolic specialization checks:',arithmetic(),flush=True)
    expected = {
        (2,F(1,2)):(57745682,102854836,256493476),
        (2,F(-1,4)):(250870415,420828230,71809561),
        (3,F(1,2)):(137093790,244987566,265671889),
        (3,F(-1,4)):(702929577,1042072294,91693197),
    }
    for (a,l), targets in expected.items():
        bounds=sample(a,l)
        assert bounds==tuple((t,t+1) for t in targets)
        print(a+1,l,bounds,flush=True)
    # Ternary coloring: output given two identical uniform letters.
    out=[sum(F(1,3)*(F(1,2) if i!=v else F(0))*
             (F(1,2) if j!=v else F(0)) for v in range(3))
         for i in range(3) for j in range(3)]
    assert out.count(F(1,6))==3 and out.count(F(1,12))==6
    assert sum(out)==1
    print("PASS exact rational Potts examples")

if __name__ == '__main__':
    main()
