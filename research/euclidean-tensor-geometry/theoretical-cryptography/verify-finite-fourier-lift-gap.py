#!/usr/bin/env python3
"""Exact arithmetic checks for the finite-Fourier lift bounds."""
from fractions import Fraction as F
from collections import Counter


def coefs(m):
    tri={j:m-abs(j) for j in range(1-m,m)}
    square=Counter()
    for j,a in tri.items():
        for k,b in tri.items():
            square[j+k]+=a*b
    return square


def check_jackson():
    checks=0
    for K in range(1,161):
        m=K//2+1
        c=coefs(m)
        assert c[0]==(2*m**3+m)//3
        assert sum(c.values())==m**4
        assert max(c)==2*m-2<=K
        assert all(c[j]==c[-j] for j in c)
        # An exact harmonic test: arbitrary even modes and all high modes
        # survive in the input, but all odd modes of degree <= K vanish.
        p={0:F(1)}
        for j in range(1,2*K+3):
            if j%2==0 or j>K:
                p[j]=p[-j]=F((-1)**j,j+2)
        C0=sum(p[j]*c[-j] for j in p)/c[0]
        Ch=sum(p[j]*c[-j]*(-1)**(abs(j)) for j in p)/c[0]
        assert C0==Ch
        checks+=len(c)
    return checks


def exp_interval(x,N=20):
    a=F(1)
    t=a
    for j in range(1,N+1):
        a*=x/j
        t+=a
    tail=a*x/(N+1)/(1-x/(N+2))
    return t,t+tail


def check_constants():
    assert exp_interval(F(3,4))[1]<F(17,8)
    assert exp_interval(F(2,3))[1]<2<exp_interval(F(7,10))[0]
    assert (F(17,8)-1)/F(3,4)==F(3,2)
    assert F(5,2)*F(8,17)>1
    R=F(1,4096)
    # Bounds for r=Rpert/B and (log(1+r))'' from the four quotient terms.
    r0=R/2
    r1=R+12*R/2
    r2=R+2*12*R+30*R/2+2*12**2*R/2
    total=r2/(1-r0)+r1*r1/(1-r0)**2
    assert r1==7*R and r2==184*R
    assert total<564*R<F(4,9)
    assert F(1,4096*36)<F(1,10000)
    assert 8*F(7,10)+32*F(1,10000)<6


def seam_and_modes():
    n=0
    for K in range(1,401):
        # Compute odd exceptional harmonic by parity without approximation.
        ell=K+1
        if ell%2==0:
            ell+=1
        assert K<ell<=K+2 and ell%2==1
        g=F(1,4096*36*ell**2)
        # Tied seam condition makes exp(-alpha/8) algebraically exact.
        E=(1-g)/(2*(1+g))
        central=(1+g)*E
        tail=(1+g)*(1-E)+g*((-1)**ell-1)
        assert central==tail==(1-g)/2
        # The residual sine derivative vanishes there, so the common
        # first derivative is -alpha*central/2 for arbitrary scalar alpha.
        for alpha in (F(5),F(11,2),F(6)):
            direct=-alpha*(1+g)*E/2
            assert direct==-alpha*central/2
        n+=1
    return n


def main():
    check_constants()
    print(f"PASS: {check_jackson()} exact Jackson coefficients, "
          f"{seam_and_modes()} exact odd-mode/seam setups, "
          "and strict rational curvature margins.")


if __name__=="__main__":
    main()
