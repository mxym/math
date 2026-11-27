#!/usr/bin/env python3
"""Independent run enumeration, spectral limits and exact parameter checks."""

from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from math import comb
from itertools import product


def path_distribution(a,b,n):
    # Transition 0 -> 1 has mass b, 1 -> 0 has mass a.
    weights=[F(0)]*(n+1)
    for seq in product((0,1),repeat=n):
        prev=0
        prob=F(1)
        for nxt in seq:
            prob*=((1-b,b),(a,1-a))[prev][nxt]
            prev=nxt
        weights[sum(seq)]+=prob
    return weights


def run_distribution(a,b,n):
    result=[(1-b)**n]
    for w in range(1,n+1):
        z=n-w
        total=F(0)
        for r in range(1,min(w,z+1)+1):
            one=comb(w-1,r-1)
            if r<=z:
                total+=(one*comb(z,r)*(a*b)**r
                        *(1-a)**(w-r)*(1-b)**(z-r))
            total+=(one*comb(z,r-1)*b**r*a**(r-1)
                    *(1-a)**(w-r)*(1-b)**(z-r+1))
        result.append(total)
    return result


def run_checks():
    count=0
    for q,u,n in product((2,3,5,11), (F(1,15),F(2,9),F(6,7),F(1)),
                         (1,2,3,5,8,10)):
        a,b=u/q,u*(q-1)/q
        ref=path_distribution(a,b,n)
        run=run_distribution(a,b,n)
        assert ref==run and sum(run)==1
        count+=1
    print(f"independent exact run counts: {count} full path-vs-runs distributions")


def times(x,y):
    return tuple(tuple(sum(x[i][k]*y[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def logmgf(q,u,n,s):
    a,b=u/q,u*(q-1)/q
    w=(s*u).exp()
    mat=((1-b,b*w),(a,(1-a)*w))
    acc=((D(1),D(0)),(D(0),D(1)))
    while n:
        if n & 1:
            acc=times(acc,mat)
        n>>=1
        mat=times(mat,mat)
    return (acc[0][0]+acc[0][1]).ln()


def calc_rate(q,d):
    a=D(1)/q
    b=1-a
    ab=a*b
    s=(2*d-1)*(ab/(d*(1-d))).sqrt()-(b-a)
    gap=((s+b-a)**2+4*ab).sqrt()
    k=(s-1+gap)/2
    j=s*d-k
    dd=2*ab/gap**3
    assert abs(j-(((1-a)*(1-d)).sqrt()-(a*d).sqrt())**2) < D("1e-55")
    return s,k,j,dd


def spectral_checks():
    cases=0
    for q,d in product((2,3,7,19),(D("0.05"),D("0.25"),D("0.4"))):
        with localcontext() as ctx:
            ctx.prec=74
            ctx.Emin, ctx.Emax=-999_999_999,999_999_999
            a=D(1)/q
            b=1-a
            s,k,j,dd=calc_rate(q,d)
            assert s<0 and j>0 and dd>0
            # Through direct non-symmetric matrix powers, not a Perron formula.
            # u -> 0, L -> infinity, L*u -> 0.
            for u,n in ((D("1e-9"),10**13),(D("1e-15"),10**23)):
                L=n*u
                K=logmgf(q,u,n,s)
                assert abs(K/L-k) < D("3e-4")
                t=D("0.37")
                h=t/L.sqrt()
                v=logmgf(q,u,n,s+h)-K-d*t*L.sqrt()
                assert abs(v-dd*t*t/2) < D("8e-3")
                cases+=1
    print(f"independent spectral/tilt checks: {cases} scaled direct matrix powers")


def comparison_checks():
    with localcontext() as ctx:
        ctx.prec=70
        h=lambda x: -x*x.ln()-(1-x)*(1-x).ln()
        d=D(1)/4
        byfield={}
        for q0 in (2,3,4,5,7):
            for q in (q0,q0+1,2*q0+1,83):
                for dh in (D("0.05"),D("0.25"),D("0.49")):
                    j0=calc_rate(q0,dh)[2]
                    j=calc_rate(q,dh)[2]
                    H=(h(dh)+dh*D(q-1).ln())/D(q).ln()
                    H0=(h(dh)+dh*D(q0-1).ln())/D(q0).ln()
                    assert j>=j0 and H<=H0
            byfield[q0]=calc_rate(q0,d)[2]
        j=byfield[2]
        eps_exp=64*D(4)/3*j
        # Source (5) gives N^-6, our fixed-ring lower tail has exponent 1-A > -6.
        assert D(1)/100 < (2/D(2).ln())*((1-(-D(1)).exp())/(1+(-D(1)).exp()))/16
        assert 64>16 and 1<eps_exp<7
        assert 18*j>1>12*j
        assert D(1)/100<1-h(d)/D(2).ln()
        # Rational enclosures remove reliance on printed decimal comparisons.
        assert F(107,64)**2<3<F(125,64)**2
        assert F(5,3)**2<3<F(16,9)**2
        print("Z4 comparison: C=64 failure log-exponent "
              f"{1-eps_exp:.9f} vs required <= -6; C=9 phase split")
    print("PASS independent runs / spectral / parameter audit")


if __name__=="__main__":
    run_checks()
    spectral_checks()
    comparison_checks()
