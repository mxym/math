#!/usr/bin/env python3
"""Exact arithmetic controls for thin logarithmic bursts.

The checker verifies the local geometry and budget inequalities on deliberately
small samples; it does not construct the probabilistic avoiding set.
"""

from fractions import Fraction as F
from random import Random

checks = 0


def check(c):
    global checks
    checks += 1
    assert c


def floor(x):
    return x.numerator // x.denominator


def log_lower(q, terms=24):
    """Positive lower series for ln q; q >= 1."""
    z = (q - 1) / (q + 1)
    return 2 * sum(z**(2*i+1) / (2*i+1) for i in range(terms))


def tree(B, d, g, L, start=0):
    """Return span and windows, with each block's whole local span."""
    if d == 1:
        span = B*L+(B-1)*g
        return span, [(start+j*(L+g), L, L) for j in range(B)]
    prev, _ = tree(B,d-1,g,L)
    u = start
    out = []
    for j in range(B):
        length = g+prev
        _, children = tree(B,d-1,g,L,u+length+g)
        out.append((u,length,2*length))
        out.extend(children)
        u += 2*length+g
    return u-start-g, out


for B in range(2,6):
    for d in range(1,5):
        for g in range(1,3):
            for L in range(2,7):
                T, all_windows = tree(B,d,g,L,4)
                check(T <= (2*B)**d*(L+2*g))
                check(len(all_windows) == sum(B**i for i in range(1,d+1)))
                check(all_windows[0][0] == 4)
                check(all_windows[-1][0]+all_windows[-1][1] == 4+T)
                check(all(len_ >= L and span <= 2*len_ 
                          for _,len_,span in all_windows))
                for (u,l,s),(v,h,t) in zip(all_windows,all_windows[1:]):
                    check(v-u-l == g)


R = Random(271124)
for trial in range(240):
    H = R.randrange(700,1500)
    X = H*R.randrange(8,1000)
    rho = F(H,X)
    S = F(R.randrange(2,21),R.randrange(2,14))
    s0 = S
    s1 = S*(1+rho/16)
    k = R.randrange(-10,11)
    U = floor(S*X-k)
    T = floor(s0*H/32)
    delta = 4/s0
    D = R.randrange(4,10)
    check(0<rho<=F(1,8) and U>abs(k) and T<=U)
    # Fill the supplied burst with a perturbed progression containing both ends.
    Z = [X-H]
    while Z[-1] < X+H:
        Z.append(min(X+H,Z[-1]+R.randrange(1,D+1)))
    Z.extend((10**q)*X for q in range(1,5))
    ZZ = [Z[0]]
    for z in Z[1:]:
        if z > ZZ[-1]+delta:
            ZZ.append(z)
    check(all(v-u>delta for u,v in zip(ZZ,ZZ[1:])))
    Dstar = s1*(delta+D+2)
    for idx in range(5):
        s = s0+(s1-s0)*idx/4
        check(abs(F(U+k,1)/s-X)<F(H,4))
        check(abs(F(U+T+k,1)/s-X)<F(H,4))
        W = [s*z-k for z in ZZ]
        check(W[0]<U<W[-1])
        for l in (T, floor(F(T,2))):
            if l<2*Dstar:
                continue
            u = U+(T-l)//2
            left = next(i for i in range(len(W)-1,-1,-1) if W[i]<=u)
            right = next(i for i in range(len(W)) if W[i]>=u+l)
            check(all(ZZ[i] >= X-H and ZZ[i+1] <= X+H and
                      4 < W[i+1]-W[i] < Dstar for i in range(left,right)))
            check(F(right-left-1)>=l/(2*Dstar))
    # A candidate is active for some real s of the entire compact sector
    # iff the range of s*z-k intersects this open window.
    P = 0
    root_windows = [(U,T//2),(U+T//2,T-T//2)]
    for u,l in root_windows:
        for z in ZZ:
            if s1*z-k>u and s0*z-k<u+l:
                check(X-H<=z<=X+H)
                P += 1
    check(P<=2*(1+2*H/delta))


for i in range(160):
    target = F(R.randrange(1001,1800),1000)
    a = F(1)
    rhos = []
    while a < target:
        rho = F(R.randrange(1,17),128)
        check(rho <= F(1,8))
        s = a*(1+rho/16)
        check(s > a and s < 2*target)
        # ln(1+x) >= x/(1+x) >= x/2; only exact rational comparisons here.
        check((rho/16)/(1+rho/16)>=rho/32)
        rhos.append(rho)
        a = s
    check(sum(rhos)<=32*log_lower(target)+F(1,8))
    w = F(1,100)
    tau = w/(192*target+1)
    check(6*tau*sum(rhos)<w)


for l in range(2,30):
    for P in range(1,78):
        lines = P*(3+2**(2*l+3))
        check(20*(lines+5)**2<=5120*P*P*2**(4*l))


# Compare enormous example centers symbolically via their exact dyadic logs.
for j in range(2,13):
    logX = 1 << (j**4)
    next_logX = 1 << ((j+1)**4)
    logHfixed = 1 << (j**3)
    check(logX-logHfixed>3)
    check(next_logX-logX>j)
    check(logX>2*(32*j).bit_length())
    check(j**4>=j*j*j)
# Exact model controls for the full arithmetic progressions in each burst.
for j in range(2,25):
    H=6*j*j+1
    fill=[-H+i*j for i in range(2*H//j+1)]
    check(fill[0] == -H and H-fill[-1] < j)
    check(all(y-x==j for x,y in zip(fill,fill[1:])))
    for s in range(-H,H-j):
        check(any(s<=v<=s+j+1 for v in fill))


print({"exact_checks":checks,"note":"finite controls, not a random-cover computation"})
