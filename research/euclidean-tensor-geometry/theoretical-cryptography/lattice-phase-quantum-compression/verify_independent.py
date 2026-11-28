#!/usr/bin/env python3
"""Independent probability-law convolution and monotone threshold bisection."""
from math import exp, expm1, floor, log, pi, sqrt
from statistics import NormalDist

def phase_ratio(h, phase):
    a = 1/expm1(h)
    t = phase % 1
    j = floor(t-a)-1
    if t-j-1>=1+a:  # only a possible floating-point seam
        j += 1
    y = (t-j-1)/a
    U = exp(-h*t)*(a+t)
    W = exp(h*(j-t))*(1+a+a*y*y)
    return U,W,W/U

def shell_probability(offsets,h,n):
    # Work only with sampling probabilities, not the multiplicities/weights.
    z = sum(exp(-h*k) for k in offsets)
    step = {k: offsets.count(k)*exp(-h*k)/z for k in set(offsets)}
    prob = [1.]
    for _ in range(n):
        new = [0.]*(len(prob)+max(step))
        for j,p in enumerate(prob):
            for k,w in step.items():
                new[j+k] += p*w
        prob = new
    return step,prob

def evaluate(step,p,h,n,f):
    s = sum(p)
    p = [x/s for x in p]
    total = 0.
    for k,x in enumerate(p):
        if total+x>=f:
            break
        total += x
    theta = (f-total)/p[k]
    probs = [v/p[k] for v in p]
    P = [(h*(i-k),v) for i,v in enumerate(probs)]
    def accept(t):
        return sum(v*((1. if u<=t else exp(t-u))-float(u<0)) for u,v in P)
    def obj(t):
        # e^(u) * clipped_weight^2; branches avoid overflow in both tails.
        return sum(v*(exp(u) if u<=t else exp(2*t-u)) for u,v in P)
    low,high = -1.,1.
    while accept(low)>theta: low *= 2
    while accept(high)<theta: high *= 2
    for _ in range(65):
        mid=(low+high)/2
        if accept(mid)<theta: low=mid
        else: high=mid
    t=(low+high)/2
    assert abs(accept(t)-theta)<1e-12
    lo = sum(v*exp(u) for u,v in P if u<0)+theta
    qt = obj(t)
    assert 0<qt<lo
    mu = sum(i*w for i,w in step.items())
    sig = sqrt(sum((i-mu)**2*w for i,w in step.items()))
    beta = sum((i-mu)**3*w for i,w in step.items())/sig**3
    zz = NormalDist().inv_cdf(f)
    shift = .5-sig*beta*(1-zz*zz)/6
    gamma = mu*n+sig*sqrt(n)*zz+shift
    phase_error = abs((k+theta-gamma+.5)%1-.5)
    phase0 = phase_ratio(h, theta)
    phase1 = phase_ratio(h, gamma)
    rescale = p[k]*sqrt(n)*exp(h*(k-mu*n-sig*sqrt(n)*zz))
    constant = exp(h*shift-zz*zz/2)/(sqrt(2*pi)*sig)
    return (phase_error,abs(qt/lo-phase0[2]),abs(qt/lo-phase1[2]),
            abs(lo*rescale/(constant*phase1[0])-1),
            abs(qt*rescale/(constant*phase1[1])-1))

N=0
for offsets,h in [([0,1,1],log(2)),([0,1],log(2)),([0,2,5],log(1.3)),
                  ([0,0,1,3,4],log(1.4))]:
    for n in (600,601,1400):
        step,p=shell_probability(offsets,h,n)
        for f in (.31,.50,.77):
            d,a,b,c,e=evaluate(step,p,h,n,f)
            assert d<.011 and max(a,b)<.036 and max(c,e)<.13, (offsets,n,f,d,a,b,c,e)
            if n==1400:
                assert d<.006 and max(a,b)<.024 and max(c,e)<.090
            if f==.50:
                assert d<.002 and max(a,b)<.004 and max(c,e)<.02
            N+=1

cnt=0
for h in (.01,.013,log(2),log(3),1.5,3.0):
    u,w,r = phase_ratio(h,0)
    u1,w1,r1 = phase_ratio(h,1-1e-9)
    assert max(abs(u-u1),abs(w-w1),abs(r-r1))<1e-6
    for i in range(101):
        p0=i/101
        u,w,r=phase_ratio(h,p0)
        assert 0<w<u and 0<r<1
        if h<.02:
            assert abs(r-2*exp(-1))<.001
        cnt+=1
print("INDEPENDENT:",N,"probability-convolution cases; phase, ratio and both prefactors PASS")
print("INDEPENDENT:",cnt,"phase function points; seams, strict gain and small-span control PASS")
