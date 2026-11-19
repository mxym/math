#!/usr/bin/env python3
"""Exact arithmetic for both constants and finite model checks of the quantile integral."""
from fractions import Fraction as Q
from itertools import product
from math import factorial

def require(x,msg):
    if not x: raise ValueError(msg)

def constants():
    # Coefficients obtained by integrating 1-u²+u⁴/2 on [-t,t] and dividing by t.
    a=Q(2,3)-Q(1,5)
    upper=10+1/(4*5*a)
    require(a==Q(7,15) and upper==Q(283,28),'maximum of quadratic envelope')
    require(5*(2-a)+2==Q(29,3)<upper,'large threshold')
    m=Q(3,25)
    require(5*m+m*m/2<Q(2,3) and 10+m>upper,'median bound')
    mu=sum(c*Q(factorial(j),5**(j+1)) for c,j in [(1,0),(-Q(1,2),2),(Q(1,8),4)])
    require(mu==Q(603,3125) and Q(2)/mu>upper,'mean bound')
    print('global upper',upper,'< median benchmark lower',10+m,'and mean benchmark lower',Q(2)/mu)

def pos(x):return max(Q(0),x)

def models():
    # Piecewise-uniform dyadic quantile curves; all remainders beyond 4m may instead
    # have any unbounded continuous law there, with no change to the integrals checked.
    count=0
    for gaps in product([Q(1,4),Q(1,2),Q(1),Q(3,2)],repeat=3):
        q=[Q(0),Q(1)]
        for d in gaps:q.append(q[-1]+d)
        q.extend([q[-1]+3,q[-1]+6])
        seg=[(a,b,Q(1,2**i)) for i,(a,b) in enumerate(zip(q,q[1:]),start=1)]
        # remaining mass is placed strictly above 4m and beyond the listed intervals.
        far=q[-1]+4;seg.append((far,far+1,seg[-1][2]))
        require(sum(p for a,b,p in seg)==1,'normalization')
        def surv(t):
            return 1-sum(p*min(Q(1),pos(t-a)/(b-a)) for a,b,p in seg)
        def num(t):
            z=2*t
            cdf=sum(p*r*(pos(z-a-c)**2-pos(z-b-c)**2-pos(z-a-d)**2+pos(z-b-d)**2)/(2*(b-a)*(d-c))
                 for a,b,p in seg for c,d,r in seg)
            return 1-cdf-surv(t)**2
        J=next(j for j,x in enumerate(q) if x>=2)
        xs=q[:J]+[Q(2)]
        n=next(j for j in range(1,J) if 2*(xs[j+1]-xs[j])>xs[j]-xs[j-1])
        a,b,c=xs[n-1:n+2]
        cuts={a,c};ends={x for lo,hi,p in seg for x in [lo,hi]}
        cuts.update(x for x in ends if a<x<c)
        cuts.update((x+y)/2 for x in ends for y in ends if a<(x+y)/2<c)
        xs2=sorted(cuts); tot=Q(0)
        for lo,hi in zip(xs2,xs2[1:]):
            # Exact: event probability is quadratic between knots.
            tot+=(hi-lo)*(num(lo)+4*num((lo+hi)/2)+num(hi))/6
        lower=(c-b)*Q(1,2**(2*n+1))
        require(tot>=lower and lower/((c-a)*surv(a)**2)>Q(1,24),'crossing integral')
        count+=1
    print('exact piecewise-quadratic numerator integrals:',count)
if __name__=='__main__': constants();models()
