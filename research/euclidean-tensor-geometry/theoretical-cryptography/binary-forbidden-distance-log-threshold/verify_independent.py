#!/usr/bin/env python3
"""Pascal-row threshold replay and a relative-tail sign-window diagnostic."""
from math import log, pi, sqrt


def pascal(tmax):
    first={}
    row=[1]
    n=0
    active=set(range(3,tmax+1))
    while active:
        start=0
        agg=[]
        for x in row:
            start+=x
            agg.append(start)
        for t in sorted(active):
            if t<=n and (n-t)%2==0:
                if agg[(n-t)//2]*agg[t-2] > agg[t-3]*start:
                    first[t]=n
                    active.remove(t)
        row=[1]+[a+b for a,b in zip(row,row[1:])]+[1]
        n+=1
    return first


def bracket_factor(n,r):
    # Successive ratios are decreasing. The discarded sum is at most a
    # geometric tail, small relative to the partial sum.
    term=partial=1.0
    for i in range(r):
        rat=(r-i)/(n-r+i+1)
        tail=term*rat/(1-rat)
        if tail<1e-12*partial:
            return partial,partial+tail
        term*=rat
        partial+=term
    return partial,partial


def log_bracket(t,n):
    r=(n-t)//2
    s=n-r
    u=t/n
    v=u*u
    assert 0<v<0.1
    # I(u) = sum_{j>=1} u^(2j)/(2j(2j-1)).
    j4=sum(v**j/(2*j*(2*j-1)) for j in range(1,5))
    mid=0.5*log(n/(2*pi*r*s))
    # Robbins Stirling bounds for the mass, in cancellation-free form.
    lo=mid-n*(j4+v**5/(90*(1-v)))+1/(12*n+1)-1/(12*r)-1/(12*s)
    hi=mid-n*j4+1/(12*n)-1/(12*r+1)-1/(12*s+1)
    a,b=bracket_factor(n,r)
    c,d=bracket_factor(n,t-2)
    e,f=bracket_factor(n,t-3)
    l=log((n-t+3)/(t-2))
    return lo+l+log(a)+log(c/f),hi+l+log(b)+log(d/e)


def implicit_z(t):
    target=log(t)-log(4*sqrt(pi))
    a,b=1e-8,log(t)+2
    for _ in range(72):
        z=(a+b)/2
        if z+1.5*log(z)>target:
            b=z
        else:
            a=z
    return (a+b)/2


def nearest(t,z):
    return t+2*round((t*t/(2*z)-t)/2)


def main():
    p=pascal(32)
    picked=tuple(p[t] for t in (3,4,5,8,16,32))
    print("INDEPENDENT: Pascal crossings 30 t-values, selected:",",".join(map(str,picked)))
    table=(64,128,256,512,1024,4096,16384,65536)
    for t in table:
        z=implicit_z(t)
        a=nearest(t,z+0.75)
        b=nearest(t,z-0.75)
        lo1,hi1=log_bracket(t,a)
        lo2,hi2=log_bracket(t,b)
        assert a<b and lo1<=hi1<-0.1 and 0.1<lo2<=hi2, (t,z,a,b,lo1,hi1,lo2,hi2)
    print(f"INDEPENDENT: {2*len(table)} separated log-sign checks in the t^2/(2 log t) window PASS")


if __name__=="__main__":
    main()
