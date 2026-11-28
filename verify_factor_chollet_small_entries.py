#!/usr/bin/env python3
"""Integer/rational certificate: small-correlation cases of the Chollet inequality."""
from fractions import Fraction as F
from math import comb, factorial, isqrt
from sys import argv

if not __debug__:
    raise RuntimeError("run without -O")

SCALE=10**12


def sqrt_interval(u):
    z=isqrt((u.numerator*SCALE*SCALE)//u.denominator)
    lo=F(z,SCALE)
    hi=lo if lo*lo==u else F(z+1,SCALE)
    assert lo*lo<=u<=hi*hi
    return lo,hi


def log_lower(r):
    assert r>=1
    y=(r-1)/(r+1)
    s=sum(2*y**(2*k+1)/F(2*k+1) for k in range(30))
    return F(s*SCALE//1,SCALE)


def row_table(n):
    # Maximum squared degree sum at each number of edges, compressed to threshold graphs.
    M=comb(n,2)
    H=[-1]*(M+1)
    def visit(deg,m):
        v=len(deg)
        if v==n:
            H[m]=max(H[m],sum(t*t for t in deg))
        else:
            visit(deg+[0],m)
            visit([i+1 for i in deg]+[v],m+v)
    visit([0],0)
    assert H[0]==0 and H[1]==2 and H[M]==n*(n-1)**2 and min(H)>=0
    return H


def cyl(n,m,v,ways):
    if v>m:return F(0)
    completions=sum((-1)**i*comb(m-v,i)*factorial(m-3-i) for i in range(m-v+1))
    return F(comb(n-v,m-v)*completions*ways,comb(m,3))


def small(n,r,parts):
    E=r*r
    M=comb(n,2)
    H=row_table(n)
    e2=E*E
    D=[1,0]
    for m in range(2,n+1):
        D.append((m-1)*(D[-1]+D[-2]))
    U=sqrt_interval(F(2))[1]*E
    dr=sqrt_interval(F(n-1,n))[1]
    rho=[F(0),F(0),F(1),sqrt_interval(F((n-2)**2,n*(n-1)))[1]]
    for m in range(4,n+1):
        t=F(n-1,n)**((m-2)//2) 
        rho.append(t*(dr if m%2 else 1))
    P=[F(1),F(0)]
    for m in range(2,n+1):
        P.append(sum(rho[k]*P[m-k] for k in range(2,m+1))/m)

    upper_params={}
    for m in range(2,n+1):
        p0=F(D[m-2],D[m])
        p1=F(2,m-1)-2*p0
        p2=1-p0-p1
        assert min(p0,p1,p2)>=0
        a,b,c=p0/M,p1/((n-2)*M),p2/(3*comb(n,4))
        N=comb(n,m)*D[m]
        pars=[N*E**m/M,N*E**(m-2),a,b,c,P[m]*U**m]
        if m>=3:
            pars.append(tuple(cyl(n,m,v,w) for v,w in ((6,8),(5,4),(4,2),(3,2),(4,2))))
        upper_params[m]=pars

    lower_params=[]
    for k in parts:
        assert k in (3,4)
        t=k*(k-1)//2*E
        a=1-2*r/3 if k==3 else F(2,3)
        b=3*E+2*r**3 if k==3 else 6*E+8*r**3+9*r**4
        c0=log_lower(1+a*t)/t
        c1=log_lower((1+b)/(1+a*t))/(b-a*t)
        K=a*a/(2*(1+a*t)**2)
        f2=F(comb(k,2),M)
        f3=F(comb(k,3),comb(n,3))
        f4=F(comb(k,4),comb(n,4))
        assert min(c0,c1,K)>0 and f3>=f4 and f2-2*f3+f4>=0
        lower_params.append((k,t,a,c0,c1,K,f2,f3,f4))

    c3=comb(n,3);c4=comb(n,4)
    closed=0; max_depth=0; margin=None

    def verify(m,lo,hi,depth):
        nonlocal closed,max_depth,margin
        assert 0<=lo<hi and max(depth,0)<=30
        y0,y1=lo*lo,hi*hi
        slope=H[m+1]-H[m]
        intercept=H[m]-m*slope
        R=e2*(slope+(F(intercept,1)/(y0 if intercept>0 else y1) if intercept else 0))
        # All bounds are normalized by y^2, with s=E*y^2.
        c3lo=(-2*E+4*e2*y0/n)/3
        c4lo=max(e2*y0/2-(F(3*(n-1),2)-1)*e2,
                 (F(1,2)+F(1,M))*e2*y0-F(3,4)*R)
        L=F(0)
        for k,t,a,c0,c1,K,f2,f3,f4 in lower_params:
            ES=f2*E
            ES2=f4*e2*y1+(f3-f4)*R+(f2-2*f3+f4)*e2
            EU=ES+f3*c3lo+f4*c4lo
            L+=c0*ES+K*max(0,t*ES-ES2)+c1*max(0,EU-a*ES)
        assert L>0
        # exp(2 L y^2)-1 >= y^2 times the following positive partial sum.
        z=2*L
        v=z; LB=v
        for j in range(2,18):
            v*=z*y0/j; LB+=v

        adj=min((n-2)*e2,R/2-e2*y0/M)
        path=min((n-1)**2*e2*E,dr*U*hi*R/2)
        tri=rho[3]*U**3*hi/6
        double=E*(e2+(1-F(4,n))*e2*y1)
        UB=F(0)
        for j,params in upper_params.items():
            one,N,a,b,c,cyc,*choices=params
            bc=b-c
            z=a-b+c/2
            pair=N*(c*e2*y1/2+
                    bc*(R if bc>=0 else 4*e2*y0/n)/2+
                    z*(e2 if z>=0 else e2*y0/M))
            candidates=[one,cyc*hi**(j-2),pair]
            if choices:
                t0,t1,t2,t3,t4=choices[0]
                for base in (t0,t1,t2,t3):
                    if base>=t0:
                        tri_bound=base*E**3*y1**2/6+max(0,t1-base)*adj*E*y1+max(0,t2-base)*path+max(0,t3-base)*tri+t4*double
                        candidates.append(E**(j-3)*tri_bound)
            assert min(candidates)>=0
            UB+=min(candidates)
        if LB>UB:
            mm=(LB-UB)*10**6//1
            margin=mm if margin is None else min(margin,mm)
            closed+=1;max_depth=max(max_depth,depth)
        else:
            if depth>=30: raise AssertionError(("uncertified",n,r,m,lo,hi,LB,UB))
            mid=(lo+hi)/2
            verify(m,lo,mid,depth+1)
            verify(m,mid,hi,depth+1)

    for m in range(M):
        lo=sqrt_interval(F(m))[0]
        hi=sqrt_interval(F(m+1))[1]
        verify(m,lo,hi,0)
    print("SMALL PASS",n,r,closed,max_depth,margin,flush=True)
    return closed,max_depth,margin


def main():
    small(7,F(1,5),(4,3))
    small(9,F(8,25),(4,4))
    small(11,F(21,50),(4,4,3))
    if '--additional' in argv:
        small(12,F(2,5),(4,4,4))
        small(13,F(3,8),(4,4,4))

if __name__=="__main__":main()
