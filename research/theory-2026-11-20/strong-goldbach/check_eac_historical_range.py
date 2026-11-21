#!/usr/bin/env python3
"""All analytic tests are rational inequalities. No numerical root finder or floats."""
from check_eac_historical_jets import F,lcm,check,eac,invert,cases,mul

data={
 128: (F(22,100),F(35,100),45,-2,F(-1,2)),
 1718:(F(27,100),F(296,1000),165,4,6),
 1862:(F(47,1000),F(75,1000),45,2,3),
 1928:(F(13,100),F(16,100),120,3,5),
 6142:(F(715,1000),F(82,100),200,F(1,8),3),
}
U1928=[27,8,24,11,72,43,18,79,15,24,43,8,28,27]
def ceil(z):return -((-z.numerator)//z.denominator)
def floor(z):return z.numerator//z.denominator
def expupper(z):
    check(0<=z<32,'exp bound domain')
    return (1-F(z,32))**(-32)

def run(N):
    s0,R,extra,L,U=data[N];C,A=eac(N);n=len(C);B=invert(A)
    w=[sum(r) for r in B];D=lcm(*(v.denominator for v in w));d=[int(D*v) for v in w]
    check(all(0<k<D for k in d),'interior');rad=[F(1)]*n if N!=1928 else [F(v,100) for v in U1928]
    check(0<s0<R and (1/s0)**D<10**8,'numerical cutoff')
    z=[R**(D-j)*expupper(v) for j,v in zip(d,rad)];check(max(z)<1,'complex log')
    for r,ui in zip(B,rad):
        check(sum(abs(b)*x/(1-x) for b,x in zip(r,z))<ui,'box maps inward')
        check(sum(abs(b)*x*uj/(1-x) for b,x,uj in zip(r,z,rad))<ui,'weighted contraction')
    # Real solution: use one-sided inverse-row costs, x_j/N<=1/3 and at most two bootstraps.
    caps=[F(3,2)**ceil(sum((-b for b in r if b<0),F(0))) for r in B]
    for stage in range(3):
        z=[min(F(1,3),s0**(D-dj)*v) for dj,v in zip(d,caps)]
        v=[sum(abs(b)*x/(1-x) for b,x in zip(r,z)) for r in B]
        if all(vj<=uj for vj,uj in zip(v,rad)):break
        # Round upper to 3 decimals to keep subsequent exact fractions small.
        caps=[min(cv,F(ceil(1000*expupper(vj)),1000)) for cv,vj in zip(caps,v)]
    else:raise ValueError('physical branch')
    pol,ell,c=cases[N];idx={p:i for i,p in enumerate(C)}
    P=[(a,tuple(idx[p] for p in v)) for a,v in pol];ws=[sum(d[i] for i in v) for _,v in P]
    H=max(ws);h0=H+ell;J=h0+extra;one=[F(1)]+[F(0)]*J
    Y=[[F(1)] for p in C]; logY=[[] for p in C];logZ=[[] for p in C]
    for h in range(1,J+1):
        for j in range(n):
            gap=D-d[j]
            raw=-Y[j][h-gap] if h>=gap else 0
            corr=sum(l*v*(-Y[j][h-l-gap]) for l,v in enumerate(logZ[j][:max(0,h-gap)],1) if v and Y[j][h-l-gap])
            logZ[j].append(F(raw)-F(corr,h))
        for i in range(n):
            val=sum(B[i][j]*logZ[j][-1] for j in range(n) if B[i][j] and logZ[j][-1])
            logY[i].append(val)
            Y[i].append(F(sum(l*v*Y[i][h-l] for l,v in enumerate(logY[i],1) if v and Y[i][h-l]),h))
    # Literal equation recomposition (rather than trusting the derivative recurrence).
    for i,row in enumerate(A):
        v=one[:]
        for j,a in enumerate(row):
            for _ in range(a):v=mul(v,Y[j],J)
        Z=one[:];gap=D-d[i]
        for j in range(J+1-gap):Z[j+gap]-=Y[i][j]
        check(v==Z,'high-order literal physical equation')
    out=[F(0)]*(J+1)
    for (a,v),weight in zip(P,ws):
        u=one[:]
        for i in v:u=mul(u,Y[i],J)
        for h in range(J+1-H+weight):out[H-weight+h]+=a*u[h]
    check(not any(out[:h0]) and out[h0]==c,'leading integer test')
    # On the closed disk, |exp(u_i)| < 3 as every polyradius <=1.
    K=sum(abs(a)*3**len(v) for a,v in P)
    tail=K/R**h0*(s0/R)**(extra+1)/(1-s0/R)
    # Outward fixed-point interval Horner on 256 equal real subintervals. A grid
    # endpoint rounds OUT from the whole bin; no isolated point sampling is used.
    scale=2**100; bins=256
    cs=[(floor(q*scale),ceil(q*scale)) for q in out[h0:]]
    for k in range(bins):
        s=(floor(scale*s0*k/bins),ceil(scale*s0*(k+1)/bins))
        a=b=0
        for l,u in reversed(cs):
            products=[x*y for x in (a,b) for y in s]
            a=min(products)//scale+l
            b=-((-max(products))//scale)+u
        check(L < F(a,scale)-tail and F(b,scale)+tail<U,'certified jet interval')
    check((L>0 or U<0) and max(abs(L),abs(U))*s0**ell<1,'no integer')
    print(N,'D',D,'coefficient order',J,'real bootstrap',stage+1,'normalized range',L,U,'N strictly below',ceil((1/s0)**D))
for N in data:run(N)
