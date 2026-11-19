#!/usr/bin/env python3
"""Integer covering of closed real boxes and exact-rational Jacobian bound for 21354."""
from fractions import Fraction as Q
from itertools import combinations,product
from math import prod

K=1024
def require(ok,detail):
    if not ok:raise RuntimeError(detail)

def bounds(s):
    """Pair-square mass and ordered [2,1] mass on prefixes; [1,2] on suffixes."""
    def scan(v):
        sq=[0];pair=[0]
        for x in v:
            pair.append(pair[-1]+sq[-1]*x);sq.append(sq[-1]+x*x)
        return sq,pair
    P,B=scan(s);R,E=scan(s[::-1]);return P,B,R[::-1],E[::-1]

def mul_nonneg(l,h,u,v):
    """[l,h] times [u,v], 0<=u<=v, l arbitrary."""
    return l*(v if l<0 else u),h*(v if h>0 else u)

def quad(a,A,b,B):
    """Enclose x*(2y-x), x in [a,A], y in [b,B], x,y nonnegative."""
    return (min(a*(2*b-a),A*(2*b-A)),
            max(a*(2*B-a),A*(2*B-A),B*B if a<=B<=A else a*(2*B-a)))

def cover(n,t):
    nboxes=hits=0
    def rec(l,h):
        nonlocal nboxes,hits
        nboxes+=1
        # Outward rounding only: coordinates need NOT be integral.
        h[1]=min(h[1],(h[0]+1)//2);h[-2]=min(h[-2],(h[-1]+1)//2)
        l[0]=max(l[0],2*l[1]);l[-1]=max(l[-1],2*l[-2])
        for i in range(1,t+1):h[i]=min(h[i],h[i-1])
        for i in range(n-2,t-1,-1):h[i]=min(h[i],h[i+1])
        for i in range(t-1,-1,-1):l[i]=max(l[i],l[i+1])
        for i in range(t+1,n):l[i]=max(l[i],l[i-1])
        if any(a>b for a,b in zip(l,h)) or 2*sum(h)<5*K:return
        if n==4 and l[1]>=300 and h[1]<=326 and l[2]>=300 and h[2]<=326 and l[3]>=1010:
            hits+=1;return
        P0,B0,R0,E0=bounds(l); P1,B1,R1,E1=bounds(h)
        # F >= (33/6000)*(sum x)^5 is necessary; every summand is nonnegative.
        if 6000*sum(h[j]*P1[j]*R1[j+1] for j in range(n))<33*sum(l)**5:return
        for i in range(n-1):
            a,b=l[i:i+2];A,B=h[i:i+2]
            L,U=P0[i],P1[i];R,S=R0[i+2],R1[i+2]
            c,C=B0[i]+E0[i+2],B1[i]+E1[i+2]
            if 2*c>=A*S+B*U:return                         # strict merge test
            if a>B and S<L or b>A and U<R:return            # swap
            p=mul_nonneg(2*(a-B),2*(A-b),c,C)
            q=mul_nonneg(*quad(a,A,b,B),R,S)
            r=mul_nonneg(*quad(b,B,a,A),L,U)
            if p[0]+q[0]-r[1]>0 or p[1]+q[1]-r[0]<0:return # first derivative
        i=max(range(n),key=lambda j:h[j]-l[j])
        require(h[i]-l[i]>1,('undecided box',n,t,l,h))
        m=(l[i]+h[i])//2;h1=h[:];h1[i]=m;l1=l[:];l1[i]=m
        rec(l[:],h1);rec(l1,h[:])
    l=[0]*n;h=[K//2]*n;h[0]=l[0]=h[-1]=K
    rec(l,h)
    return nboxes,hits

# Small polynomial ring, so the Jacobian polynomials are built directly
# from the five independently sampled positions, rather than transcribed.
def Fpoly(n):
    f={}
    for i,j,k in combinations(range(n),3):
        e=[0]*n;e[i]=2;e[j]=1;e[k]=2;f[tuple(e)]=1
    return f
def op(f,g,k=1):
    h=dict(f)
    for e,c in g.items():h[e]=h.get(e,0)+k*c
    return {e:c for e,c in h.items() if c}
def diff(f,i):
    g={}
    for e,c in f.items():
        if e[i]:
            d=list(e);d[i]-=1;g[tuple(d)]=c*e[i]
    return g
def at_one(f):
    g={}
    for e,c in f.items():g[e[1:]]=g.get(e[1:],0)+c
    return g
def poly_range(f,l,h):
    lo=hi=0
    for e,c in f.items():
        a=prod(v**k for v,k in zip(l,e));b=prod(v**k for v,k in zip(h,e))
        lo+=c*(a if c>=0 else b);hi+=c*(b if c>=0 else a)
    return lo,hi
def isolate():
    f=Fpoly(4)
    g=[at_one(op(diff(f,i),diff(f,i+1),-1)) for i in range(3)]
    J=[[diff(gi,j) for j in range(3)] for gi in g]
    m=[[461,-627,94],[185,822,-181],[905,629,905]]
    l=[Q(300,K),Q(300,K),Q(1010,K)];h=[Q(326,K),Q(326,K),Q(1)]
    norms=[]
    for i in range(3):
        val=0
        for j in range(3):
            pol={(0,0,0):1000*int(i==j)}
            for k in range(3):pol=op(pol,J[k][j],-m[i][k])
            val+=max(map(abs,poly_range(pol,l,h)))/1000
        norms.append(val);require(val<1,'Jacobian bound')
    print('Jacobian row bounds for I - BJ:',*norms)
    return norms
if __name__=='__main__':
    trial=list(map(Q,['19/50','3/25','3/25','19/50']))
    a,b,c,d=trial
    require(30*(a*a*d*d*(b+c)+a*a*b*c*c+b*b*c*d*d)>Q(33,200),'benchmark')
    for n in range(4,11):
        out=[cover(n,t) for t in range(1,n-1)]
        print('layers',n,'boxes',sum(x for x,y in out),'root-neighborhood boxes',sum(y for x,y in out))
    isolate()
    poly=lambda r: 2*r**3-3*r**2+4*r-1
    require(poly(Q(300,K))<0<poly(Q(326,K)),'symmetric root bracket')
    print('All exact cover and isolation checks passed.')
