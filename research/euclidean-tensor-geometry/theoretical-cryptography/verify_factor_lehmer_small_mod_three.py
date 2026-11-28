#!/usr/bin/env python3
"""Independent exact Mahler-measure sieve for the uniform mod-three reciprocal class."""
from fractions import Fraction as F
from functools import cache,reduce
from math import comb,gcd
from sys import argv


def require(test,msg):
    if not test:raise AssertionError(msg)


def schur(a,N,Q):
    # A necessary strict-disk test. Divide the Schur transform by positive content.
    d=len(a)-1
    a=[x*N**(d-i)*Q**i for i,x in enumerate(a)]
    while len(a)>1:
        if abs(a[-1])>=a[0]:return False
        lead,tail=a[0],a[-1]
        a=[lead*x-tail*y for x,y in zip(a[:-1],a[:0:-1])]
        if len(a)>1 and abs(a[-1])>=a[0]:return False
        g=reduce(gcd,a)
        if g>1:a=[x//g for x in a]
    return True


def power_sums(p,l):
    D=len(p)-1
    S=[D]
    for j in range(1,l+1):
        v=sum(p[k]*S[j-k] for k in range(1,min(D,j-1)+1))
        if j<=D:v+=j*p[j]
        S.append(-v)
    return S


def search(D,R,T):
    m=D//2
    require(R+1/R<T,"strict trace-disk upper radius")
    a=[1];q=[1];sp=[D]
    ts=[[comb(m-j,m-k) for j in range(k+1)] for k in range(m+1)]
    ps=[[comb(D-j,D-k) for j in range(k+1)] for k in range(m+1)]
    B=[int(2*(m-1)+R**k+R**(-k)) for k in range(4*D+1)]
    acc=[0]*(m+1); final=[]; moments=0
    def visit(k):
        nonlocal moments
        if k>m:
            p=a+a[-2::-1]
            s=sp.copy()
            for j in range(m+1,4*D+1):
                v=sum(p[h]*s[j-h] for h in range(1,min(D,j-1)+1))
                if j<=D:v+=j*p[j]
                if abs(v)>B[j]:return
                s.append(-v)
            moments+=1
            if schur(p,R.numerator,R.denominator):final.append(tuple(p))
            return
        v=sum(a[j]*sp[k-j] for j in range(1,k))
        lo=-((B[k]+v)//k); hi=(B[k]-v)//k
        n=sum(q[j]*comb(m-j,(k-j)//2) for j in range(k) if (k-j)%2==0)
        for c in range(lo+(2-lo)%3,hi+1,3):
            a.append(c); q.append(c-n); sp.append(-k*c-v)
            if (schur([w*x for w,x in zip(ts[k],q)],T.numerator,T.denominator)
                    and schur([w*x for w,x in zip(ps[k],a)],R.numerator,R.denominator)):
                acc[k]+=1
                visit(k+1)
            a.pop();q.pop();sp.pop()
    visit(1)
    print(D,R,acc[1:],moments,len(final),flush=True)
    return acc[-1],moments,final


def polydiv(a,b):
    a=list(a)
    if len(a)<len(b):return (),a
    c=[0]*(len(a)-len(b)+1)
    for i in range(len(c)-1,-1,-1):
        c[i]=a[i+len(b)-1]
        if c[i]:
            for j,x in enumerate(b):a[i+j]-=c[i]*x
    return c,a[:len(b)-1]


@cache
def cyclo(n):
    a=[-1]+[0]*(n-1)+[1]
    for d in range(1,n):
        if n%d==0:
            a,r=polydiv(a,cyclo(d))
            require(not any(r),"exact cyclotomic division")
    return a


def cyclo_pool(D):
    return [cyclo(i) for i in range(1,2*D*D+1)
            if sum(gcd(j,i)==1 for j in range(1,i+1))<=D]


def exterior_reject(a,R,limit):
    D=len(a)-1; m=D//2
    C=comb(D,m)
    S=power_sums(a,m*limit)
    for k in range(1,limit+1):
        e=[1]
        for j in range(1,m+1):
            t=sum((-1)**(h-1)*e[j-h]*S[k*h] for h in range(1,j+1))
            u,r=divmod(t,j)
            require(r==0,"integral exterior power sum")
            e.append(u)
        if abs(e[-1])*R.denominator**k>C*R.numerator**k:return k
    return None


Z=(F(0),F(0)); ONE=(F(1),F(0))
def zadd(a,b):return a[0]+b[0],a[1]+b[1]
def zmul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def sq(a):return a[0]**2+a[1]**2
def polyval(a,x):
    y=F(0)
    for c in a:y=y*x+c
    return y
def taylor(p,c):
    a=[]
    for k in range(len(p)):
        v=Z
        for l in range(len(p)-1,k-1,-1):
            v=zadd(zmul(v,c),(F(p[len(p)-1-l]*comb(l,k)),F(0)))
        a.append(v)
    return a


P8=(1,-1,-1,2,-1,2,-1,-1,1)
P10=(1,)+(-1,)*9+(1,)


def witnesses():
    # Real trace verification in degree 10.
    q=(1,-1,-6,3,7,-1)
    ranges=[(-2,F(-9,5)),(F(-6,5),-1),(0,F(1,5)),
            (F(6,5),F(3,2)),(F(12,5),F(5,2))]
    require(all(polyval(q,a)*polyval(q,b)<0 for a,b in ranges),"five distinct real trace roots")
    for D,p,T in [(8,P8,(1,-1,-5,5,3)),(10,P10,q)]:
        m=D//2; u=[0]*(D+1)
        for i,x in enumerate(T):
            for j in range(m-i+1):
                u[i+2*j]+=x*comb(m-i,j)
        require(tuple(u)==p and not any(not any(polydiv(p[::-1],v)[1]) for v in cyclo_pool(D)),
                "trace identity and cyclotomic-free candidate")
    a,b=F(19970,10000),F(19971,10000)
    require(polyval(P10,a)*polyval(P10,b)<0,"degree-ten outside bracket")
    C=[(F(-143789337,10**8),F(0)),
       (F(109354797,10**8),F(62287067,10**8))]
    r=F(1,10**6)
    for i,c in enumerate(C):
        a=taylor(P8,c)
        require(r*max(map(abs,a[1]))>sum((abs(u)+abs(v))*r**j for j,(u,v) in enumerate(a) if j!=1),
                "one root in each indicated Rouche disk")
        a,b=[(F(1437892,10**6),F(1437895,10**6)),
             (F(1258496,10**6),F(1258499,10**6))][i]
        require(1<a and (a+r)**2<sq(c)<(b-r)**2,"strict radial intervals")
    require(polyval((1,-1,-5,5,3),F(-1,2))*polyval((1,-1,-5,5,3),F(-2,5))<0,
            "degree-eight remaining pair on the unit circle")
    lo=F(1437892,10**6)*F(1258496,10**6)**2
    hi=F(1437895,10**6)*F(1258499,10**6)**2
    require(F(22773,10000)<lo<hi<F(22774,10000),"degree-eight measure bracket")
    print("PASS exact degree-eight and degree-ten witness isolation")

TESTS={8:(F(23,10),F(274,100),(220,118,118,50,67,47),(P8,)),
       10:(F(2),F(251,100),(797,236,236,81,154,26),(P10,)),
       14:(F(17221,10000),F(231,100),(7963,991,991,303,688,23),())}


def test(D):
    R,T,expected,singleton=TESTS[D]
    prefixes,moments,survivors=search(D,R,T)
    pool=cyclo_pool(D)
    c=ex=h=0; rest=[]
    for p in survivors:
        if any(not any(polydiv(p[::-1],g)[1]) for g in pool):
            c+=1
        else:
            k=exterior_reject(p,R,48)
            if k is None:rest.append(p)
            else:ex+=1;h=max(h,k)
    out=(prefixes,moments,len(survivors),c,ex,h)
    require(out==expected and tuple(rest)==singleton,(D,out,rest))
    print("PASS exact search",D,out,singleton,flush=True)


if __name__=="__main__":
    witnesses()
    for D in ([int(x) for x in argv[1:]] or sorted(TESTS)):
        test(D)
