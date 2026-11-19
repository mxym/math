"""Exact checks independent of the analytic all-n proof; no external inputs."""
from functools import cache
from fractions import Fraction as F
from math import factorial,prod
from itertools import combinations
from bisect import bisect_left
from collections import Counter

def check(c,reason):
    if not c: raise ArithmeticError(reason)

@cache
def parts(n,maxpart=None):
    if not n:return ((),)
    return tuple((k,)+p for k in range(1,min(n,maxpart or n)+1) for p in parts(n-k,k))

@cache
def dim(lam):
    # Young-graph count rather than gamma or Vandermonde
    if not lam:return 1
    return sum(dim(change(lam,i,-1)) for i in range(len(lam)) if i==len(lam)-1 or lam[i]>lam[i+1])

def change(a,i,dt):
    v=list(a)+( [0] if i==len(a) else [])
    v[i]+=dt
    return tuple(x for x in v if x)

def jack(t,a):
    # Hook product in the original (alpha) convention.
    alpha=1/t; d=F(1)
    for i,r in enumerate(a):
        for j in range(r):
            arm=r-1-j;leg=sum(s>j for s in a[i+1:]);z=alpha*arm+leg
            d*=(z+1)*(z+alpha)
    return factorial(sum(a))*alpha**sum(a)/d

@cache
def rates(t,a,L):
    n=sum(a);p=a+(0,)*(L-len(a));x=[p[i]+t*(L-1-i) for i in range(L)]
    D=[x[i]/n * prod(1-t/(x[i]-x[j]) for j in range(L) if i!=j) if n else F(0) for i in range(L)]
    U=[t/(x[i]+t)*prod(1+t/(x[i]-x[j]) for j in range(L) if i!=j) for i in range(L)]
    check(sum(D)==int(n>0) and sum(U)==1,'rate sums')
    check(all((d>0)==(p[i]>(p[i+1] if i+1<L else 0)) and d>=0 for i,d in enumerate(D)),'D legal')
    check(all((u>0)==(not i or p[i]<p[i-1]) and u>=0 for i,u in enumerate(U)),'U legal')
    return D,U

def lis(word):
    z=[]
    for x in word:
        j=bisect_left(z,x)
        if j==len(z):z.append(x)
        else:z[j]=x
    return len(z)

def matchings(points):
    if not points:yield ();return
    for j in range(1,len(points)):
        for m in matchings(points[1:j]+points[j+1:]):yield ((points[0],points[j]),)+m

steps=Counter()
for n in range(1,7):
    lhs=[Counter() for _ in range(3)]
    for arcs in matchings(tuple(range(2*n))):
        perm=[0]*(2*n)
        for i,j in arcs:perm[i]=j;perm[j]=i
        cr=ne=0
        for m in range(1,n+1):
            for e in combinations(arcs,m):
                a,b=zip(*e)
                if a[-1]>=min(b):continue
                if all(x<y for x,y in zip(b,b[1:])):cr=max(cr,m)
                if all(x>y for x,y in zip(b,b[1:])):ne=max(ne,m)
        check(lis([-x for x in perm])==2*ne,'nest LDS')
        for h,k in zip(lhs,[lis(perm),cr,ne]):h[k]+=1
        steps['direct matchings']+=1
    lisjack=Counter();crjack=Counter()
    for a in parts(n):
        lisjack[a[0]]+=dim(tuple(v for k in a for v in (k,k)))
        crjack[a[0]]+=dim(tuple(2*k for k in a))
    check(lhs[0]==lisjack and lhs[1]==lhs[2]==crjack,'distinct matching marginals')
    if n==2:check([lhs[0][1],lhs[0][2],lhs[1][1],lhs[1][2]]==[1,2,2,1],'orientation')

for t in map(F,['1/4','1/2','2/3','1','7/5','2','4']):
    for n in range(1,12):
        L=n+1;pi={a:jack(t,a) for a in parts(n)}
        check(sum(pi.values())==1,'Jack mass')
        A=Counter()
        for a,w in pi.items():
            A[a[0]]+=w; D,U=rates(t,a,L)
            for i,d in enumerate(D):
                if not d:continue
                b=change(a,i,-1)
                check(w*d==jack(t,b)*rates(t,b,L)[1][i],'Jack bond')
                steps['positive Jack bonds']+=1
            if t in [F(1,2), F(2)]:
                doubled=tuple(2*k for k in a) if t==F(1,2) else tuple(v for k in a for v in (k,k))
                check(w*prod(range(1,2*n,2))==dim(doubled),'Stanley/Matsumoto hook')
            for v in parts(n):
                aa=a+(0,)*(L-len(a));vv=v+(0,)*(L-len(v))
                if not all(y<=x+1 for x,y in zip(aa,vv)):continue
                DD,UU=rates(t,v,L)
                for i,(x,y) in enumerate(zip(aa,vv)):
                    if y!=x+1:continue
                    check(D[i]<=DD[i] and U[i]>=UU[i] and (i or U[0]>UU[0]),'ordered tight-row moves')
                    steps['ordered tight rows']+=1
        for k in range(2,n):
            check(A[k]**2>A[k-1]*A[k+1],'strict first-row marginal')
            steps['strict marginal inequalities']+=1
check(steps['direct matchings']==11464,'coverage count')
print('PASS',dict(steps))
