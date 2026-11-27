#!/usr/bin/env python3
"""Exact tangent contact spectra and Gram-quantization constants; no dependencies."""
from fractions import Fraction as F
from itertools import combinations,product
from math import comb,isqrt
if not __debug__:raise RuntimeError('enable assertions')
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def roots(d):
    R=[]
    for i,j in combinations(range(8),2):
        for a,b in product([-2,2],repeat=2):
            x=[0]*8;x[i]=a;x[j]=b;R.append(x)
    R.extend(x for x in product([-1,1],repeat=8)if x.count(-1)%2==0)
    return [x for x in R if x[6]+x[7]==0 and (d==7 or x[5]+x[7]==0)]
def run(d):
    r=roots(d);n=len(r)
    A=[(i,j)for i,j in combinations(range(n),2)if dot(r[i],r[j])==4]
    k=2*len(A)//n;assert (n,k)=={6:(72,20),7:(126,32)}[d]
    B=[(i,j,[(h,2*r[j][h]-r[i][h])for h in range(8)if 2*r[j][h]!=r[i][h]],[(h,2*r[i][h]-r[j][h])for h in range(8)if 2*r[i][h]!=r[j][h]]) for i,j in A]
    # Every root belongs to the reflection orbit of root zero.
    ix={tuple(z):i for i,z in enumerate(r)};seen={0};todo=[0]
    while todo:
        v=r[todo.pop()]
        for x in r:
            g=dot(v,x);assert g%4==0
            w=ix[tuple(z-g//4*t for z,t in zip(v,x))]
            if w not in seen:seen.add(w);todo.append(w)
    assert len(seen)==n
    # tight frame on the root span; tightness follows from S^2=(8n/d)S, tr S=8n.
    S=[[sum(v[i]*v[j] for v in r)for j in range(8)]for i in range(8)]
    assert all(d*sum(S[i][h]*S[h][j] for h in range(8))==8*n*S[i][j]for i in range(8)for j in range(8))
    for i in range(n):
        U=[r[j] for j in range(n)if dot(r[i],r[j])==4]
        assert len(U)==k and all(2*sum(v[h] for v in U)==k*r[i][h] for h in range(8))
    def T(X):
        Y=[[0]*8 for _ in r]
        for i,j,p,q in B:
            u=sum(X[i][h]*v for h,v in p)+sum(X[j][h]*v for h,v in q)
            if u:
                for h,v in p:Y[i][h]+=u*v
                for h,v in q:Y[j][h]+=u*v
        return Y
    mult={6:{0:231,48:70,64:81,96:60,144:114,192:20},
          7:{0:273,64:112,96:210,128:189,192:147,208:56,256:21}}[d]
    # For vector site i=0 and each of 8 coordinates evaluate successive
    # T-powers and the proposed annihilator; transitivity covers every site.
    coef=[1]
    for z in mult:
        p=[0]*(len(coef)+1)
        for j,v in enumerate(coef):p[j]-=z*v;p[j+1]+=v
        coef=p
    tr=[0]*len(coef)
    for h0 in range(8):
        X=[[0]*8 for _ in r];X[0][h0]=1
        Y=[[0]*8 for _ in r]
        for j,v in enumerate(coef):
            tr[j]+=n*X[0][h0]
            if v:
                for i in range(n):
                    for h in range(8):Y[i][h]+=v*X[i][h]
            if j+1<len(coef):X=T(X)
        assert all(not any(z)for z in Y)
    for j,v in enumerate(tr):
        assert v==sum(t*x**j for x,t in mult.items())
    assert mult[0]-n*(8-d+1)==d*(d-1)//2
    return n,k
for d in (6,7):
    n,k=run(d);print(d,n,k,'exact tangent spectrum PASS')

def plus(p,q):
    a=[F(0)]*max(len(p),len(q))
    for j,x in enumerate(p):a[j]+=x
    for j,x in enumerate(q):a[j]+=x
    return a
def cheb_interval_check(p,l,u):
    # Bernstein coefficients on [l,u]: positivity is sufficient.
    n=len(p)-1
    c=[sum(p[j]*comb(j,h)*l**(j-h) for j in range(h,n+1))*(u-l)**h for h in range(n+1)]
    b=[sum(F(comb(j,h),comb(n,h))*c[h] for h in range(j+1))for j in range(n+1)]
    if min(b)>=0:return 1
    assert u-l>F(1,1024)
    m=(l+u)/2
    return cheb_interval_check(p,l,m)+cheb_interval_check(p,m,u)
g=[0,0,-F(1,4),-F(7,12),1,F(8,3),0,-F(4,3)]
root=[F(-1),-F(1,2),F(0),F(1,2)]
cuts=sorted(root[:]+[(x+y)/2 for x,y in zip(root,root[1:])]);parts=0
for l,u in zip(cuts,cuts[1:]):
    z=min(root,key=lambda y:abs(y-(l+u)/2));c=F(21,256)
    p=plus([-x for x in g],[-c*z*z,2*c*z,-c])
    parts+=cheb_interval_check(p,l,u)
assert sum(-g[i]*(-F(1,4))**i for i in range(len(g)))==F(21,256)*F(1,16)
# e^(1+3/352)<11/4 by a geometric bound on its exponential tail
v=1+F(3,352);t=F(1);w=t
for j in range(1,12):t=t*v/j;w+=t
assert w+t*v/12/(1-v/13)<F(11,4)
for d,N,k,b,h,kap in [(6,72,20,F(5,32),352,F(3,2)),(7,126,32,F(128,663),704,F(2))]:
    assert F(11,4*h)==F(1,2**(d+1))
    # If the Gram deviation is <=1/25, Procrustes squared is <=(201d/(100N))/625.
    assert 1+1/(1-F(d,25*N))<F(201,100)
    U2=F(201*d,100*625*N)
    assert U2<kap/(9*k*k) and U2<F(1,100)
    gap=F(21,256)/(h*h*b*N*N)
    print(d,'M7 gap >=',gap)
print('sharp quartic-distance control and rounding constants:',parts,'Bernstein leaves; PASS')
