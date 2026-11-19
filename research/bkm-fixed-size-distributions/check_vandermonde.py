"""Exact small cases for the fixed-trace squared Vandermonde proof; no external data."""
from fractions import Fraction as F
from functools import cache
from itertools import combinations
from math import prod,comb
from collections import Counter

def demand(ok,msg):
    if not ok:raise ArithmeticError(msg)

@cache
def pts(n,k):
    if not n:return ((),)
    return tuple((i,)+v for i in range(1,min(n,k)+1) for v in pts(n-i,i))
def data(a,m):
    z=[r+m-i-1 for i,r in enumerate(a+(0,)*(m-len(a)))]
    # Squared Weyl dimension, with degree-dependent total checked against all matrices.
    mass=F(prod((x-y)**2 for i,x in enumerate(z) for y in z[i+1:]),prod((j-i)**2 for i,j in combinations(range(m),2)))
    demand(mass.denominator==1,'Weyl integer')
    t=sum(a)
    up=[F(h+1,t+m*m)*prod(1+F(1,h-g) for g in z if g!=h) for h in z]
    down=[F(h,t)*prod(1-F(1,h-g) for g in z if g!=h) if t else F(0) for h in z]
    demand(sum(up)==1 and sum(down)==bool(t),'normalization')
    return mass.numerator,up,down

cnt=Counter();examples={}
for n in range(1,13):
 for m in (n+1,n+2,2*n+3):
    shapes=pts(n,n);D={a:data(a,m) for a in shapes}
    demand(sum(w for w,u,d in D.values())==comb(m*m+n-1,n),'level enumeration')
    for r in range(n+1):
        mm=Counter()
        for a,(w,u,d) in D.items():mm[a[r] if len(a)>r else 0]+=w
        demand(all(mm[k]**2>=mm[k-1]*mm[k+1] for k in sorted(mm)),'row marginal')
        cnt['row laws']+=1
    padded={a:a+(0,)*(m-len(a)) for a in shapes}
    for a in shapes:
     for b in shapes:
        aa,bb=padded[a],padded[b]
        if any(y>x+1 for x,y in zip(aa,bb)):continue
        for ii,(x,y) in enumerate(zip(aa,bb)):
            if y!=x+1:continue
            demand(D[a][2][ii]<=D[b][2][ii] and D[a][1][ii]>=D[b][1][ii],'tight rows')
            if D[b][1][ii]==0:
                cnt['tight blocked']+=1;continue
            H=max(map(len,(a,b))); i=ii+1; c=x+1-i; B=m+c;X=H+c
            demand(0<X<=m,'X range')
            name='nonnegative c' if c>=0 else ('negative tail' if H<=-2*c else 'negative interior')
            examples.setdefault(name,(n,m,a,b,i));cnt[name]+=1
            for jj in range(H):
                if jj==ii:continue
                d=x-aa[jj]+jj-ii;e=y-bb[jj]+jj-ii
                if jj<ii:demand(0<d*(e+1)<=m*(m-H),'bound (B)')
                else:demand(0<d*(e+1)<=X**2-1,'lower gap bound')
            if name=='negative tail':
                demand(B>=2*X+1 and (1+F(1,X))>=(1+F(1,B))**2,'tail proof')
            else:
                M=m if c>=0 else B
                demand((1+F(H,M**2))*(1+F(1,X))>=(1+F(1,B))**2,'bound (A)')
demand(all(name in examples for name in ('nonnegative c','negative tail','negative interior')),'branch coverage')
print('PASS',dict(cnt))
print('branch examples: (size, particles, left, right, row)',examples)
