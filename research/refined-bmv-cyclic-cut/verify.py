"""Exact finite sanity checks, independent of numerical linear algebra. Python 3."""
from itertools import groupby, product
from fractions import Fraction as F
from math import comb
def require(test):
    if not test: raise ArithmeticError("exact verification failed")

def runs(w):
    h=next(i for i,x in enumerate(w) if x==0 and w[i-1]==1)
    p=[len(tuple(g)) for _,g in groupby(w[h:]+w[:h])]
    return p[::2],p[1::2]
def feasible(a,b):
    n,m=sum(a),sum(b); k=len(a); C=n*m
    A=[2*m*t for t in a]; B=[2*n*t for t in b]
    z=[0]
    for i in range(1,k): z.append(z[-1]+A[i]-B[i-1])
    require(z[-1]+A[0]-B[-1]==0)
    return max(max(0,y-C)-o for y,o in zip(B,z))<=min(min(C,y)-o for y,o in zip(B,z))
def cuts(a,b):
    n,m=sum(a),sum(b); k=len(a)
    for I in product((0,1),repeat=k):
        for J in product((0,1),repeat=k):
            c=sum((I[i]+I[(i+1)%k])*(1-J[i]) for i in range(k))
            cap=(sum(x*(1-h) for x,h in zip(a,I))*2*m
                 +sum(x*h for x,h in zip(b,J))*2*n+c*n*m)
            if cap<2*n*m:return False
    return True
total=total_both=regions=0
for l in range(2,14):
    hist={n:True for n in range(1,l)}
    for w in product((0,1),repeat=l):
        n=w.count(0)
        if n in (0,l):continue
        a,b=runs(w); ok=feasible(a,b)
        if l<=9: require(ok==cuts(a,b)); total_both+=1
        hist[n]&=ok; total+=1
    for n,ok in hist.items():
        m=l-n; require(ok==(2*(n+m)>=n*m)); regions+=1
print('All length 2–13 words:',total,'; independent all-cut comparisons length ≤9:',total_both,'; exponent pairs:',regions)
cnt=0
for n,m in product(range(2,12),repeat=2):
    for a,b in product(range(1,n),range(1,m)):
        require(feasible([a,n-a],[b,m-b])==(2*(min(a,n-a)*m+min(b,m-b)*n)>=n*m))
        cnt+=1
print('Rational four-factor diamonds:',cnt)
def fn(f):return tuple(tuple(f(i,j) for j in range(3)) for i in range(3))
Id=fn(lambda i,j:int(i==j)); O=fn(lambda i,j:0)
def add(A,B):return fn(lambda i,j:A[i][j]+B[i][j])
def sc(c,A):return fn(lambda i,j:c*A[i][j])
def mul(A,B):return fn(lambda i,j:sum(A[i][k]*B[k][j] for k in range(3)))
def P(x):return fn(lambda i,j:F(x[i]*x[j],sum(t*t for t in x)))
def tr(A):return sum(A[i][i] for i in range(3))
def word(*Ms):
    A=Id
    for B in Ms:A=mul(A,B)
    return A
def ratio(n,m,T,expected):
    D=2*T**50
    # A,B are scaled by D here. The same power D**(n+m) cancels from both sides.
    def scaled(c,X,z):return fn(lambda i,j:int(c*X[i][j])+z*int(i==j))
    A=add(scaled(D,P((1,0,0)),2),scaled(D//T**m,P((0,-1,1)),0))
    B=add(scaled(D,P((0,0,1)),2),scaled(D//T**n,P((1,-1,0)),0))
    S={(0,0):Id}
    for i in range(n+1):
        for j in range(m+1):
            if i+j>0:S[i,j]=add(mul(A,S.get((i-1,j),O)),mul(B,S.get((i,j-1),O)))
    num=tr(S[n,m]); den=comb(n+m,n)*tr(word(*([A]*n+[B]*m)))
    R=F(num,den); require(expected<R<expected+1)
    # Exact integers bracket the answer, not merely a floating comparison.
    print(f'PD ratio ({n},{m}), t=1/{T}: {R.numerator//R.denominator} < R < {R.numerator//R.denominator+1}')
ratio(4,5,100,45)
ratio(3,7,100000,521)
h=F(1,1000); r=h**5
sv=2*r/(1+r*r);cv=(1-r*r)/(1+r*r); require(sv*sv+cv*cv==1)
PX,UX=P((1,0,0)),P((0,-1,1)); PY,VY=P((sv,0,cv)),P((cv,-1,-sv))
def x(i):return add(PX,sc(h**(2*i),UX))
def y(i):return add(PY,sc(h**(2*i),VY))
R=tr(word(x(4),y(4),x(1),y(1)))/tr(word(x(5),y(5)))
require(100<R<101)
print('Rational PSD four-factor (4/5,4/5) ratio:',R.numerator//R.denominator,'< R <',R.numerator//R.denominator+1)
