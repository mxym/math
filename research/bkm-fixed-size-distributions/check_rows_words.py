"""Finite exact row/word marginal and slice sanity checks. No third-party modules."""
from math import prod,factorial
from itertools import product
from functools import cache
from fractions import Fraction as F
from collections import Counter

def req(p,s):
    if not p:raise ArithmeticError(s)
@cache
def parts(n,k):
    if n==0:return ((),)
    return tuple((i,)+a for i in range(1,min(n,k)+1) for a in parts(n-i,i))

def shape(word):
    import bisect
    rows=[]
    for x in word:
        for a in rows:
            j=bisect.bisect_right(a,x)
            if j==len(a):a.append(x);break
            x,a[j]=a[j],x
        else:rows.append([x])
    return tuple(map(len,rows))

def jack(a,t):
    s=F(1)
    for i,l in enumerate(a):
        for j in range(l):
            x=(l-j-1)/t+sum(k>j for k in a[i+1:])
            s*=(x+1)*(x+1/t)
    return factorial(sum(a))*(1/t)**sum(a)/s

def words(n,m,a):
    x=[v+m-1-i for i,v in enumerate(a+(0,)*(m-len(a)))]
    return F(factorial(n)*prod((y-z)**2 for i,y in enumerate(x) for z in x[i+1:]),prod(factorial(y) for y in x)*prod(factorial(i) for i in range(m)))

def rows(w,m):
    res=[]
    for r in range(m):
        A=Counter()
        for a,x in w.items():A[a[r] if r<len(a) else 0]+=x
        support=sorted(A)
        req(support==list(range(min(A),max(A)+1)),'interval support')
        req(all(A[k]**2>=A[k-1]*A[k+1] for k in support),'log-concavity')
        res.append(support)
    return res

cnt=Counter()
for m in range(1,5):
 for n in range(1,9):
    a0=parts(n,n)
    W={a:words(n,m,a) for a in a0 if len(a)<=m};req(sum(W.values())==m**n,'total')
    B=Counter(map(shape,product(range(m),repeat=n)));req(B==W,'RSK counts')
    for r,support in enumerate(rows(W,m),1):
        expected=list(range((n+m-1)//m,n+1)) if r==1 else list(range(n//r+1))
        req(support==expected,'cap/slice support')
    cnt['uniform words']+=m**n;cnt['word row laws']+=m
for theta in map(F,['1/5','1/2','1','7/6','2','6']):
 for n in range(1,14):
    W={a:jack(a,theta) for a in parts(n,n)};req(sum(W.values())==1,'total')
    for r,support in enumerate(rows(W,n+1),1):
        req(support==(list(range(1,n+1)) if r==1 else list(range(n//r+1))),'Jack support')
        cnt['Jack row laws']+=1

req(cnt['uniform words']==97738,'exact enumeration length')
print('PASS',dict(cnt))
