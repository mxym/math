"""Exact finite smoke tests of the private analytic argument; no third-party dependencies."""
from fractions import Fraction as F
from itertools import product
from math import comb
from random import Random

def ok(b, msg):
    if not b:
        raise ArithmeticError(msg)

def setups(gen):
    cases=[]
    # Exhaust all binary early *integer split values* through level 7.
    def visit(l,r):
        i=len(l)
        if i==8:
            cases.append((2,l,r))
            return
        s=sum(l[j]*r[i-j] for j in range(1,i))
        for x in range(s+1):
            visit(l+[x],r+[s-x])
    visit([0,1],[0,1])
    for q in (2,3,4,7):
        for n in (17,31,55):
            for mode in range(8):
                p=gen.randrange(1,q); l=[0,p];r=[0,q-p]
                for i in range(2,n):
                    s=sum(l[j]*r[i-j] for j in range(1,i))
                    if mode==0: a=s
                    elif mode==1:a=s*(i%2)
                    elif mode==2:a=s*int(i<n//3)
                    elif mode==3:a=s*gen.randrange(2)
                    elif mode==4:a=F(s*gen.randrange(5),4)
                    else:a=gen.randrange(s+1)
                    l.append(a);r.append(s-a)
                cases.append((q,l,r))
    return cases

def verify(q,l,r):
    n=len(l)
    a=[F(v,q**i) for i,v in enumerate(l)]
    b=[F(v,q**i) for i,v in enumerate(r)]
    g=max(a[1],b[1])
    s=[F(0),F(1)]+[sum(a[j]*b[i-j] for j in range(1,i)) for i in range(2,n+1)]
    E=[1]
    for h in range(1,n):
        if h>=2:
            ok(a[h]+b[h]==s[h] and s[h]<=F(1,h),'coefficient cap')
        ok(a[h]<=g*(1-sum(a[1:h])) and b[h]<=g*(1-sum(b[1:h])),'hazard')
        E.append(max(sum(y[j]*E[h-j] for j in range(1,h+1)) for y in (a,b)))
        ok(E[-1]<=g,'positive-lag propagation')
    N=(2*n+2)//3
    k=n-N
    ok(n<2*N and N<n,'split')
    seeds=[F(0)]*(2*N-1)
    for i in range(1,N):
        for j in range(1,N):
            if i+j>=N:seeds[i+j]+=a[i]*b[j]
    def ev(y,x):
        t=F(0)
        for c in reversed(y):t=t*x+c
        return t
    def root(x):return max(ev(a[:N],x),ev(b[:N],x))>=1
    lo,hi=F(1),F(N,N-1)
    ok(not root(lo) and root(hi),'first root incorrect bracket')
    # Verify algebraic identity at rational endpoints and interior after bisection.
    for _ in range(14):
        x=(lo+hi)/2
        if root(x):hi=x
        else:lo=x
    for x in (F(1),lo,hi):
        ok((1-ev(a[:N],x))*(1-ev(b[:N],x))==1-x+ev(seeds,x),'cutoff identity')
    K=[F(0)]*n+[F(1)]
    for u in range(n-1,N-1,-1):
        theta=a[u]/s[u]
        def p(j):return theta*b[j]+(1-theta)*a[j]
        K[u]=sum(p(j)*K[u+j] for j in range(1,n-u+1))
        ok(K[u]<=E[n-u],'backward coefficient')
    ok(s[n]==sum(seeds[u]*K[u] for u in range(N,n+1)),'positive seeds')
    x=lo
    ok(x**n*s[n]<=seeds[n]*x**n+g*x**k*sum(seeds[u]*x**u for u in range(N,n)),'weighted continuation')
    G=ev(seeds,x)
    ok(G<=F(1,N-1),'weighted total tail')
    M=F(18,n*(k+1)) # substitute the strict bound e<3
    u=[v*x**i for i,v in enumerate(a[:N])]
    v=[w*x**i for i,w in enumerate(b[:N])]
    H=F(0)
    for U,V,grp in ((u,v,tuple(i for i in range(k+1,N) if 2*i<=n)),(v,u,tuple(i for i in range(k+1,N) if 2*i<n))):
        X=sum(U[i]*V[n-i] for i in grp)
        crossed=sum(U[i]*V[n-j] for i in grp for j in grp if j<i)
        ok(crossed<=G,'distinct crossed pairs')
        ok(all(U[j]*V[n-i]<=M for j in grp for i in grp),'opposite product cap')
        ok(X**2<=3*M*G,'endpoint convolution square')
        H+=X
    ok(H==seeds[n]*x**n,'midpoint coverage')

def avoid(words):
    for h in range(1,len(words[0])):
        ok(not ({w[:h] for w in words}&{w[-h:] for w in words}),'prefix/suffix collision')
def mark(q,n,k,t,size):
    P=[(0,)*k+(1,)+v+(1,) for v in product(range(q),repeat=t)][:size]
    L=len(P[0]); avoid(P); P=set(P)
    ok(n>=2*L+1,'conditional sanity parameters')
    p=F(len(P),q**L); m=n-2*L; acc=[]; hits=[0]*(m+1);d=0
    for prefix in P:
        for rest in product(range(q),repeat=n-L):
            word=prefix+rest
            if word[-1]==0:continue
            d+=1
            interior=[i for i in range(L,n-L) if word[i:i+L] in P]
            hits[len(interior)]+=1
            if any(word[i:i+L] in P for i in range(1,n-L+1)):continue
            if any(word[n-h:n-h+k]==(0,)*k for h in range(k+1,L)):continue
            acc.append(word)
    ok(acc,'nonempty toy code'); avoid(acc)
    for h in range(1,m+1):
        exact=F(sum(comb(j,h)*hits[j] for j in range(h,m+1)),d)
        z=m-(h-1)*(L-1)
        calc=(comb(z,h) if z>=h else 0)*p**h
        ok(exact==calc,'factorial moment')
    return len(acc)
if __name__=='__main__':
    cases=setups(Random(20261118))
    for case in cases:verify(*case)
    rows=[mark(2,16,2,1,i) for i in (1,2)]+[mark(3,12,2,1,i) for i in (1,2,3)]
    print(f'PASS: {len(cases)} exact coefficient systems; 5 exhaustive toy marker codes, sizes {rows}.')
