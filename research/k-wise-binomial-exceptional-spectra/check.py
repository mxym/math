"""Exact finite checks; Python standard library. They do not prove an infinite-size result."""
from fractions import Fraction as F
from itertools import combinations
from math import comb, factorial, gcd, isqrt, prod
from functools import lru_cache

def require(a):
    if not a:raise ArithmeticError("failed exact verification")
def trim(q):
    while q and not q[-1]: q.pop()
    return q
def pgcd(a,b):
    a,b=trim(list(map(F,a))),trim(list(map(F,b)))
    while b:
        while len(a)>=len(b):
            c,i=a[-1]/b[-1],len(a)-len(b)
            for j,t in enumerate(b):a[i+j]-=c*t
            trim(a)
        a,b=b,a
    return tuple(x/a[-1] for x in a)
def evalp(q,p):return sum(c*p**j for j,c in enumerate(q))
def falling_coeff_expectation(N,roots):
    # Multiply by x-root using x(x)_j=(x)_(j+1)+j(x)_j, then take binomial moments.
    c=[1]
    for r in roots:
        d=[0]*(len(c)+1)
        for j,v in enumerate(c):d[j]+=(j-r)*v;d[j+1]+=v
        c=d
    return tuple(v*factorial(j)*comb(N,j) for j,v in enumerate(c))
def mulhalf(N,roots):
    return sum(f*(1<<(N-j)) for j,f in enumerate(falling_coeff_expectation(N,roots)))
def criterion4(N,p):
    s=1+2*(N-1)*p; ds=1+4*(N-1)*p*(1-p)
    D=isqrt(ds.numerator)
    return s.denominator==1 and ds.denominator==1 and D*D==ds.numerator and D>=3 and (int(s)-D)%2==0
cnt4=count6=0
for n in range(6,41):
    N=n-1; found=set()
    # Exact gcd of the two vanishing lower cardinal masses for each left basis.
    for u,v in combinations(range(N),2):
        if v-u<2:continue
        P=falling_coeff_expectation(N,(u+1,v,v+1))
        Q=falling_coeff_expectation(N,(u,u+1,v+1))
        G=list(pgcd(P,Q))
        # Remove irrelevant roots at p=0 or 1 using exact division.
        while G and not G[0]:G=G[1:]
        while len(G)>1 and sum(G)==0:
            T=[];z=F(0)
            for a in G[:0:-1]:z+=a;T.append(z)
            G=T[::-1]
        require(len(G)<=2)
        if len(G)==2:
            p=-G[0]/G[1]
            if 0<p<1:
                require(evalp(P,p)==evalp(Q,p)==0)
                require(u+1<N*p<v+1)
                found.add(p)
        cnt4+=1
    possible={p for s in range(2,2*(N-1)+1) if criterion4(N,p:=F(s-1,2*(N-1)))}
    require(found==possible)
for den in range(2,32):
    for num in range(1,den):
        if gcd(num,den)!=1:continue
        p=F(num,den); r=abs(2*p-1);a,b=r.numerator,r.denominator; d=b*b-a*a
        for j in (1,2,3):
            D=1+2*j*d; N=1+b*b*((D*D-1)//d)
            require(criterion4(N,p))
print("Four-wise lower-cardinal gcds checked:",cnt4,"; all exact spectra agree for n=6..40.")
found6=[]
for n in range(8,74):
    N=n-1
    # Compute the tilted mean for every unchanged pair of pairs. These signs
    # test all three left cardinal pairs, without any symmetry assumption.
    @lru_cache(None)
    def mass(a,b):
        sites=(a,a+1,b,b+1); den=mulhalf(N,sites)
        return F(mulhalf(N,sites+(0,)),den)
    old=[]
    for a,b,c in combinations(range(N),3):
        if b-a<2 or c-b<2:continue
        M=(mass(b,c)-a,mass(a,c)-b,mass(a,b)-c)
        if min(M)>0 and max(M)<=1 and M.count(1)>=2:old.append((a,b,c,M.count(1)))
        count6+=1
    D=isqrt(3*N-2); E=isqrt(3*N)
    expected=3 if N%2==0 and D*D==3*N-2 and D%2==0 else (2 if N%2 and E*E==3*N else 0)
    require(len(old)==bool(expected))
    if old:
        require(old[0][-1]==expected)
        found6.append((n,expected))
print("Six-wise paired supports tested:",count6,"; (n,actual departures) at p=1/2:",found6)
print("PASS (finite checks).")
