"""Finite algebra/sign controls only, not a numerical check of an asymptotic."""
from math import gcd, isqrt, log
from fractions import Fraction
from pathlib import Path
from collections import Counter
def require(ok, reason):
    if not ok: raise RuntimeError(reason)
def fac(n):
    pp=[]
    for p in range(2,isqrt(n)+1):
        while n%p==0:
            pp.append(p);n//=p
    if n>1: pp.append(n)
    return pp
def mob(n):
    f=fac(n)
    return 0 if len(set(f))<len(f) else (-1)**len(f)
def norm(c): return dict((p,e) for (p,e) in c.items() if e)
def Alog(n):
    """Record coefficient of every independent log(p), removing any zero at d^2=n."""
    out=Counter(); nf=Counter(fac(n))
    for d in range(1,isqrt(n)+1):
        if n%d: continue
        a=mob(d)
        for p,k in nf.items():out[p]+=a*k
        for p in fac(d):out[p]-=2*a
    return norm(out)
def Vlog(n):
    f=fac(n)
    return {n:1} if len(f)==1 else {}
sqr=0;odd=0;semi=0;negative=0
for n in range(2,7001):
    f=fac(n)
    a=Alog(n)
    if len(set(f))==len(f):
        sqr+=1
        if len(f)%2:
            require(a==Vlog(n),("odd parity row",n,a));odd+=1
        if len(f)==2:
            require(a=={f[0]:2},("true semiprime",n,a));semi+=1
        if sum(e*log(p) for p,e in a.items()) < -1e-7:negative+=1
require(negative>0 and semi>0,("sign guards",negative,semi))
pairs=0;neg=0
# Explicit CRT floor for a nonintegral boundary includes both original endpoints.
for P in range(32,650,2):
    a=(P+2)//3;b=2*P//3;lo=a-1;hi=b
    for d in range(1,isqrt(b)+1):
        for e in range(1,isqrt(b)+1):
            g=gcd(d,e)
            raw=sum(n%d==0 and (P-n)%e==0 for n in range(a,b+1))
            if P%g:
                require(raw==0,("incompatible",P,d,e));continue
            u=d//g;v=e//g
            z=(P//g)*pow(u,-1,v)%v if v>1 else 0
            def xi(y):return Fraction(y,d*v)-Fraction(z,v)
            def fl(t):return t.numerator//t.denominator
            calc=fl(xi(hi))-fl(xi(lo))
            require(calc==raw,("CRT sign",P,d,e,raw,calc))
            pairs+=1
            if (Fraction(raw)-Fraction(b-a+1,d*v))<0:neg+=1
require(neg and pairs>20000,("coverage",pairs,neg))
require(2*.8-2-1.6*log(.8)<-.042,"low-rank exponent")
require(1.6-1-1.6*log(1.6)<-.152,"high-rank exponent")
require(Fraction(1,2)+Fraction(7,20)+Fraction(1,8)==Fraction(39,40),"BC1")
require(Fraction(1,2)+Fraction(3,8)+Fraction(1,16)==Fraction(15,16),"BC2")
raw=Path(__file__).with_name('Proof.md').read_bytes()
require(not any(c<32 and c not in (10,) for c in raw),"Markdown control bytes")
print(f"OK: squarefree={sqr}, odd={odd}, semiprimes={semi}, negative signed rows={negative}; compatible CRT tests={pairs}, negative discrepancies={neg}.")
