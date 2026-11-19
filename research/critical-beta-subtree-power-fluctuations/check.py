"""Exact small-tree checks of the identities used for centered fluctuation laws.

The leaf-count indicators form a formal toll basis, so the covariance test covers
every real toll at these sizes, not numerical approximations to fractional powers.
Entropy is represented in the independent basis log(2),log(3),log(5),log(7).
Only Python's standard library is used. No asymptotic conclusion is inferred
from the finite checks. Run normally or under python -O.
"""
from fractions import Fraction as F
from functools import lru_cache

N=9
PR=(2,3,5,7)
def check(condition):
    if not condition: raise ArithmeticError("exact identity failed")
def zero(d): return (0,)*d
def add(*vv): return tuple(map(sum,zip(*vv)))
def scale(c,v): return tuple(c*x for x in v)
def minus(u,v): return add(u,scale(-1,v))
def outer(v): return tuple(x*y for x in v for y in v)
def innerrow(m): return tuple(int(k==m) for k in range(2,N+1))
def mean(pairs): return add(*(scale(w,v) for w,v in pairs))

@lru_cache(None)
def h(m): return sum((F(1,z) for z in range(1,m+1)),F())
def q(m,i): return F(m,2*i*(m-i))/h(m-1)
@lru_cache(None)
def visits(n,k):
    if n<=k: return F(n==k)
    return sum(visits(i,k)/((n-i)*h(n-1)) for i in range(k,n))
@lru_cache(None)
def lp(n):
    out=[]
    for p in PR:
        c=0
        while n%p==0:n//=p;c+=1
        out.append(c)
    check(n==1);return tuple(out)
def entmass(m,i): # equals m e(i/m)
    j=m-i
    return add(scale(m,lp(m)),scale(-i,lp(i)),scale(-j,lp(j)))
@lru_cache(None)
def expectedcounts(m):
    if m==1:return zero(N-1)
    return add(innerrow(m),mean((q(m,i),add(expectedcounts(i),expectedcounts(m-i))) for i in range(1,m)))
@lru_cache(None)
def entmean(m):return mean((q(m,i),entmass(m,i)) for i in range(1,m))
@lru_cache(None)
def condbrackets(m):
    dif=[];eds=[]
    for i in range(1,m):
        j=m-i
        dif.append((q(m,i),outer(minus(add(innerrow(m),expectedcounts(i),expectedcounts(j)),expectedcounts(m)))))
        eds.append((q(m,i),outer(minus(entmass(m,i),entmean(m)))))
    return mean(dif), mean(eds)
# Explicit ordered tree lists, independent of the visit recurrence.
@lru_cache(None)
def trees(n):
    if n==1:return [(F(1),zero(N-1),zero(len(PR)),zero(len(PR)))]
    out=[]
    for i in range(1,n):
        j=n-i;w=q(n,i);d=entmass(n,i);e=entmean(n)
        for w1,s1,d1,e1 in trees(i):
            for w2,s2,d2,e2 in trees(j):
                out.append((w*w1*w2,add(s1,s2,innerrow(n)),add(d1,d2,d),add(e1,e2,e)))
    return out

def main():
    nt=small=scalar=0
    for n in range(2,N+1):
        ts=trees(n);nt+=len(ts)
        check(sum(t[0] for t in ts)==1)
        en=tuple(n*visits(n,k)/k for k in range(2,N+1))
        check(sum(en)==n-1 and en==expectedcounts(n))
        if n>2: check(all(visits(n,k)<visits(n-1,k) for k in range(2,n)))
        check(mean((w,s) for w,s,d,e in ts)==en)
        check(all(d==scale(n,lp(n)) for w,s,d,e in ts))
        check(mean((w,minus(d,e)) for w,s,d,e in ts)==zero(len(PR)))
        cv=mean((w,outer(minus(s,en))) for w,s,d,e in ts)
        ev=mean((w,outer(minus(d,e))) for w,s,d,e in ts)
        check(cv==mean((en[m-2],condbrackets(m)[0]) for m in range(2,n+1)))
        check(ev==mean((en[m-2],condbrackets(m)[1]) for m in range(2,n+1)))
        small+=2
        for p in (-2,-1,0,1,2,3):
            a=tuple(F(k)**p for k in range(2,N+1))
            variance=sum(cv[i*len(a)+j]*x*y for i,x in enumerate(a) for j,y in enumerate(a))
            check((variance>0)==(n>=4 and p!=0));scalar+=1
    # Strict inequalities for the third moment comparison: zeta(2)<5/3
    # by the finite integral-test upper bound H_2^(2)+...+sum_1^M 1/i^2+1/M.
    check(sum(F(1,i*i) for i in range(1,11))+F(1,10)<F(5,3))
    check(F(17,12)**2>2 and 2*(F(17,12)-1)<F(3,2)/F(5,3))
    print("Explicit ordered trees (leaf sizes 2..9):",nt)
    print("Full count-covariance and formal prime-log entropy bracket matrices:",small)
    print("Integer-power nondegeneracy tests:",scalar)
    print("Occupation normalization and monotonicity, entropy telescoping, third-moment comparison: PASS")

if __name__=="__main__": main()
