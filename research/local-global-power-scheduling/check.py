"""Finite exact checks only. Python standard library; assertions are not used."""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product

S=10**22
def ensure(ok, msg):
    if not ok:
        raise ArithmeticError(msg)
def iroot(a, d):
    l=0; r=1<<((a.bit_length()+d-1)//d)
    while r-l>1:
        m=(l+r)//2
        if m**d<=a: l=m
        else: r=m
    return r if r**d<=a else l
@lru_cache(maxsize=None)
def power(x, a, d):
    x=Q(x); y=x**a*S**d
    k=iroot(y.numerator//y.denominator,d)
    ensure(Q(k**d)<=y<Q((k+1)**d),"root")
    return Q(k,S),Q(k+(k**d!=y),S)
def sub(x,y): return x[0]-y[1],x[1]-y[0]
def mul(x,y):
    v=[a*b for a,b in product(x,y)]
    return min(v),max(v)
def div(x,y):
    ensure(y[0]>0, "nonpositive denominator")
    return mul(x,(1/y[1],1/y[0]))
def scalar(x): return (Q(x),Q(x))
def add(x,y): return x[0]+y[0],x[1]+y[1]
bs,ordr,case=0,0,0
for num,den in [(1,5),(1,4),(1,3),(1,2),(2,3),(3,4),(4,5),(9,10)]:
    def f(x): return power(x,num,den)
    def D(l,x): return sub(f(x+l),f(x))
    for p in [2,3,4,7,11,31]:
        for q in sorted({1,p//2,p-1}):
            cutoff=div(D(p,q),D(q,p))
            for b in [1,2,3,7,11,31,127,1024]:
                U=mul(div(D(p-q,b+q),D(p,b)), div(D(b,p),D(b,p+q)))
                T=mul(scalar(Q(p-q,p)),power(Q(p+q,p),den-num,2*den))
                R=div(D(p-q,q),D(p,q))
                ensure(U[1]<T[0] and T[1]<R[0],("separator",num,den,p,q,b))
                bs+=1
            W=1009; w=(cutoff[1]*W).__floor__()+1
            ensure(Q(w,W)>cutoff[1],"not locally dominant")
            i,j=(p,w),(q,W)
            for start in [0,3,19]:
                for jobs in [[(1,10)],[(5,1021)],[(13,18291)],[(2,67),(1,2001),(17,11293)],[(11,11009),(2,333),(1,120)],[(8,12923),(7,7731),(2,2965),(19,10101)]]:
                    def objective(items):
                        t=start; c=scalar(0)
                        for pt,wt in items:
                            t+=pt; c=add(c,mul(scalar(wt),f(t)))
                        return c
                    inv=objective([j,*jobs,i])
                    c1,c2=objective([*jobs,i,j]), objective([i,*jobs,j])
                    ensure(min(c1[1],c2[1])<inv[0],("schedule",num,den,p,q,start,jobs))
                    ordr+=1
            case+=1
print(f"PASS: {case} ordered pair/exponent cases, {bs} strict algebraic separator enclosures, {ordr} direct block permutations with at least one strictly smaller comparison.")
print("All roots bounded by integer powering; analytical proof, not this finite check, covers the full domain.")
