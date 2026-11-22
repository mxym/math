"""Exact consistency checks, not a replacement for Weil or the analytic proofs."""
from fractions import Fraction as F
from itertools import product, combinations
from math import gcd, isqrt, prod
from random import Random

def ck(p, text):
    if not p:
        raise RuntimeError(text)

def D(w): return F(w)
t1=lambda v: D(".766")-v/2
t2=lambda v: D(".918")-v
t3=lambda v: D(".674")-v/4
ck(t1(D(".304"))==t2(D(".304")),"base junction")
for v in map(D,(".13",".304",".32")):
    ck(min(t1(v),t2(v))-t3(v)>=D(".004"),"strict factored annulus")
    ck(2*t3(v)>1-v and 1-v-t3(v)<D(".24"),"middle HB legality")
for v in map(D,(".304",".495")):
    ck(2*t2(v)>1-v and 1-v-t2(v)==D(".082"),"two-free HB legality")
ck(D(".082")+F(3,2)*D(".6092")==D(".9958"),"modular rectangle summed power")
ck(D(".234")-D(".157")/2<D(".157"),"base nonnegative score")
ck(D(".326")-F(3,4)*D(".187")<D(".187"),"wider nonnegative score")
ck(D(".082")<D(".157"),"two-free half nonnegative")
ck(D(".918")+D(".25")>1,"balanced triprime no proper a")
ck(1-D(".38")-D(".02")>D(".423"),"signed mass subfamily")
for k in (D("1"),D("1.05"),D("1.1")):
    ck(2-D(".8")*k<D("1.22")<D("1.26")<2-D(".65")*k,"common y radial range")

# Empirically check the exact complete block decomposition, including intervals > A.
rng=Random(239)
nrect=0
for A in range(2,88):
    units=[j for j in range(A) if gcd(j,A)==1]
    phi=len(units)
    for _ in range(48):
        b=rng.choice(units)
        u,v = rng.randrange(-2*A,2*A),rng.randrange(-2*A,2*A)
        M,S = rng.randrange(4*A),rng.randrange(4*A)
        a,r=divmod(M,A); c,t=divmod(S,A)
        I=range(u,u+r); J=range(v,v+t)
        full=a*c*phi+a*sum(gcd(j,A)==1 for j in J)+c*sum(gcd(i,A)==1 for i in I)
        small=sum((i*j-b)%A==0 for i,j in product(I,J))
        actual=sum((i*j-b)%A==0 for i,j in product(range(u,u+M),range(v,v+S)))
        ck(actual==full+small,"literal full-period decomposition")
        ck(F(phi,A*A)*(A*a)*(A*c)==a*c*phi,"complete unit normalization")
        nrect+=1

def prime_after(p):
    k=(p+1)|1
    while any(k%i==0 for i in range(3,isqrt(k)+1,2)):
        k+=2
    return k

p2=[prime_after(p) for p in [94_321,998_991,98_765_339,999_999_940,
                              1_000_000_010,1_000_001_050,10_000_000_100,
                              90_000_000_071,180_010_010_000]]
p3=[prime_after(p) for p in [1_001_011,2_014_900,3_020_002,4_017_650,5_491_190,
                              6_374_820,7_123_000,8_661_220,9_134_966]]
def subsets(P):
    return [(prod(B),len(B)) for n in range(len(P)+1) for B in combinations(P,n)]

def selected(x,a,s,wider):
    if wider and x**130<=s**1000<=x**320:
        return a**1000*s**250>x**674
    return a**1000*s**500>x**766 or (a*s)**1000>x**918

n2=n3=n3all=0
for P in list(combinations(p2,2))+list(combinations(p3,3))+list(combinations(p2,3)):
    y=prod(P); x=(4*y)//5
    ds=subsets(P)
    K={}; G0={}; G1={}
    for s,o in ds:
        if s==1: continue
        r=y//s
        if r**1000<=x**505: continue
        K[s]=(-1)**(len(P)-o)
        for c,oc in ds:
            if r%c: continue
            a=r//c
            w=(-2)**oc
            if selected(x,a,s,False): G0[s]=G0.get(s,0)-w
            if selected(x,a,s,True): G1[s]=G1.get(s,0)-w
    if len(P)==2:
        ck(K==G0==G1,"real semiprime annihilation, both cutoffs")
        n2+=1
    else:
        for s,val in K.items():
            ck(val-G0.get(s,0) in (0,2) and val-G1.get(s,0) in (0,2),
               "all genuine triprime coefficients are nonnegative")
        n3all+=1
        if min(P)**4>=x:
            neg={s:-m for s,m in K.items()}
            ck(neg==G0==G1,"central real triprime coefficient doubles")
            n3+=1
print(f"exact exponent margins, {nrect} hyperbola decompositions, {n2} genuine semiprimes, "
      f"{n3all} genuine triprimes ({n3} central) pass")
