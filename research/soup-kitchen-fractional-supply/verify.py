"""Exact arithmetic sanity checks. No third-party packages, nonzero exit on failure."""
from fractions import Fraction as F
from itertools import product
from math import comb
from collections import defaultdict

def ck(condition, label):
    if not condition:
        raise ArithmeticError(label)

def conv(a,b):
    out=defaultdict(F)
    for x,p in a.items():
        for y,q in b.items():
            out[x+y]+=p*q
    return dict(out)

def stats(K, laws):
    d={F(0):F(1)}
    for p in laws: d=conv(d,p)
    return sum(p for x,p in d.items() if x>=K),sum(min(x,K)*p for x,p in d.items())

K=F(3,2); law={F(0):F(3,4),F(3,4):F(1,4)}
s,T=stats(K,[law]*3)
ck((1-s,T/K)==(F(27,32),F(47,128)),"three diners")
z=F(1,3);lo=2*(z+z**3/3);hi=2*z/(1-z*z)
ck(F(11,16)<lo<hi and (1+lo)/2>1-s and F(1,2)-hi/6>T/K,"Poisson bracket")
# Strict inequality in the upper geometric series gives log 2 < hi.
print("Three iid diners: availability 27/32, relative throughput 47/128; rational log(2) bracket separates every Poisson mean. PASS")

def coeff(k):
    c=k-1; return max(4/k**2,1/(c*(2-c)))

def paid(k,nu):
    return sum(p*q for x,p in nu.items() for y,q in nu.items() if x+y>=k)

# Exhaustive count weights on a common finite grid, selecting every threshold.
count=0;grid=[F(i,5) for i in range(1,6)]
for w in product(range(4),repeat=5):
    cost=sum(x*a for x,a in zip(grid,w))
    if not cost:continue
    nu=dict(zip(grid,w))
    for j in range(6,11):
        k=F(j,5)
        ck(paid(k,nu)<=coeff(k)*cost*cost,"pair-kernel inequality")
        count+=1
# Analytic equality measures on both branches and the common endpoints.
def winner(k):
    c=k-1;h=k/2
    if k>=F(6,5):return {h:1/h}
    B=1/(2-c);return {c:(1-B)/c,F(1):B}
eq=0
for j in range(1,101):
    k=1+F(j,100);c=k-1;h=k/2
    nu=winner(k)
    ck(sum(x*w for x,w in nu.items())==1 and paid(k,nu)==coeff(k),"achiever")
    ck((4/k**2>=1/(c*(2-c)))==(k>=F(6,5)),"crossover")
    eq+=1
print(f"{count} grid kernel inequalities; {eq} rational sharp measures, including the 6/5 switch and K=2. PASS")

# Count exact-two and 3+-jump remainder directly, and test T=mu+O(mu^2).
count=0
for k in [F(51,50),F(11,10),F(6,5),F(3,2),F(19,10),F(2)]:
    nu=winner(k);M=sum(nu.values())
    for n in (2,3,5,8):
        for v in [F(1,50),F(1,100),F(1,200)]:
            a=v/M;w={x:a*p/n for x,p in nu.items()};w[F(0)]=1-a*M/n
            s,T=stats(k,[w]*n);mu=a
            exact2=comb(n,2)*(a/n)**2*(1-v/n)**(n-2)*coeff(k)
            ck(0<=s-exact2<=comb(n,3)*(v/n)**3,"factorial-moment sandwich")
            ck(0<=mu-T<=mu**2/2,"throughput versus mean")
            count+=1
print(f"{count} exact finite sparse instances; calibrated polynomial's two-active contribution, cubic remainder, and throughput/mean sandwich. PASS")
