"""Exact small checks of the clock bounds; tests supplement the analytic proof."""
from fractions import Fraction as Q
from itertools import product

def req(v):
    if not v: raise ArithmeticError("failed rational certificate")
def logi(x):
    """Certified rational enclosure of log(x), x>=1."""
    req(x>=1)
    u=(x-1)/(x+1); power=u; s=Q(0)
    for j in range(12):
        s+=power/(2*j+1);power*=u*u
    return 2*s,2*(s+power/(25*(1-u*u)))
def L(p):
    if p==0:return Q(1),Q(1)
    lo,hi=logi(1/(1-p)); return lo/p,hi/p
def D(t,atoms):
    return sum(p*max(Q(),t-z) for z,p in atoms)
def F(t,atoms):
    return sum((p for z,p in atoms if z<=t),Q())
cases=crossed=0
for si in [(0,2,5,11),(0,1,7,14),(0,3,4,8)]:
    for w in [(1,2,3,4),(2,1,1,5)]:
        atoms=[(Q(z,16),Q(p,sum(w))) for z,p in zip(si,w)]
        for k in range(4,si[-1]*4):
            g=Q(k,64); new=g-D(g,atoms); a=F(g,atoms);b=F(new,atoms)
            req(0<new<g and 0<b<=a<1)
            # Independently split the exact one-step integral at every cdf jump.
            breaks=[new]+[z for z,p in atoms if new<z<g]+[g]
            lo=hi=Q(0)
            for x,y in zip(breaks,breaks[1:]):
                p=F((x+y)/2,atoms)
                d,e=D(x,atoms),D(y,atoms)
                req(e-d==p*(y-x))
                num=logi(e/d);den=logi(1/(1-p))
                lo+=num[0]/den[1];hi+=num[1]/den[0]
            if a==b:
                # D is affine across the full step; exact ratio is one.
                req(D(new,atoms)==(1-a)*D(g,atoms) and lo<=1<=hi)
            else:
                Aa=L(a);Bb=L(b)
                req(Bb[1]/Aa[0]<=lo<=hi<=Aa[0]/Bb[1]);crossed+=1
            cases+=1
req(crossed>0)
print(f"Corrected one-step clock: {cases} certified rational cases, {crossed} with different endpoint slopes.")

# Uniform conditional positive cost, with a genuine zero atom:
# S=q(1-x) on (0,1), M_n=q^n/(n+1); G_{n+1}=q G_n(1-G_n/2).
# G_i<=q^i/2 implies G_n/q^n >= (1/2)(1-sum_{i>=1}q^i/4)
# for q<=1/2, hence >=3/8. This illustrates *divergence* in the theorem.
for q in [Q(1,4),Q(1,3),Q(1,2)]:
    req(Q(1,2)*(1-q/(4*(1-q)))>=Q(3,8))
    g=q/2
    for n in range(1,10):
        M=q**n/(n+1);req(g/M >= Q(3*(n+1),8))
        g=q*g*(1-g/2)
print("Zero atom plus uniform positive component: 27 exact Bellman/prophet comparisons.")

# Fair zero atom; Y uniform on {1,2}; beyond n=1, G_n=3/2^(n+1);
# M_n=(1/2)^n+(1/4)^n. Compare explicit enumeration with limit ratio 3/2.
for n in range(1,8):
    atoms=[(0,Q(1,2)),(1,Q(1,4)),(2,Q(1,4))]
    import math
    m=sum(min(x[0] for x in r)*math.prod(x[1] for x in r) for r in product(atoms,repeat=n))
    req(m==Q(1,2)**n+Q(1,4)**n)
    g=Q(3,2**(n+1));req(g/m==Q(3,2)/(1+Q(1,2)**n))
print("Zero atom and positive gap: exact order-statistic enumeration for 7 horizons.")
