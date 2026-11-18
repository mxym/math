"""Check exact finite rankings, strict ties and conditional change of measure.
Finite regressions only; prerequisites: Python standard library."""
from itertools import product, permutations
from collections import Counter
from fractions import Fraction as F
from math import factorial, prod
def ck(cond,msg):
    if not cond: raise ArithmeticError(msg)
def integrated(n,m):
    # Row pattern of the distinguished candidate in d pairwise comparisons
    # has beta-integral mass k!(d-k)!/(d+1)!; use integer weights.
    d=n-1
    W={v:factorial(sum(v))*factorial(d-sum(v)) for v in product((0,1),repeat=d)}
    ck(sum(W.values())==factorial(n),'rank mass')
    D={d*(0,):1}
    for _ in range(m):
        O=Counter()
        for z,c in D.items():
            for v,w in W.items(): O[tuple(a+b for a,b in zip(z,v))]+=c*w
        D=O
    return F(sum(t for z,t in D.items() if min(z)>m/2)*n, factorial(n)**m)
def direct(n,m):
    # Enumerate all permutations, retaining every candidate's comparisons.
    ps=list(permutations(range(n))); keys=list(permutations(range(n),2))
    ops=[[p.index(i)<p.index(j) for i,j in keys] for p in ps]
    count=0
    for prof in product(ops,repeat=m):
        wins=set(range(n))
        for idx,(i,_) in enumerate(keys):
            if i in wins and 2*sum(v[idx] for v in prof)<=m: wins.remove(i)
        ck(len(wins)<=1,'two strict winners')
        count+=len(wins)
    return F(count,len(ps)**m)
cases=[(n,m) for n,maxm in [(2,8),(3,6),(4,3),(5,2)] for m in range(1,maxm+1)]
for n,m in cases:
    q=integrated(n,m)
    ck(q==direct(n,m),'exact rank-integral and enumeration differ')
    if m==2: ck(q==F(1,n),'strict even electorate')
ck(integrated(3,3)==F(17,18),'3x3 election')
print(f'PASS: {len(cases)} exact complete-profile elections (odd/even); 3x3=17/18; two voters Q=1/n')
# For rational t=exp(a), the RN formula is algebraic. Verify each vector, not a sample of events.
num=0
for m in [2,3,4,5,6,7,8]:
    u=[F(i+2,2*m+3) for i in range(m)]
    for t in map(F,[1,2,3,5]):
        h=[t*(1-x)+x/t for x in u];q=[x/t/z for x,z in zip(u,h)]
        # q(x)=x/(t^2+(1-t^2)x), derivative q'(x)=h^-2 and endpoints 0,1.
        for x,z in zip(u,h): ck(t*t/(t*t+(1-t*t)*x)**2==1/z**2,'environment Jacobian')
        for v in product((0,1),repeat=m):
            w=lambda ps:prod(y if bit else 1-y for bit,y in zip(v,ps))
            ck(w(u)==w(q)*prod(h)*t**(2*sum(v)-m),'Bernoulli RN derivative')
            num+=1
print(f'PASS: {num} exact Bernoulli outcome/tilt likelihood identities; rational environment Jacobian')
# Cube independent orientation: exact factorial moments first/second, all orientations for d<=3.
for d in [1,2,3]:
    N=2**d; edges=[(u,u^(1<<i)) for u in range(N) for i in range(d) if not (u>>i)&1]
    tot=2**len(edges);one=two=0
    for v in product((0,1),repeat=len(edges)):
        sinks=set(range(N))-{e[i] for e,i in zip(edges,v)}
        k=len(sinks);one+=k;two+=k*(k-1)
    ck(F(one,tot)==1,'fair-orientation expectation')
    ck(F(two,tot)==F(N-1-d,N),'fair-orientation distinct non-neighbors')
print('PASS: fair-orientation first/second factorial moments, exhaustive cubes d=1,2,3')
