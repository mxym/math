"""Finite diagnostics for proof constants and labeled-factor / truncation identities."""
from fractions import Fraction as F
from itertools import combinations,product
from math import comb, prod, gcd, lcm
import random
def ck(b,m):
    if not b: raise RuntimeError(m)
beta=F(8,1000);eta=F(1,10000); M=F(1,2)+beta+eta
loss=beta+eta
ck((33*M-17)/20+loss < -F(3,1000),"BC1 gap")
ck((15*M-8)/8+loss < -F(3,1000),"BC2 gap")
ck(F(85,100)+M/4+loss < F(99,100),"H<1 BC1")
ck(F(875,1000)+M/8+loss < F(99,100),"H<1 BC2")
ck(F(98,100)+2*beta+eta < F(997,1000),"small dyads")
ck(F(1,2)+F(23,1000)+F(1,2000)<min((1+F(5,100))/2,F(4,7)-F(6,7)*F(54,1000)),"fixed right rail")
ck(F(1,2)+F(4,100000)+F(5,1000000)<F(50005,100000),"full right rail")
pr=[2,3,5,7,11]
div={prod(x):(-1)**h for h in range(len(pr)+1) for x in combinations(pr,h)}
for T,Q in product(div,range(2,100)):
    a=sum((F(mu,lcm(d,T)) for d,mu in div.items() if d<=Q),F(0))
    b=sum((F(s*mu,T*e) for g,s in div.items() if T%g==0 for e,mu in div.items() if gcd(T,e)==1 and e*g<=Q),F(0))
    ck(a==b,"marked harmonic identity")
def subsets(x):return [j for j in range(1<<5) if j&x==j]
subs=[subsets(i) for i in range(32)]
rng=random.Random(20261121)
f={(a,b):(rng.randrange(-10,11) if a*b else 0) for a,b in product(range(32),repeat=2)}
c={(a,b):sum((-1)**((a^t).bit_count()+(b^u).bit_count())*f[t,u] for t in subs[a] for u in subs[b]) for a,b in f}
for a,b in f:
    ck(f[a,b]==sum(c[t,u] for t in subs[a] for u in subs[b]),"arbitrary bivariate selector")
    ck((a*b or c[a,b]==0) and abs(c[a,b])<=10*2**(a.bit_count()+b.bit_count()),"coefficient envelope")
for K in range(1,12):
 for n in range(K+1,50):
    for h in range(K+1):ck(comb(n,h)<=comb(K+1,h)*comb(n,K+1),"tail domination")
print('All exact rail, marked-divisor, Boolean-selector and factorial inequalities passed.')
