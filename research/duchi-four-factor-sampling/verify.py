"""Exact four-factor Duchi witness. Python standard library only; no numerical optimization."""
from fractions import Fraction as F
from itertools import permutations,product
from math import prod
from collections import Counter
def check(v,msg):
    if not v: raise ArithmeticError(msg)
def falling(n,k):return prod(n-j for j in range(k))
def wordtypes(w=()):
    if len(w)==4:yield w;return
    for i in range(max(w,default=-1)+2):yield from wordtypes(w+(i,))
c,h=F(99,101),F(20,101)
check(c*c+h*h==1,'rotation is not unitary')
v=[(F(1),F(0))]
for i in range(3):
    x,y=v[-1];v.append((c*x-h*y,h*x+c*y))
dot=lambda a,b:sum(x*y for x,y in zip(a,b))
g=[[abs(dot(x,y)) for y in v] for x in v]
check(all(dot(x,x)==1 for x in v),'not rank-one unit vectors')
B=(0,3,3,0);s=[c**b for b in B]
def score(z):
    return prod(s[j] for j in z)*prod(g[a][b] for a,b in zip(z,z[1:]))
def cost(z):
    return sum(B[j] for j in z)+sum((a-b)**2 for a,b in zip(z,z[1:]))
S=Counter();T=Counter();types={};n_types=Counter()
for w in wordtypes():
    k=max(w)+1; images=[tuple(f[j] for j in w) for f in permutations(range(4),k)]
    val=max(map(score,images));tau=min(map(cost,images))
    types[w]=val;S[k]+=val;T[k]+=tau;n_types[k]+=1
check([T[k] for k in range(1,5)]==[0,42,63,9],'false loss coefficient')
check([n_types[k] for k in range(1,5)]==[1,7,6,1],'incomplete patterns')
H=types[(0,1,2,3)]
check(H==c**9,'wrong optimum on four distinct labels')
D=1126825030131969720661201
a,b,e=82396441351706403933495,453284944698127805248788,278074855080257891924992
def poly(n):return F(2*n*(a*n*n-b*n+e),D)
def diff(n):return n**4*H-sum(falling(n,k)*S[k] for k in range(1,5))
# Both are polynomials in n of degree at most four: five points prove identity.
check(all(diff(n)==poly(n) for n in range(5)), 'rational coefficient certificate')
check(a>0 and 10*a-b>0 and 25*a-5*b+e>0,'quadratic not positive for all n>=5')
delta=diff(5)/625
# Second enumeration at n=5: build all sixty distinct reversed-pair blocks and all 625 words.
blocks=[f for f in permutations(range(5),4) if f[0]<f[-1]]
check(len(blocks)==60,'wrong dimensions')
lookup=[dict((label,j) for j,label in enumerate(f)) for f in blocks]
direct={}
for w in product(range(5),repeat=4):
    val=max((score(tuple(f[j] for j in w)) for f in lookup if all(j in f for j in w)),default=F(0))
    direct[w]=val
wr=sum(direct.values())/625
wor=sum(v for w,v in direct.items() if len(set(w))==4)/120
check(wor-wr==delta and delta>0,'full labeled enumeration mismatch')
print('PASS: analytic loss table, uniform rational inequality and labeled n=5 certificate.')
print('WOR =',wor,'; WR =',wr,'; gap =',delta)
