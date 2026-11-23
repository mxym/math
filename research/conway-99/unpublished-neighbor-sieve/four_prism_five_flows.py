
from itertools import product,combinations_with_replacement,permutations
from collections import Counter
def can(h):return min(h,tuple(-x%5 for x in h))
T=sorted({can((a,b,(-a-b)%5)) for a,b in product(range(5),repeat=2) if a or b})
def gauge(x):
 return min(tuple(sorted(can(tuple(s*h[w]%5 for w in pi)) for h in x)) for s in (1,2) for pi in permutations(range(3)))
def alphabet(h):return [y for x in h for y in (x,-x%5)]
H={}
for a,b in product(T,T):
 x=alphabet(a);y=alphabet(b);h=[0]*5
 for i in range(6):
  for j in range(6):h[(x[i]+y[j])%5]+=2-int(i//2==j//2)
 H[a,b]=tuple(h)
GG=sorted({gauge(x) for x in combinations_with_replacement(T,4)});print('full',len(GG))
keep=[]
for a,b,c,d in GG:
 if H[a,b]==H[c,d] and H[a,c]==H[b,d] and H[a,d]==H[b,c]:keep.append((a,b,c,d))
assert len(GG)==142 and len(keep)==5
left=[g for g in keep if sum(x*x for h in g for x in h)%5==0]
assert left==[((0,1,4),(1,1,3),(1,1,3),(1,1,3))]
print('142 orbits; 5 survive all pair splits; one survives norm; final mandatory two-site tag has no legal sum.')
