from itertools import permutations, product, combinations
from collections import Counter
from math import prod
P=11;k=6;m=4
cases=[
(0,0,0,0,1,1),(0,0,0,1,1,1),(0,0,0,0,1,3),(0,0,0,1,1,3),
(0,0,1,1,3,3),(0,0,0,1,3,9),(0,0,1,1,3,9),(0,0,1,3,5,9),(0,1,2,3,4,5)
]
def projective(n):
 for i in range(n):
  for tail in product(range(P),repeat=n-i-1):
   yield (0,)*i+(1,)+tail
def rrefs(r):
 for piv in combinations(range(m),r):
  free=[(i,j) for i,p in enumerate(piv) for j in range(p+1,m) if j not in piv]
  for v in product(range(P),repeat=len(free)):
   b=[[int(j==p) for j in range(m)] for p in piv]
   for (i,j),x in zip(free,v):b[i][j]=x
   yield b
for labels in cases:
 S=sorted(set(permutations(labels)));L=len(S)
 c=Counter(labels); C=prod(v**v for v in c.values())
 D={v:Counter() for v in c}
 for x,y in product(S, repeat=2):
  if x[-1]!=y[-1]:continue
  d=tuple((u-v)%P for u,v in zip(x[:m],y[:m]))
  lead=next((i for i in d if i),0)
  f=pow(lead,-1,P) if lead else 0
  D[x[-1]][tuple(f*x%P for x in d)]+=1
 ds={d:tuple(D[v][d] for v in c) for d in set().union(*D.values())}
 for r in range(1,m):
  coef=list(projective(r)); zeros=ds[(0,)*m]
  maximum=0;target=L**((m+r)*k)*C**(m+r)
  for B in rrefs(r):
   nn=list(zeros)
   for a in coef:
    d=tuple(sum(x*y for x,y in zip(a,col))%P for col in zip(*B))
    if d in ds:
     for i,x in enumerate(ds[d]):nn[i]+=x
   value=prod(n**(m*v) for n,v in zip(nn,c.values()))*k**((m+r)*k)
   maximum=max(maximum,value)
  assert maximum < target, (labels,r)
  print(labels,r,maximum<target, flush=True)
