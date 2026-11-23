from itertools import combinations,permutations,product
from collections import defaultdict
from functools import lru_cache
V=range(16); H8=range(8)
P=[x for x in V if x.bit_count()%2==0];N=[x for x in V if x.bit_count()%2==1]
def bits(x):return [i for i in range(x.bit_length()) if x>>i&1]
I=lambda x: (P+N).index(x)
M=tuple(sum(1<<j for j,n in enumerate(N)if (p^n).bit_count()==1)for p in P)
pp=[(p,p^15)for p in P if p<8]; nn=[(n,n^15)for n in N if n<8]
cells=[sum(1<<I(x)for x in a+b)for a in pp for b in nn]
GP=[]
for g in permutations(range(4)):
 for s in V:
  G=[I(s^sum(1<<g[i] for i in bits(x))) for x in P+N]
  GP.append(tuple(cells.index(sum(1<<G[i] for i in bits(y)))for y in cells))
def forms():
 seen=set();out=[]
 for rows in product(combinations(range(4),2),repeat=4):
  if any(sum(i in r for r in rows)!=2 for i in range(4)):continue
  ix=tuple(4*i+j for i,row in enumerate(rows)for j in row)
  if ix in seen:continue
  orb={tuple(sorted(g[i] for i in ix))for g in GP};seen.update(orb)
  st={tuple(ix.index(g[i])for i in ix)for g in GP if tuple(sorted(g[i]for i in ix))==ix}
  T=[cells[i]for i in ix];out.append((T,()))
  marked=set()
  for i,j in combinations(H8,2):
   if T[i]&T[j] or (i,j)in marked:continue
   marked.update(tuple(sorted((p[i],p[j])))for p in st);out.append((T,(i,j)))
 return out

def cycle_type(T):
 G=[{j for j,r in enumerate(T) if i!=j and r&s}for i,s in enumerate(T)]
 assert all(len(g)==2 for g in G)
 seen=set();sizes=[]
 for i in range(8):
  if i in seen:continue
  cc={i};q=[i]
  while q:
   for j in G[q.pop()]:
    if j not in cc:cc.add(j);q.append(j)
  seen.update(cc);sizes.append(len(cc))
 return sorted(sizes)
charts=forms()
assert len(charts)==24
reps=[(i,T)for i,(T,E)in enumerate(charts)if not E and cycle_type(T)==[8]]
assert [i for i,T in reps]==[4,10]
print("24 portraits: 4 unmarked, 20 with one height-two edge; analytic cut leaves edgeless C8 portraits 4 and 10.")
for i,T in reps:print(i,T)
