from itertools import product,combinations
from pathlib import Path
def pair(p,q):
 x,z=p;u,v=q;return ((x&v)^(z&u)).bit_count()%2
H=[tuple(int(v[::-1],2)for v in l.split())for l in Path('known16.txt').read_text().splitlines()]
assert len(H)==11 and all(pair(row,q)==0 for row in H for q in H)
S={(0,0)}
for x,z in H:S|={(a^x,b^z)for a,b in S}
assert len(S)==2048
for w in range(1,5):
 n=0;hit=None
 for t in combinations(range(16),w):
  for u in product((1,2,3),repeat=w):
   p=(sum(((v&1)<<i)for i,v in zip(t,u)),sum(((v>>1)<<i)for i,v in zip(t,u)))
   if p not in S and all(not pair(p,h)for h in H):hit=p;n+=1
 if w<4:assert not n
 else:assert n;print('PASS: explicit [[16,5,4]] stabilizer; logical weight-four Paulis =',n,', example masks',hit)
