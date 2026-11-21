from itertools import combinations,combinations_with_replacement
from math import isqrt
from collections import defaultdict,deque
import json
from pathlib import Path
P=[p for p in range(3,318,2) if all(p%i for i in range(2,isqrt(p)+1))]; A=(19,283,313);B=(17,281,317)
def get(t):
 pairs=defaultdict(list)
 for a,b,c in combinations_with_replacement(P,3):
  d=t+615-a-b-c
  if d<c or d not in P:continue
  st=(a,b,c,d)
  for ij in set(combinations(st,2)):pairs[ij].append(st)
 U=tuple(sorted((t,)+A));V=tuple(sorted((t,)+B));Q=deque([U]);prev={U:None}
 while Q and V not in prev:
  n=Q.popleft()
  for ij in combinations(n,2):
   for z in pairs.pop(ij,()):
    if z not in prev:prev[z]=n;Q.append(z)
 if V not in prev:raise ValueError((t,'not connected'))
 path=[V]
 while path[-1]!=U:path.append(prev[path[-1]])
 return list(reversed(path))
paths={p:get(p) for p in P};f=Path(__file__).with_name('prefix317_paths.json');f.write_text(json.dumps(paths,separators=(',',':'))+'\n')
print('wrote',len(paths),'paths',sum(len(r)-1 for r in paths.values()),'moves; maximal individual length',max(map(len,paths.values()))-1)
