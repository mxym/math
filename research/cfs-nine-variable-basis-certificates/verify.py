#!/usr/bin/env python3
"""Verify both CFS certificate tables against the external classification."""
import argparse,hashlib,itertools,json,re
from collections import Counter
from pathlib import Path
from functools import lru_cache
H='c2ea3dd3bab2833596cdd83376b5289257fd20a91c435a080abd8f5902718f17'
E=[1<<j for j in range(9)]
pairs=list(itertools.combinations(range(9),2))
triples=list(itertools.combinations(range(9),3))
quads=list(itertools.combinations(range(9),4))
def ck(ok,msg):
 if not ok:raise ValueError(msg)
def read_catalogue(p):
 b=Path(p).read_bytes();ck(len(b)==37877 and hashlib.sha256(b).hexdigest()==H,"wrong input catalogue")
 R={}
 for l in b.decode('latin-1').splitlines():
  m=re.fullmatch(r'\s*(\d+) h=[0-9a-f]+\s*((?:\+\d{3})*)\s*',l)
  if not m:continue
  i=int(m[1]);ck(i not in R,"duplicate catalogue ID")
  ts=[tuple(int(k)-1 for k in t) for t in m[2].split('+')[1:]]
  ck(len(ts)==len(set(ts)) and all(0<=j<k<h<9 for j,k,h in ts),"bad catalogue monomial")
  R[i]=ts
 ck(set(R)==set(range(1,350)) and [i for i,v in R.items() if not v]==[349],"catalogue IDs or zero orbit")
 return R
def checkbasis(B):
 ck(type(B)==list and len(B)==9 and all(type(v)==int and 0<v<512 for v in B),"basis format")
 V={0}
 for x in B:V|={z^x for z in V}
 ck(len(V)==512,"singular basis")
def prove(R,d,kind):
 ck(type(d)==list and [x[0] for x in d]==list(range(1,350)),"certificate IDs")
 C=Counter()
 for idx,tag,*args in d:
  ts=R[idx];C[tag]+=1
  @lru_cache(maxsize=None)
  def ev(a,b,c):
   return sum(((a>>i)&1)*((b>>j)&1)*((c>>k)&1) for t in ts for i,j,k in itertools.permutations(t))%2
  if tag==('radical' if kind==2 else 'factor'):
   ck(len(args)==1 and type(args[0])==int and 0<args[0]<512,"zero or invalid obstruction")
   h=args[0]
   if kind==2:ck(all(not ev(h,E[j],E[k]) for j,k in pairs),f"radical failure:{idx}")
   else:ck(all(not(sum(((h>>u)&1) for u in q if tuple(v for v in q if v!=u) in ts)%2) for q in quads),f"factor failure:{idx}")
  else:
   ck(tag in (('standard','slice','descent') if kind==2 else ('standard','descent')) and len(args)==2,"unknown tag")
   B,W=args;checkbasis(B);ck(len(W)==9,"missing witness")
   if tag=='standard':ck(B==E,"wrong standard-basis label")
   if kind==2:
    for i,p in enumerate(W):
     ck(type(p)==list and len(p)==2 and all(type(a)==int for a in p) and tuple(p) in pairs,"pair format")
     ck(all(ev(B[p[0]],B[p[1]],z)==int(j==i) for j,z in enumerate(B)),f"pair failure:{idx}:{i}")
   else:
    for i,q in enumerate(W):
     ck(type(q)==list and len(q)==4 and all(type(a)==int for a in q) and tuple(q) in quads and i in q,"4-set format")
     ck(all(ev(*(B[v] for v in q if v!=u))==int(i==u) for u in q),f"4-set failure:{idx}:{i}")
 assert_matches=({'radical':32,'slice':308,'standard':4,'descent':5} if kind==2 else {'factor':5,'standard':300,'descent':44})
 ck(C==Counter(assert_matches),"wrong orbit totals")
 return dict(sorted(C.items()))
def main():
 p=argparse.ArgumentParser();p.add_argument('catalogue');p.add_argument('--negative-controls',action='store_true');a=p.parse_args()
 R=read_catalogue(a.catalogue)
 for k in (1,2):
  d=json.loads(Path(__file__).with_name(f'op{k}-certificates.json').read_text())
  print(f'PASS OP{k}, 349 orbits:',prove(R,d,k))
  if not a.negative_controls:continue
  def mutate_test(label,f):
   b=json.loads(json.dumps(d));f(b)
   try:prove(R,b,k)
   except ValueError:print(f'REJECTED OP{k}:',label);return
   raise ValueError('negative test accepted: '+label)
  s=next(i for i,r in enumerate(d) if len(r)==4);t=next(i for i,r in enumerate(d) if len(r)==3)
  mutate_test('missing row',lambda b:b.pop())
  mutate_test('dependent basis',lambda b:b[s][2].__setitem__(0,b[s][2][1]))
  mutate_test('incorrect designated witness',lambda b:b[s][3].__setitem__(0,b[s][3][1]))
  mutate_test('zero obstruction',lambda b:b[t].__setitem__(2,0))
 print('OK: both full tables verified.')
if __name__=='__main__':main()
