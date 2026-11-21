from pathlib import Path
import json
from collections import Counter
def ck(b,m):
 if not b: raise ValueError(m)
def prime(n):return n>1 and all(n%i for i in range(2,n) if i*i<=n)
def main():
 P={n for n in range(3,318) if prime(n)};A=(19,283,313);B=(17,281,317)
 ck(all(x%3==1 for x in A) and all(x%3==2 for x in B) and sum(A)==sum(B)==615,'sectors')
 ck(not any(612-p in P for p in P),'unexpected bridge via 3')
 paths=json.loads(Path(__file__).with_name('prefix317_paths.json').read_text());ck(set(paths)==set(map(str,P)),'prefix incomplete')
 lengths=[]
 for k,L in paths.items():
  t=int(k);ck(L[0]==sorted((*A,t)) and L[-1]==sorted((*B,t)),'endpoints')
  for z in L:ck(len(z)==4 and sum(z)==615+t and all(x in P for x in z),'not a prime quartet')
  for a,b in zip(L,L[1:]):
   x,y=Counter(a)-Counter(b),Counter(b)-Counter(a)
   ck(sum(x.values())==sum(y.values())==2 and sum(x.elements())==sum(y.elements()),'not a binary move')
  lengths.append(len(L)-1)
 print('complete prefix 317, all',len(P),'socle annihilators certified by',sum(lengths),'literal equal-pair moves; longest path',max(lengths),'PASS')
if __name__=='__main__':main()
