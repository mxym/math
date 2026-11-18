from itertools import combinations
from collections import Counter
def rank(xs):
 ps={}
 for a in xs:
  while a:
   j=a.bit_length()
   if j not in ps:ps[j]=a;break
   a^=ps[j]
 return len(ps)
def components(S):
 a=Counter(i^j for i,j in combinations(S,2)); rem=set(S); out=[]
 while rem:
  t={min(rem)}
  while True:
   x={j for i in t for j in rem if a[i^j]==1}
   if x<=t:break
   t|=x
  rem-=t;out.append(sorted(t))
 return sorted(out)
def canonical4(h):
 # Orbit representatives using the fact that every full affine span contains an affine frame.
 d=4;B=[0,1,2,4,8];others=[i for i in range(16) if i not in B]
 masks={frozenset(B+list(T)) for T in combinations(others,h-5)};ans=[]
 while masks:
  S=min(masks,key=lambda x:tuple(sorted(x)));ans.append(S)
  # Walk over affine frames chosen in S. Include all orderings.
  from itertools import permutations
  for x in S:
   for tup in permutations(S-{x},4):
    xs=[v^x for v in tup]
    if rank(xs)!=4:continue
    T=[x]
    for v in xs:T += [u^v for u in T]
    masks.discard(frozenset(i for i,y in enumerate(T) if y in S))
 return ans
if __name__=='__main__':
 for h in range(5,9):
  S=canonical4(h);print(h,len(S))
  for s in S:print(sorted(s),list(map(len,components(s))),sum(all(x^a in s for x in s) for a in range(1,16)))
