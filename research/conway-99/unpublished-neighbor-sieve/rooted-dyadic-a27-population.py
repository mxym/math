from math import isqrt
from collections import Counter,defaultdict
from itertools import product,combinations,combinations_with_replacement as mega
def rootshapes():
 seen=set()
 for L in range(8):
  aa=defaultdict(set)
  for a,b in product(range(16),repeat=2):
   f=tuple(sorted(((L-3*a-b)%8,(L-3*b-a)%8)));aa[f].add((a+b)%16)
  for v in mega(sorted(aa),7):
   states={0}
   for f in v:states={(x+y)%16 for x in states for y in aa[f]}
   if 2*L%16 not in states:continue
   f=min(tuple(sorted(tuple(sorted(((s*sgn+b0)%8,(t*sgn+b0)%8)))for s,t in v))for sgn in[1,-1]for b0 in[0,4])
   if f not in seen:yield f;seen.add(f)
def pat(v):
 a=[x for k in v for x in k];pairs=[(i,j)for i,j in combinations(range(14),2)if i//2!=j//2]
 W=[(a[i]+a[j])%8 for i,j in pairs];cur=sum(min(h,8-h)**2 for h in W)
 return cur,W,pairs

from functools import cache
@cache
def rowcost(q):
 x=[i if i<4 else i-8 for i in q]
 assert not sum(x)%8
 while sum(x): 
  assert sum(x)%8==0
  d=8 if sum(x)<0 else -8
  j=min(range(len(x)),key=lambda j:(x[j]+d)**2-x[j]**2)
  x[j]+=d
 return sum(u*u for u in x)
def exactrow(v):
 mn,w,ij=pat(v)
 ms=[rowcost(tuple(sorted(w[k]for k,pp in enumerate(ij)if i in pp)))for i in range(14)]
 return sum(ms)//2

def ck(v,n):
 l=sum((tuple(x) for x in v),());p=[l[i]+l[j]for i in range(14)for j in range(i)if i//2!=j//2]
 return (n+sum(q*q for q in p)+96*sum(l))%128==0
def charges(v,j,a,t):
 for hh in [0,4]:
  vv=[tuple((i+hh)%8 for i in uv)for uv in v];r=(3*vv[0][0]-vv[0][1])%8
  for co in range(-25,26):
   if co%8!=r:continue
   g,rem=divmod(64*t-16*j-35*co*co+112*a*co-128*a*a,7)
   if rem or g<0:continue
   L=isqrt(g//2);state=[(0,0,())]
   for u,h in vv:
    opts=[(c,d,3*c*c-2*c*d+3*d*d)for c in range(-L,L+1)if c%8==u for d in range(-L,L+1)if d%8==h and 3*c*c-2*c*d+3*d*d<=g]
    state=[(n+c+d,e+ee,seq+(c,d))for n,e,seq in state for c,d,ee in opts if e+ee<=g]
   for n,e,seq in state:
    if n==8*a-co and e==g:
     assert (3*co-sum(seq))%8==0
     assert all((3*seq[i]-seq[i^1]-co)%8==0 for i in range(14))
     yield co,seq


# 7-axis types are ordered only for this certificate, not as graph automorphisms.
def verify():
 count=Counter(); total=0
 for v in rootshapes():
  if not ck(v,432) or exactrow(v)>432:continue
  total+=1
  bad=[(a,t)for a,t in ((0,26),(1,21),(-1,21),(3,37),(-3,37))if next(charges(v,27,a,t),None)]
  if bad: count['forbidden']+=1;continue
  labels=set()
  for a in (-2,2):
   for co,cs in charges(v,27,a,34):
    sg=a//2; assert co+sum(cs)==8*a
    rs=[3*co-sum(cs)]+[3*cs[i]-cs[i^1]-co for i in range(14)]
    assert all(not z%8 for z in rs)
    labels.add(tuple(sg*z//8 for z in rs))
  assert labels and all(vec[0]==-1 and max(map(abs,vec))==1 for vec in labels)
  d={vec.count(1) for vec in labels}
  assert (d,len(labels)) in [({5},2),({6},1)]
  count[(min(d),len(labels))]+=1
 assert total==7 and count=={'forbidden':5,(5,2):1,(6,1):1}
 print('verified: seven shapes; five forbidden; two or one normalized true (2,34) marks on remaining types')
if __name__=='__main__':verify()
