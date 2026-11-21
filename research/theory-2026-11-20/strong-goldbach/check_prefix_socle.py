from itertools import product,combinations
from math import isqrt
from collections import Counter
def ck(b,m):
 if not b: raise ValueError(m)
def prime(n):return n>=2 and all(n%i for i in range(2,isqrt(n)+1))
def chart(s,t,a,b,u,w):
 c=s-a-b;v=t+a-u;h=u+b-3;z=3+c-w;r=a-u+w
 return (a,b,u,w,c,v,h,z,r),[(t,a,b,c),(u,v,b,c),(3,h,v,c),(w,z,h,v),(t,r,h,z)]
def exchanges(states):
 for x,y in zip(states,states[1:]):
  a=Counter(x)-Counter(y);b=Counter(y)-Counter(x)
  ck(sum(a.values()) in [0,2] and sum(a.values())==sum(b.values()) and sum(a.elements())==sum(b.elements()),'not a move')
def run():
 forms=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(-1,-1,0,0),(1,0,-1,0),(0,1,1,0),(-1,-1,0,-1),(1,0,-1,1)]
 ck(all(any(v[i]*w[j]!=v[j]*w[i] for i,j in combinations(range(4),2)) for v,w in combinations(forms,2)),'parallel')
 nloc=0
 for p in [2,3]+[q for q in range(5,80,2) if prime(q)]:
  for s in ([1] if p==2 else [0] if p==3 else range(p)):
   for t in ([1] if p==2 else [1,2] if p==3 else range(p)):
    if p<=3:a=b=u=1;w=1 if p==2 else 2
    else:
     a=1;b=next(i for i in range(1,p) if (s-a-i)%p);c=s-a-b
     u=next(i for i in range(1,p) if (t+a-i)%p and (i+b-3)%p)
     w=next(i for i in range(1,p) if (3+c-i)%p and (a-u+i)%p)
    vals,_=chart(s,t,a,b,u,w);ck(all(q%p for q in vals),'bad local')
    nloc+=1
 for center,limits in [((400,280,200,160),(0,750)),((320,160,420,260),(750,1000))]:
  for t in limits:
   for err in product((-1,1),repeat=4):
    a,b,u,w=(x+y for x,y in zip(center,err))
    # Balanced units 1/1000 of s. s>=3000 gives 0 <= 3/s*1000 <= 1.
    for sh in (0,1):
     c=1000-a-b;v=t+a-u;h=u+b-sh;z=sh+c-w;r=a-u+w
     ck(min(a,b,c,v,h,z,r,u,w)>=150 and max(a,b,c,v,h,z,r,u,w)<=960,'positivity/cutoff')
     ck(min(a,b,c,h,z,r)>=125 and max(a,b,c,h,z,r)<=625,'centrality')
 # Literal genuine paths (different t-bands; chart inputs near specified boxes are not needed for this control).
 for s,t,A in [(10005,5,(4000,2800,2000,1600)),(10005,9973,(3200,1600,4200,2600))]:
  ck(prime(t),'bad fixed catalyst')
  C=[[i for i in range(a-100,a+101) if prime(i) and i%3==r] for a,r in zip(A,(1,1,1,2))]
  found=None
  for a,b,u,w in product(*C):
   labels,states=chart(s,t,a,b,u,w)
   if all(prime(x) and x<=s for x in labels):
    exchanges(states);found=states;break
  ck(found is not None,'literal chart missing');print('literal',s,t,found)
 print('local residues',nloc,'two-band box corners, move identities, 9 nonparallel forms: PASS')
if __name__=='__main__':run()
