from itertools import product
from math import isqrt
from functools import lru_cache
from collections import Counter
def ck(b,msg):
 if not b:raise ValueError(msg)
@lru_cache(None)
def prime(x):return x>1 and all(x%i for i in range(2,isqrt(x)+1))
def checkmoves(L,A):
 for st in L:ck(all(x in A for x in st),'outside support')
 for a,b in zip(L,L[1:]):
  x=Counter(a)-Counter(b);y=Counter(b)-Counter(a)
  ck(sum(x.values())==sum(y.values()) and sum(x.values()) in [0,2] and sum(x.elements())==sum(y.elements()),'not a move')
def vals(s,t,q,a,b,y,w):
 c=s-a-b;v=t+a-y;h=y+b-q;z=q+c-w;r=a-y+w
 return (c,v,h,z,r),((t,a,b,c),(y,v,b,c),(q,h,v,c),(w,z,h,v),(t,r,h,z))
def special(s,q,a,b,p,f):
 c=s-a-b;v=q+a-p;h=b+p-f;d=f+c-q
 return (c,v,h,d),((q,a,b,c),(p,v,b,c),(h,v,f,c),(q,h,v,d))
def run():
 n9=nL=0
 for u,q in ((1,19),(2,11),(4,13),(5,5),(7,7),(8,17)):
  ck(prime(q) and q%9==u,'pivot')
  e,d=(u+3)%9,(u-3)%9;s0=1500000;s=next(n for n in range(s0,s0+20) if n%9==(3*u)%9 and n%2)
  N=s-q; A={n for n in range(3,s+1,2) if n%9 in (e,d) and prime(n)}|{q}
  ck(all((x+y+z)%9!=s%9 or x==y==z for x,y,z in product((e,d),repeat=3)),'mixed cubic')
  for tt in (e,d):
   out,ss=vals(s,tt,q,e,e,e,d)
   ck(tuple(x%9 for x in out)==(e,tt,d,d,d),'mod nine')
   n9+=1
  out,ss=special(s,q,e,e,d,e);ck(tuple(x%9 for x in out)==(e,d,d,d),'pivot mod nine')
  for p in [2,5,7,11,13,17,19,23]:
   for si in ([1] if p==2 else range(p)):
    for t in ([1] if p==2 else range(p)):
     if p==2:a=b=y=w=1
     else:
      a=1;b=next(i for i in range(1,p) if (si-a-i)%p);c=si-a-b
      y=next(i for i in range(1,p) if (t+a-i)%p and (i+b-q)%p)
      w=next(i for i in range(1,p) if (q+c-i)%p and (a-y+i)%p)
     out,_=vals(si,t,q,a,b,y,w);ck(all(x%p for x in out),'local');nL+=1
     if p==2:a=b=y=w=1
     else:
      a=1;b=next(i for i in range(1,p) if (si-a-i)%p);c=si-a-b
      y=next(i for i in range(1,p) if (q+a-i)%p)
      w=next(i for i in range(1,p) if (b+y-i)%p and (i+c-q)%p)
     out,_=special(si,q,a,b,y,w);ck(all(x%p for x in out),'local pivot')
  tests=[(q,(450,275,225,275),(e,e,d,e))]
  for sign in [e,d]:
   tests.extend([(min(i for i in A if i%9==sign),(400,280,200,160),(e,e,e,d)),
       (max(i for i in A if i%9==sign),(320,160,420,260),(e,e,e,d))])
  for t,cs,rs in tests:
   C=[[i for i in range((c-1)*s//1000+1,(c+1)*s//1000) if i in A and i%9==r] for c,r in zip(cs,rs)]
   found=False
   for a,b,y,w in product(*C):
    vs,path=special(s,q,a,b,y,w) if t==q else vals(s,t,q,a,b,y,w)
    if all(o in A for o in vs):
     checkmoves(path,A);found=True;break
   ck(found,('missing literal chart',u,t))
  print('u,q,N,s',u,q,N,s,'all 5 literal prime charts pass')
 print('mod9 patterns',n9,'fixed-pivot local states',nL,'30 prime chart paths: PASS')
if __name__=='__main__':run()
