from itertools import product,combinations
from random import Random
from math import isqrt
def ck(b,msg):
 if not b:raise ValueError(msg)
def prime(n):return n>1 and all(n%i for i in range(2,isqrt(n)+1))
def run():
 forms=((1,0,0),(0,1,0),(-1,-1,0),(0,0,1),(-1,0,-1))
 ck(all(any(x[i]*y[j]!=x[j]*y[i] for i,j in combinations(range(3),2)) for x,y in combinations(forms,2)),'rank')
 cnt=0
 for l in [2,3,5,7,11,13,17,19]:
  for S,p,q in ([(0,1,1)] if l==2 else product(range(l),repeat=3)):
   r=1;a=next(i for i in range(1,l) if (S-p-r-i)%l);b=next(i for i in range(1,l) if (S-q-r-i)%l)
   ck(all(v%l for v in (r,a,S-p-r-a,b,S-q-r-b)),'local');cnt+=1
 S=600;P=[p for p in range(3,S//4+1,2) if prime(p)];R=[r for r in range(S//5,S//4+1) if prime(r)]
 gl=0
 for p,q in product(P,repeat=2):
  # Expanded positive interval for this SMALL-S witness (the analytic theorem only uses its narrow box asymptotically).
  old=next(((r,a,S-p-r-a,b,S-q-r-b) for r in R for a in P if prime(S-p-r-a) for b in P if prime(S-q-r-b)),None)
  ck(old is not None,'common anchor');r,a,c,b,d=old
  ck(all(prime(x) for x in old) and p+r+a+c==q+r+b+d==S,'fixture');gl+=1
 # Reproduce the hA zero-filling move on random finite lists; use enough genuine labels for every summand total.
 rng=Random(3541);A=[(i-3)//2 for i in range(3,601,2) if prime(i)];small=A[:10]
 def compress(L):
  G=list(L);zeros=0
  while len(G)>=4:
   total=sum(G[:4]);T=next(((a,b,total-a-b) for a in A if a<=total for b in A if a+b<=total and total-a-b in A),None)
   ck(T is not None,'ternary coverage');G=list(T)+G[4:];zeros+=1
  return [0]*zeros+G
 for _ in range(200):
  d=rng.randint(4,15);X=rng.choices(small,k=d);Y=compress(X);ck(len(Y)==d and sum(Y)==sum(X) and Y.count(0)>=d-3,'compression')
 print('local residues',cnt,'all small anchor pairs at weight 600',gl,'200 higher-degree compressions: PASS')
if __name__=='__main__':run()
