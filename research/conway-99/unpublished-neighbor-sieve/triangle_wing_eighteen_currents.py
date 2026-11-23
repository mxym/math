"""Exact centered seven-current visibility in all 18-site triangle-wing components.
Python standard library only. No far labels are enumerated or assumed extendible.
"""
from itertools import permutations,product,combinations
from collections import Counter,defaultdict
def mates(U):
 if not U:yield {};return
 a=U[0]
 for b in U[1:]:
  for f in mates([x for x in U if x not in [a,b]]):yield {a:b,b:a,**f}
M=sorted({tuple(p[i] for i in range(6)) for p in mates(list(range(6)))})
P=M[0];S=list(permutations(range(6)));I=tuple(range(6))
def compose(f,g):return tuple(f[x] for x in g)
def inv(f):return tuple(f.index(i) for i in I)
def conj(g,f):return compose(g,compose(f,inv(g)))
Z=[g for g in S if conj(g,P)==P];named=[]
for q in M:
 for r in M:
  if (q,r)!=min((conj(g,q),conj(g,r)) for g in Z):continue
  z=[g for g in Z if conj(g,q)==q and conj(g,r)==r]
  pi=set(S)
  while pi:
   f=min(pi);orb={conj(g,f) for g in z};pi-=orb;named.append((q,r,f,len(orb)*len(Z)//len(z)))
assert sum(p[-1] for p in named)==162000
assert len(named)==3802
def blocks(q,r,f):
 N=[set() for i in range(18)]
 for i in I:
  for a,b in [(i,P[i]),(i+6,6+q[i]),(12+i,12+r[i]),(i,6+i),(6+i,12+i),(12+i,f[i])]:
   N[a].add(b);N[b].add(a)
 return N
def conn(g):
 F=[0];S={0}
 while F:i=F.pop();t=g[i]-S;S|=t;F+=list(t)
 return len(S)==len(g)
def kval(G):
 A=[[3*(i==j)-int(j in G[i]) for j in range(18)] for i in range(18)]+[[1]*18]
 return kernel(A)
def signature(g,h,m):
 for i in range(18):
  c=Counter()
  for j in range(18):
   if i!=j:c[h[j]]+=m[i][j]
  for b in range(7):
   k=(-h[i]-b)%7
   if c[k]!=c[b] or k==b and c[b]%2:return False
 return True
def kernel(a):
    A=[[v%7 for v in r] for r in a];m=len(A);n=len(A[0]);piv=[]
    for j in range(n):
        t=len(piv);r=next((i for i in range(t,m) if A[i][j]),None)
        if r is None:continue
        A[t],A[r]=A[r],A[t];inv=pow(A[t][j],-1,7)
        A[t]=[v*inv%7 for v in A[t]]
        for i in range(m):
            if i!=t:
                q=A[i][j];A[i]=[(v-q*u)%7 for v,u in zip(A[i],A[t])]
        piv.append(j)
    B=[]
    for f in sorted(set(range(n))-set(piv)):
        x=[0]*n;x[f]=1
        for i,j in enumerate(piv):x[j]=-A[i][f]%7
        B.append(tuple(x))
    return B



def rank_sign(a):
    A=[[v%7 for v in r] for r in a];rank=0;det=1
    while any(any(r) for r in A):
        n=len(A);j=next((i for i in range(n) if A[i][i]),None)
        if j is None:
            i,j=next((i,j) for i,j in combinations(range(n),2) if A[i][j])
            A[i]=[(v+w)%7 for v,w in zip(A[i],A[j])]
            for k in range(n):A[k][i]=(A[k][i]+A[k][j])%7
            j=i
        A[0],A[j]=A[j],A[0]
        for r in A:r[0],r[j]=r[j],r[0]
        d=A[0][0];rank+=1;det=det*d%7;di=pow(d,-1,7)
        A=[[(A[i][j]-A[i][0]*di*A[0][j])%7 for j in range(1,n)] for i in range(1,n)]
    return rank,(1 if det in (1,2,4) else -1)



def canon(p):
 G=blocks(*p);mkeys=[]
 for a,b,c in permutations(range(3)):
  ids=[i for i in range(6*a,6*a+6)];mate=tuple(next(j%6 for j in G[i] if j//6==a) for i in ids)
  pfix=next(g for g in S if conj(g,mate)==P);order=tuple(ids[x] for x in inv(pfix));snd=tuple(next(v for v in G[i] if v//6==b) for i in order);th=tuple(next(v for v in G[i] if v//6==c) for i in snd)
  q=tuple(snd.index(next(w for w in G[i] if w//6==b)) for i in snd)
  r=tuple(th.index(next(w for w in G[i] if w//6==c)) for i in th)
  f=tuple(order.index(next(w for w in G[i] if w//6==a)) for i in th)
  mkeys.append(min((conj(x,q),conj(x,r),conj(x,f)) for x in Z))
 return min(mkeys)

C=[];out=Counter();named_dim=Counter();lines_tested=0
for q,r,f,orb in named:
 G=blocks(q,r,f)
 if not conn(G):continue
 m=[[0 if j==i else 2-int(j in G[i])-len(G[i]&G[j])-int(i//6==j//6) for j in range(18)] for i in range(18)]
 if min(min(row) for row in m)<0:continue
 assert [sum(row) for row in m]==[20]*18
 K=kval(G);d=len(K);named_dim[d]+=1
 # Choose first nonzero BASIS coefficient equal to one. Rows of K independent.
 for n in range(d):
  for suffix in product(range(7),repeat=d-1-n):
   coeff=(0,)*n+(1,)+suffix
   h=tuple(sum(z*v[j] for z,v in zip(coeff,K))%7 for j in range(18))
   lines_tested+=1
   assert not signature(G,h,m)
 if (q,r,f)!=canon((q,r,f)):continue
 L=[[3*int(i==j)-int(j in G[i]) for j in range(18)] for i in range(18)]
 rank,sign=rank_sign([[L[i][j]-L[i][-1]-L[-1][j]+L[-1][-1] for j in range(17)] for i in range(17)])
 assert rank+d==17
 C.append((d,sign));out[d,sign]+=1
assert named_dim=={0:1957,1:410,2:45,3:1} and lines_tested==827
assert out=={(0,1):259,(0,-1):184,(1,1):42,(1,-1):62,(2,1):1,(2,-1):14,(3,1):1}
from itertools import combinations_with_replacement
cuts=Counter()
for (d,p),(e,q) in combinations_with_replacement(C,2):
 s=max(d,e);rank=35-d-e+2*s
 if rank>36 or (rank==36 and p*q*(-1)**s!=-1):
  cuts[tuple(sorted((d,e)))]+=1
assert sum(cuts.values())==31902 and len(C)*(len(C)+1)//2==158766
print("All",lines_tested,"named projective currents detected;",len(C),"unlabelled component types.")
print("Rank 36 cuts",sum(cuts.values()),"out of 158766 unlabelled 18+18 pairs:",dict(cuts))
