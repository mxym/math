"""Exact residual-two-theta checker with central-overlap and pure-cycle cuts."""
from itertools import combinations, permutations, product
from collections import Counter
AX=set(range(7))
pair=lambda i,j:tuple(sorted([i,j]))
def E(paths):
 return [pair(i,j)for p in paths for i,j in zip(p,p[1:])]
def thetas(a,b):
 off=sorted(AX-{a,b});out=[]
 for mids in combinations(off,3):
  p=[[a,m,b]for m in mids];out.append((222,p,frozenset(E(p)),set(),set(),None))
 for i,j,k in permutations(off,3):
  p=[[a,b],[a,i,j,b],[a,k,i,b]]
  out.append((133,p,frozenset(E(p)),set(E(p[1:])),{pair(a,b)},tuple(sorted(AX-set([a,b,i,j,k])))))
 for i,j,k in permutations(off,3):
  for v,w in combinations([u for u in off if u not in (i,k)],2):
   p=[[a,i,j,k,b],[a,v,b],[a,w,b]]
   es=frozenset(E(p));assert len(es)==8
   out.append((422,p,es,set(E(p[:1])),set(),tuple(sorted(AX-{a,b,i,j,k}))))
 return out
def mkcell(X,idx,DG):
 k,ps,es,m,em,u=X
 a,b=ps[0][0],ps[0][-1]
 for p in ps:
  for i,j in zip(p,p[1:]):
   for k,t in [(i,j),(j,i)]:
    key=(idx,k,tuple(p)if k not in (a,b)else ())
    DG.setdefault((pair(i,j),k),key)
 return DG
def diag(A,B,clean):
 paths=A[1]+B[1]; orth=[]
 for i,j in combinations(range(6),2):
  if i//3==j//3:
   if set(paths[i][1:-1])&set(paths[j][1:-1]):orth.append((i,j))
  elif set(paths[i])&set(paths[j]):orth.append((i,j))
 M=[28 if len(p)>=4 else None for p in paths]
 for I,xx in [(0,A),(3,B)]:
  if xx[0]==133:M[I]=56
  V=set(x for x in orth if x[0]//3 == I//3 and x[1]//3==I//3)
  if len(V)>1:return
  if V:
   i,j=next(iter(V));k=next(k for k in range(I,I+3)if k not in (i,j))
   if any(M[x]not in (None,v)for x,v in [(i,28),(j,28),(k,56)]):return
   M[i]=M[j]=28;M[k]=56
 return M
def farcheck(X,DG,allE,mat,empty):
 # with just the split groups, check local degree parity when it is forced.
 if X[0]!=133:return True
 p,q=X[1][1:]
 for z in (p,q):
  F=list(combinations(sorted(AX-set(z)),2))
  for C in F:
   others=[D for D in F if D!=C]
   # exactly degree 0,1,2 as known from internal cell (else undecided).
   if C not in allE: own=[2]
   elif C in mat: own=[1]
   elif C in empty:own=[0]
   else:own=[0,1,2]
   # sum condition odd only on X unused cell.
   want=int(C==X[-1])
   force=[]
   for D in others:
    a=next(iter(set(C)&set(D)))
    if DG.get((C,a)) is None or DG.get((C,a))!=DG.get((D,a)):force.append(0);continue
    K=[e for (e,b),g in DG.items() if b==a and g==DG[C,a]]
    force.append(2 if len(K)==2 else 1)
   if not any((d+e+f)%2==want for d in own
          for e in (list(range(3-d)) if force[0]==1 else [0 if force[0]==0 else 2-d])
          for f in (list(range(3-d)) if force[1]==1 else [0 if force[1]==0 else 2-d])):return False
 return True

ALL=frozenset(combinations(range(7),2))
CYCLES=[]
for S in combinations(range(7),4):
 for a,b,c in permutations(S[1:]):
  if a>c:continue
  sc=(S[0],a,b,c,S[0]);Ecy=frozenset(E([sc]))
  CYCLES.append((sc,Ecy,tuple(sorted(AX-set(S)))))
assert len(CYCLES)==105
def configs(rem, lo=0, cap=2):
 yield []
 if cap==0:return
 for i in range(lo,105):
  C=CYCLES[i]
  if C[1]<=rem:
   for z in configs(rem-C[1],i+1,cap-1):
    yield [C]+z
def check():
 ret=Counter();sample={}
 for A,B in product(thetas(0,1),thetas(2,3)):
  if A[2]&B[2]:continue
  es=A[2]|B[2]; ty=(A[0],B[0])
  if any(X[0]==422 and X[1][0][2] in (X[1][1][1],X[1][2][1]) for X in (A,B)):continue
  rows=diag(A,B,None)
  if rows is None:continue
  mat=A[3]|B[3];empt=A[4]|B[4]
  DG=mkcell(B,1,mkcell(A,0,{}))
  ok=True
  for X in (A,B):
   if X[0]!=422:continue
   z=X[-1]
   if z not in es or z in mat:ok=False;break
   k=next(i for i,p in enumerate(A[1]+B[1])if z in E([p]))
   if rows[k] not in (None,56):ok=False;break
   rows[k]=56;empt.add(z)
  if not ok:continue
  for C in configs(ALL-es):
   EE=es.union(*(x[1]for x in C))
   mm=mat.union(*(x[1]for x in C))
   dd=dict(DG)
   for k,(cy,D,E0) in enumerate(C):
    for e in D:
     for i in e:dd[e,i]=(k+2,i,cy)
   if any(any(e in mm for e in combinations(c[2],2)) or
          sum(e not in EE for e in combinations(c[2],2))>1 for c in C):continue
   bad=False
   for c in C:
    tri=list(combinations(c[2],2))
    if sum(e not in EE for e in tri)!=1:continue
    hits=[e for e in tri if e in EE]
    if all(e in A[2] for e in hits) and A[0]==222:bad=True
    if all(e in B[2] for e in hits) and B[0]==222:bad=True
   if bad:continue
   ret[(ty,len(C),'outer')]+=1
   if all(farcheck(X,dd,EE,mm,empt)for X in (A,B)):
    ret[(ty,len(C),'far')]+=1
    sample.setdefault((ty,len(C)),(A[1],B[1],C,rows))
 expected={
  ((133,133),0,'outer'):228,((133,222),0,'outer'):84,
  ((222,133),0,'outer'):84,((222,222),0,'outer'):19,
  ((222,222),0,'far'):19,
 }
 assert dict(ret)==expected
 for k,v in sorted(ret.items()):print(k,v)
 print("Only 19 ordered 222+222 axis diagrams survive, none with a separate cycle.")

if __name__ == '__main__':
 check()
