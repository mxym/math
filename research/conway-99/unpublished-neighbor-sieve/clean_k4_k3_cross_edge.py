"""Exact standard-library certificate: disjoint clean K4 and K3 allow at most one cross edge.
No assumptions enter about any of the nine unmarked axis cells or the Seidel rank.
Packet labels index the four vertices of each K4 cell by its complementary contacts;
the independent signed-parent labeling of those vertices is enumerated separately.
See clean-k4-k3-cross-edge.md for the coverage and meanings of the tests.
"""
from itertools import product, combinations, permutations
from collections import Counter
F=list(product(range(2),repeat=2))
# A=(x,y), B=(x,z), C=(y,z)
def ff(V,W,axis1,axis2):return int(V[axis1]!=W[axis2])+1
L=[]
for ax,A in enumerate(F):
 rows=[ff(A,B,0,0) for B in F];cols=[ff(A,C,1,0) for C in F];L.append([])
 for Bc in product(*[list(combinations(range(4),n)) for n in rows]):
  if [sum(i in a for a in Bc) for i in range(4)]!=cols:continue
  L[-1].append(sum(1<<(4*j+k) for j,c in enumerate(Bc) for k in c))
print('layers',list(map(len,L)))
U=sum(1<<(4*i+j) for i,B in enumerate(F) for j,C in enumerate(F) if B[1]!=C[1]);mask=(1<<16)-1; lookup=set(L[3])
def arraygen():
 for a,b,c in product(*L[:3]):
  if a&b&c or (a&b|a&c|b&c)&~U:continue
  d= ((a^b^c)^~U)&mask
  if d in lookup:yield a,b,c,d

E=list(combinations(range(4),2))
PERM=tuple(permutations(range(4)))
ALL=tuple(range(4))
def decomp(U):
 F=[I for I in combinations(range(24),4) if all(len({U[i][k] for i in I})==4 for k in range(3))]
 B=[(sum(1<<i for i in I),I)for I in F]
 IB=[[p for p in B if p[0]>>j&1]for j in range(24)]
 def rec(msk,D):
  if not msk:yield D;return
  j=(msk&-msk).bit_length()-1
  for P,X in IB[j]:
   if P&msk==P:yield from rec(msk^P,D+(X,))
 return rec((1<<24)-1,())

def extend(D,R,DiagOK):
 # Center chosen after fixing the four-axis gauge.
 A=tuple(PERM[d] for d in R)
 Es=E+[(a+4,b+4)for a,b in ex]
 def adj(Q,x,y):Q[x]|=1<<y;Q[y]|=1<<x
 base=[0]*51
 for axis in range(7):
  adj(base,50,36+2*axis);adj(base,50,37+2*axis);adj(base,36+2*axis,37+2*axis)
 for j,(a,b) in enumerate(Es):
  for i in ALL:
   u=A[j][i]if j<6 else i
   adj(base,4*j+i,36+2*a+F[u][0]);adj(base,4*j+i,36+2*b+F[u][1])
   for v in range(i+1,4):
    vv=A[j][v]if j<6 else v
    if (u^vv)in(1,2):adj(base,4*j+i,4*j+v)
 for e in range(6):
  for i in ALL:
   for j,t in enumerate(D[e][i]):adj(base,4*e+i,24+4*j+t)
 def okay(G):
  return all((G[i]&G[j]).bit_count()<=2-(G[i]>>j&1)for i,j in combinations(range(len(G)),2))
 assert okay(base)
 pairL=[(e,f)for e,f in combinations(range(6),2)if not set(E[e])&set(E[f])]
 def Di(p):return p.index(3^p[0])
 opts=[DiagOK[e,f,Di(A[e]),Di(A[f])]for e,f in pairL]
 assert all(opts)
 def Min(axis,p,t):
  h=sum(F[A[e][next(i for i,v in enumerate(D[e])if v[p]==t)]][E[e].index(axis)]for e in range(6)if axis in E[e])
  assert h in (1,2)
  return 2-h
 def add_extra(G,axes):
  i,j=axes; pp=next(v for v in range(3)if j-4 not in ex[v]);p0=24+4*pp
  targets=[4*e for e in range(6) if i not in E[e]]
  for ji in product(range(2),repeat=2):
   J=[ji[0],ji[1]]
   R=[];seen=[0,0]
   for t in ALL:
    ni=Min(i,pp,t); nj=J[ni]^seen[ni];seen[ni]^=1
    R.append((36+2*i+ni,36+2*j+nj,p0+t,2*ni+nj))
   assert len({x[-1] for x in R})==4
   def possible(i0):
    v=R[i0][:-1]
    def run(z,u):
     if z==len(targets):yield u;return
     for d in ALL:
      y=targets[z]+d
      if all((G[x]&G[y]).bit_count()<2-(G[x]>>y&1)for x in v+u):
       yield from run(z+1,u+(y,))
    # The fixed root-parent and peripheral-word incidences also consume old-old caps.
    if all((G[x]&G[y]).bit_count()<2-(G[x]>>y&1)for x,y in combinations(v,2)):
     yield from run(0,())
   O=[tuple(possible(k))for k in ALL]
   if not all(O):continue
   ss=tuple(sorted(ALL,key=lambda k:len(O[k])))
   def fill(L,mask,S):
    if L==4:
     n=len(G);H=G.copy()+[0]*4
     for shi,row in zip(ss,S):
      v=n+shi
      for x in R[shi][:-1]+row:adj(H,v,x)
      for w in range(shi+1,4):
       if (R[shi][-1]^R[w][-1])in(1,2):adj(H,v,n+w)
     if okay(H):yield H
     return
    for row in O[ss[L]]:
     m=sum(1<<x for x in row)
     if m&mask:continue
     yield from fill(L+1,mask|m,S+(row,))
   yield from fill(0,0,())
 for P in product(*opts):
  COUNTS['validated-51-site-chart'] += 1
  Q=base.copy()
  for (i,j),p in zip(pairL,P):
   for x in ALL:adj(Q,4*i+x,4*j+p[x])
  assert okay(Q)
  # Test each possible cross axis individually. A common underlying graph
  # would have to pass both individual tests on this one fixed chart.
  L=[e for e in product(range(4),range(4,7)) if next(add_extra(Q,e),None) is not None]
  COUNTS['eligible number '+str(len(L))]+=1
  assert len(L)<=1,(D,R,P,L)
 return False
def check(S):
 first=S[0]
 DIA=((0,3,1,2),(0,1,3,2),(0,1,2,3))
 DIDX=tuple(DIA[P.index(3^P[0])-1]for P in PERM)
 # Gauge: packet on axis pair AB fixed; its internal labeling r remains free apart from independent axis flips.
 for js in permutations(range(1,6)):
  D=(first,)+tuple(S[j] for j in js)
  # Gauge swap A/B and C/D and other edge labels preserving edge AB.
  if js[0]>js[1] or js[0]>js[2] or js[0]>js[3]:continue
  Q={};DiagOK={}
  for i,j in combinations(range(6),2):
   Fij=tuple(tuple(sum(x==y for x,y in zip(X,Y)) for Y in D[j]) for X in D[i])
   M=set(E[i])&set(E[j])
   if M:
    ot,=M; k=E[i].index(ot); l=E[j].index(ot)
    L=[(x,y)for x,y in product(ALL,repeat=2)if Fij[x][y]==2]
    Q[i,j]=[tuple(jj for jj,B in enumerate(PERM) if all(F[A[x]][k]!=F[B[y]][l]for x,y in L))for A in PERM]
   else:
    # Need only each cell's diagonal matching (colour sign-flip orientation irrelevant).
    cache={}
    for A in DIA:
     for B in DIA:
      ok=[]
      for P in PERM:
       inv=[P.index(x)for x in ALL]
       if not all((Fij[x][y]<=1 if P[x]==y else Fij[x][y]+int((B[y]^B[P[x]]) in (1,2))+int((A[x]^A[inv[y]]) in (1,2))<=2)for x,y in product(ALL,repeat=2)):continue
       def paircheck(U,V,L,S):
        for k in range(3):
         seq=[x[k]for x in U]
         for x in ALL:
          y=V[S[x]][k]
          if y==seq[x]:continue
          z=seq.index(y)
          if (y^seq[x])in(1,2) and (L[x]^L[z])in(1,2):return False
        return True
       if paircheck(D[i],D[j],A,P) and paircheck(D[j],D[i],B,inv):
        ok.append(P)
      cache[A,B]=tuple(ok)
      DiagOK[i,j,A.index(3),B.index(3)]=tuple(ok)
    Q[i,j]=[tuple(jj for jj,Bc in enumerate(DIDX) if cache[Ac,Bc])for Ac in DIDX]
  bulk={(s):[{(z,k,t):F[A[next(m for m,V in enumerate(D[s])if V[k]==t)]][l]for l,z in enumerate(E[s])for k,t in product(range(3),range(4))}for A in PERM]for s in range(6)}
  def CSP(L):
   i=len(L)
   if i==6:return L if extend(D,L,DiagOK) else None
   for v in range(24):
    if i==0 and PERM[v][0]!=0:continue
    if any(v not in Q[j,i][w] for j,w in enumerate(L)):continue
    W=L+(v,)
    bad=False
    for z in range(4):
     I=[s for s,e in enumerate(E) if z in e]
     if I[-1]>i:continue
     for k in range(3):
      mm=0
      for t in range(4):
       H=sum(bulk[s][W[s]][z,k,t]for s in I)
       if H not in (1,2):bad=True;break
       mm+=H==1
      if bad or mm!=2:bad=True;break
     if bad:break
    if bad:continue
    sol=CSP(W)
    if sol is not None:return sol
  R=CSP(())
  if R is not None:return D,R
 return None
ex=list(combinations(range(3),2))
def norm(T):
 vv=tuple(T);Rt=[]
 for order in permutations(range(3)):
  for sig in product(range(2),repeat=3):
   W=[]
   for u in vv:
    Im=[None]*3
    for d,e in enumerate(ex):
     dst=tuple(sorted(order[a]for a in e))
     z={order[a]:F[u[d]][i]^sig[order[a]]for i,a in enumerate(e)}
     Im[ex.index(dst)]=F.index(tuple(z[b]for b in dst))
    W.append(tuple(Im))
   Rt.append(tuple(sorted(W)))
 return min(Rt)

seen=set();cnt=Counter();COUNTS=Counter()
for packed in arraygen():
 cnt['raw tensors'] += 1
 us=tuple((i,j,k)for i in range(4)for j in range(4)for k in range(4)if packed[i]>>(4*j+k)&1)
 assert len(us)==24
 for i,j in combinations(range(3),2):
  t,=set(ex[i])&set(ex[j]); u,v=ex[i].index(t),ex[j].index(t)
  S=Counter((w[i],w[j])for w in us)
  assert all(S[a,b]==1+(F[a][u]!=F[b][v])for a,b in product(ALL,repeat=2))
 w=norm(us)
 if w in seen:continue
 seen.add(w)
 for D in decomp(w):
  cnt['partition']+=1
  S=tuple(tuple(w[i]for i in x)for x in D)
  R=check(S)
  if R is not None:
   print('PASS', cnt,R);raise SystemExit
 cnt['tried']+=1
assert cnt=={'raw tensors':816,'partition':106,'tried':34}
assert COUNTS=={'validated-51-site-chart':768,'eligible number 0':576,'eligible number 1':192}
print(dict(cnt),dict(COUNTS))
