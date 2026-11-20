if not __debug__:
    raise RuntimeError("Run without python -O; proof assertions must remain enabled.")

from itertools import product,combinations
from pathlib import Path
import json
def run(code,R):
 E=list(combinations(range(7),2));D=[]
 for j in range(7):
  for i in range(j):
   z=code>>(j*(j-1)+2*i)&3
   if z:D.append((i,j)if z==1 else(j,i))
 d=len(D);tree=[[]for _ in range(14)];cy=[];ch=[];cells=[E.index(tuple(sorted(y)))for y in D]
 for j,(a,b)in enumerate(D):
  b+=7;p={a:(a,-1)};L=[a]
  for u in L:
   for v,i in tree[u]:
    if v not in p:p[v]=(u,i);L.append(v)
  if b not in p:tree[a].append((b,j));tree[b].append((a,j));continue
  z=[0]*d;z[j]=1;sg=-1
  while b!=a:b,k=p[b];z[k]=sg;sg=-sg
  cy.append(z);ch.append(cells[j])
 k=len(ch);notch=[i for i in range(21)if i not in ch];dis=[(h,f)for f in range(21)for h in range(f)if not set(E[h])&set(E[f])];assert len(dis)==105
 rows=[]
 for h,e in enumerate(E):
  jd=cells.index(h)if h in cells else -1;folder=[]
  for t in product(range(-1,2),repeat=k):
   w=[sum(a[j]*s for a,s in zip(cy,t))for j in range(d)]
   if max(map(abs,w))>1:continue
   ok=True
   for j,g in enumerate(D):
    if not set(e)&set(g):continue
    if j==jd:ok&=w[j]==-1
    elif jd>=0 and(g[0]==D[jd][0]or g[1]==D[jd][1]):ok&=w[j]>=0
    else:ok&=w[j]==0
   if not ok:continue
   A=[t[i]*((h==p)-(cy[ch.index(h)][cells.index(p)]if h in ch and p in cells else 0))for i in range(k)for p in notch]
   A.extend((t[i]+7*(h==ch[i]))*t[j]for i in range(k)for j in range(k))
   dg=[2*(h==f)+int(not set(e)&set(g))+(w[cells.index(f)]if f in cells else 0)for f,g in enumerate(E)]
   pr=[(1 if jd>=0 else 2)if f==h else (w[cells.index(f)]if jd>=0 and f in cells and D[jd][1]==D[cells.index(f)][1]else 0)for f in range(21)]
   Q=[((h==i)+pr[i])*dg[j]+pr[j]*dg[i]for i,j in dis];folder.append((A,Q,w))
  assert folder;rows.append(folder)
 cs=R[0];S0,up,ap,claimed=R[1]
 def obj(tag,w,Q,h):
  if tag[0]=='Q':return Q[tag[1]]
  assert tag[0]=='M';i,j=tag[1:];return (h==cells[j])*w[i]
 for idx,rec in enumerate(cs+[None]):
  final=rec is None
  if final:S,u,a,lo=S0,up,ap,claimed;targets=[16]*105+[r[2]for r in cs]
  else:tag,sg,b,S,u,a,lo=rec;targets=[16]*105
  assert S>0 and all(0<=j<len(targets)and v>=0 for j,v in a)
  val=sum(targets[j]*v for j,v in a)
  for h,fold in enumerate(rows):
   vv=[]
   for A,Q,w in fold:
    q=Q+([r[1]*obj(r[0],w,Q,h)for r in cs]if final else [])
    cost=0 if final else sg*obj(tag,w,Q,h);vv.append(S*cost-sum(A[j]*v for j,v in u)-sum(q[j]*v for j,v in a))
   val+=4*min(vv)
  assert val==lo and (lo>0 if final else lo>(b-1)*S)
 print(code,len(cs),'integer cuts; final contradiction numerator',claimed,'/',S0)
if __name__=='__main__':
 data=json.loads(Path(__file__).with_name('integer.json').read_text());assert set(data)=={'42991782400','45141371392'}
 for code,r in data.items():run(int(code),r)
