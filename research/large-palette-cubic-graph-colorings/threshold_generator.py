"""Exact lower-bound ledger and endpoint certificate; use Python 3.10+ without -O."""
from blocks import K, Q, maskgraph, gen, edges, subgraph_data, hascycle, sweight

def host(kind):
 if kind=='H':
  return maskgraph(14,[(i,7+(i+s)%7) for i in range(7) for s in (0,1,3)])
 return maskgraph(10,[(i,(i+1)%5) for i in range(5)]+[(i+5,5+(i+2)%5) for i in range(5)]+[(i,i+5) for i in range(5)])
def inj(a,H):
 n=len(a);h=len(H);order=[]
 while len(order)<n:
  u=max((u for u in range(n) if u not in order),key=lambda u:(sum(a[u]>>v&1 for v in order),a[u].bit_count()));order.append(u)
 def go(i,used,p):
  if i==n:return 1
  u=order[i];ops=((1<<h)-1)&~used
  for j,v in enumerate(order[:i]):
   if a[u]>>v&1:ops&=H[p[j]]
  ct=0
  while ops:
   y=ops&-ops;ops^=y;ct+=go(i+1,used|y,p+[y.bit_length()-1])
  return ct
 return go(0,0,[])
def rows(kind):
 g=5 if kind=='P' else 6; sign=(-1)**g;X=[4] if g==5 else [3,5]
 f=gen(kind); w={}; const=[Q(0)]*(K+1); ledger={l:[Q(0)]*(K+1) for l in X};H=host(kind)
 for key,(a,aut) in sorted(f.items(),key=lambda v:len(edges(v[1][0]))):
  n=len(a);m=len(edges(a));p,subs=subgraph_data(a);d=[Q(0)]*(K+1)
  for k in range(1,K+1):
   d[k]=Q(k*p[k]-sum(j*d[j]*p[k-j] for j in range(1,k)),k)
  for k in range(1,K+1):
   d[k]+=Q(m,k);d[k]-=sum(v*w[h][k] for h,v in subs.items())
  assert all(x==0 for x in d[:n-1]) and d[n-1]==(-1)**m
  w[key]=d
  bl=next((l for l in X if hascycle(a,l)),0)
  if bl:
   if n==m==bl:
    for k in range(K+1): ledger[bl][k]+=-sign*d[k]
   else:
    lim=Q(2*bl*2**(n-bl),aut)
    for k in range(K+1):ledger[bl][k]-=max(0,sign*d[k])*lim
  elif n==m==g:
   assert sign*d[g-1]==1 and all(q*sign>=0 for q in d[g:])
   const[g-1]+=Q(1,g)
   if g==5:ledger[4][4]-=2
  else:
   hm=Q(inj(a,H),aut*len(H));lim=Q(sweight(a),aut)
   assert hm<=lim
   for k in range(K+1):const[k]+=sign*d[k]*hm-max(0,sign*d[k])*lim
 return const,ledger,len(w)
for kind in 'PH':
 c,L,size=rows(kind);g=5 if kind=='P' else 6
 print('kind',kind,'size',size,'K',K,'const',' '.join(str(x) for x in c),'ledger',{j:[str(x) for x in l] for j,l in L.items()},flush=True)
 for q in range(8,300000):
  z=Q(1,q)
  def low(l,d):
   return l[d]+sum(min(0,l[i])*z**(i-d) for i in range(d+1,K+1))
  tail=Q(2*7**(K+1),K+1)*z**(K-g+2)/(1-7*z)
  if low(c,g-1)>tail and all(low(l,j-1)>=0 for j,l in L.items()):
   print('q>=',q,'base lower scaled',float(low(c,g-1)),'tail scaled',float(tail),flush=True);break
