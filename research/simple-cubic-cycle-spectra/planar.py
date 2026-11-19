"""Find a genus-zero rotation or a literal subgraph subdividing K3,3.
The fast parity search is only a certificate finder; both outcomes are verified."""
from itertools import combinations
def need(x):
 if not x:raise ValueError("invalid certificate")
def rotation(n,E):
 adj=[[] for _ in range(n)]
 for u,v in E:adj[u].append(v);adj[v].append(u)
 for ns in adj:ns.sort()
 roots=[];seen=set();tree=set()
 for u in range(n):
  if u in seen:continue
  roots.append(u);seen.add(u);todo=[u]
  while todo:
   a=todo.pop()
   for b in adj[a]:
    if b not in seen:seen.add(b);todo.append(b);tree.add(tuple(sorted((a,b))))
 old=sorted(set(E)-tree)
 pairs=list(combinations(range(len(old)),2))
 # Enlarge the spanning forest with distinct leaves for both ends of every chord.
 T=[list(ns) for ns in adj]
 for i,(u,v) in enumerate(old):
  x=n+2*i;y=x+1;T[u][T[u].index(v)]=x;T[v][T[v].index(u)]=y;T.extend([[u],[v]])
 def crossing(flip):
  pos={};ind=0
  def go(v,p):
   nonlocal ind
   if v>=n:pos[v]=ind;ind+=1;return
   ns=T[v][::(-1 if flip>>v&1 else 1)]
   if p in ns:
    j=ns.index(p);ns=ns[j+1:]+ns[:j]
   for w in ns:go(w,v)
  for v in roots:go(v,-1)
  res=0
  for j,(i,h) in enumerate(pairs):
   a,b=sorted((pos[n+2*i],pos[n+2*i+1]));c,d=pos[n+2*h],pos[n+2*h+1]
   if (a<c<b)!=(a<d<b):res|=1<<j
  return res
 base=crossing(0)
 cols=[crossing(1<<i)^base if len(adj[i])==3 else 0 for i in range(n)]
 # Solve sum cols[i]*x_i=base, returning a mask of rotations.
 piv={}
 for i,col in enumerate(cols):
  coeff=1<<i
  while col:
   j=col.bit_length()-1
   if j not in piv:piv[j]=(col,coeff);break
   a,b=piv[j];col^=a;coeff^=b
 word=0
 while base:
  j=base.bit_length()-1
  if j not in piv:return None
  a,b=piv[j];base^=a;word^=b
 return [tuple(ns[::-1] if word>>i&1 else ns) for i,ns in enumerate(adj)]
def sphere(n,E,rot):
 # Connected, edge-containing graph. Verify by walking directed edge-sides.
 need(len(rot)==n and all(set(ns)=={v if u==i else u for u,v in E if i in (u,v)} and len(set(ns))==len(ns) for i,ns in enumerate(rot)))
 darts={(u,v) for u in range(n) for v in rot[u]};faces=0
 while darts:
  a,b=next(iter(darts));faces+=1
  while (a,b) in darts:
   darts.remove((a,b));ns=rot[b];a,b=b,ns[(ns.index(a)+1)%len(ns)]
 need(n-len(E)+faces==2)
def k33(n,F):
 adj=[set() for _ in range(n)]
 for u,v in F:adj[u].add(v);adj[v].add(u)
 s={i for i in range(n) if len(adj[i])==3}
 need(len(s)==6 and all(len(ns) in (0,2,3) for ns in adj))
 red={i:set() for i in s}; used=set()
 for i in s:
  for j in adj[i]:
   a,b=i,j; ed=tuple(sorted((a,b)))
   if ed in used:continue
   used.add(ed)
   while b not in s:
    c,=adj[b]-{a};a,b=b,c;ed=tuple(sorted((a,b)));need(ed not in used);used.add(ed)
   need(b!=i and b not in red[i]);red[i].add(b);red[b].add(i)
 need(used==set(F))
 side=red[next(iter(s))]
 need(len(side)==3 and all(red[i]==s-side for i in side) and all(red[i]==side for i in s-side))
def certificate(n,E):
 rot=rotation(n,E)
 if rot is not None:
  sphere(n,E,rot);return ('P',rot)
 F=E[:]
 for e in E:
  f=[v for v in F if v!=e]
  if rotation(n,f) is None:F=f
 k33(n,F);return ('N',F)
def readrows():
 ans=[]
 for ln in open('simple.txt'):
  n,k,*E=ln.split();E=sorted(tuple(sorted(map(int,e.split(',')))) for e in E)
  ans.append((int(n),int(k),E))
 return ans
if __name__=='__main__':
 import json,collections
 records=[];s=set();freq=collections.Counter()
 for n,k,E in readrows():
  typ,cert=certificate(n,E);freq[(n,typ)]+=1
  records.append(dict(n=n,k=k,edges=E,type=typ,certificate=cert))
  if typ=='P':s.add(k)
 print("planar/nonplanar by order:",sorted(freq.items()))
 print("missing planar:",*[i for i in range(1,132) if i not in s])
 with open('labeled.json','w') as f:json.dump(records,f,separators=(',',':'))
