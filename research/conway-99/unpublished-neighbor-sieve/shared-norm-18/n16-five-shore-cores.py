from itertools import combinations,permutations,product
from collections import Counter
def decks(ds):
 e=[[0]*8 for _ in range(8)];i=0
 for l in ds:
  for j in range(l):
   x,y=i+j,i+(j+1)%l;e[x][y]+=1;e[y][x]+=1
  i+=l
 return e
def mats(ds):
 d=decks(ds);lines=[]
 def go(i,C):
  if i==8:
   W=tuple(sorted(v for v,n in C.items()for _ in range(n)))
   if all((x&y).bit_count()<=2 for x,y in combinations(W,2)):lines.append(W)
   return
  for h in product(*(range(q+1)for q in C.values())):
   if sum(h)!=4:continue
   if any(sum(z for z,c in zip(h,C)if c>>j&1)!=2-d[i][j] for j in range(i)):continue
   D={}
   for (w,k),t in zip(C.items(),h):
    if (w.bit_count()+8-i-1<4 and k!=t)or (w.bit_count()==4 and t):break
    if k-t:D[w]=k-t
    if t:D[w+(1<<i)]=t
   else:go(i+1,D)
 go(0,{0:8})
 G=[p for p in permutations(range(8))if all(d[i][j]==d[p[i]][p[j]]for i,j in combinations(range(8),2))]
 def act(W,p):return tuple(sorted(sum(1<<p[i]for i in range(8)if x>>i&1)for x in W))
 result=[]
 seen=set()
 for W in lines:
  if W not in seen:
   orb=set(act(W,p)for p in G);seen|=orb;result.append(W)
 assert len(lines)==len(set(lines)) and seen==set(lines)
 return len(lines),result

for ds in [[8],[6,2],[4,4],[4,2,2],[2,2,2,2]]:
 nmat,models=mats(ds);assert len(models)==1;W=models[0];D=decks(ds);ep=[(i,j)for i,j in combinations(range(8),2)for k in range(D[i][j])]
 dn=[[2-(X&Y).bit_count() if X!=Y else 0 for X in W]for Y in W];en=[(i,j)for i,j in combinations(range(8),2)for k in range(dn[i][j])]
 choices=[]
 for x in set(ep):
  for y in set(en):
   if all(sum(W[j]>>i&1 for j in y)<=1 for i in x)and all(sum(W[j]>>i&1 for i in x)<=1 for j in y):choices.append((x,y))
 out=set()
 for t in permutations(en):
  h=tuple(sorted(zip(ep,t)))
  if len(set(h))!=8 or any(x not in choices for x in h):continue
  if any(sum(int(p in a and n in b)for a,b in h)>2-(W[n]>>p&1)for p in range(8)for n in range(8)):continue
  S=[set(a)|{8+i for i in b}for a,b in h]
  if any(len(u&v)>2 for u,v in combinations(S,2)):continue
  out.add(h)
 def conflict(H):
  S=[set(a)|{8+i for i in b}for a,b in H];N=[{j for j,y in enumerate(S) if i!=j and len(x&y)==2}for i,x in enumerate(S)]
  roots=[];open=list(range(8));em=0;lo=0
  while open:
   C={open[0]}
   while 1:
    t=C|set().union(*(N[i]for i in C))
    if t==C:break
    C=t
   open=[i for i in open if i not in C];l=len(C);em+=sum(len(N[i])for i in C)//2
   if all(len(N[i])==2 for i in C):roots.append(l)
  return tuple(sorted(roots)),em

 G=[]
 for p in permutations(range(8)):
  if not all(D[i][j]==D[p[i]][p[j]] for i,j in combinations(range(8),2)):continue
  W1=[sum(1<<p[i]for i in range(8)if a>>i&1)for a in W]
  if set(W1)==set(W):G.append((p,tuple(W.index(w)for w in W1)))
 seen=set();cl=[];cyc=[]
 for h in sorted(out):
  if h in seen:continue
  if conflict(h)[0] not in ((),(8,)):continue
  orb=set(tuple(sorted((tuple(sorted(p[i]for i in a)),tuple(sorted(q[i]for i in b)))for a,b in h))for p,q in G)
  assert orb<=out;seen|=orb;cl.append(h)
  if conflict(h)[0]:cyc.append((h,len(orb)))
 expected={(8,):(2,8,1820,1820,243,4),(6,2):(4,6,681,681,118,0),(4,4):(4,32,2068,1984,77,0),(4,2,2):(4,16,326,324,26,0),(2,2,2,2):(2,192,90,72,2,2)}
 assert (nmat,len(G),len(out),len(seen),len(cl),len(cyc))==expected[tuple(ds)]
 print(ds,'group',len(G),'bare',len(out),'survivors',len(seen),'orbits',len(cl),'cyclic',len(cyc),'cyclic sizes',[n for h,n in cyc],flush=True)
