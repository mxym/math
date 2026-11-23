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
 assert len(seen)==len(lines)
 return len(lines),result

for ds in [[4,2,2]]:
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


from functools import lru_cache
from math import comb
def bits(x):
 while x:
  b=x&-x;x-=b;yield b.bit_length()-1
def bm(z):return sum(1<<i for i in z)
# Key the uncolored signed-contact counts with the distinguished edge at 0,1.
def keyify(Q,i,j):
 def it(a,b):
  groups={}
  for g in set(range(8))-{a,b}:groups.setdefault((len(Q[a]&Q[g]),len(Q[b]&Q[g])),[]).append(g)
  for tail in product(*(permutations(groups[k])for k in sorted(groups))):
   order=(a,b)+sum(tail,());yield tuple(len(Q[x]&Q[y])for x,y in combinations(order,2)),order
 return min((*it(i,j),*it(j,i)))
classes={};rooted=0
for index,H0 in enumerate(cl):
 Q=[set(a)|{8+n for n in b}for a,b in H0]
 for i,j in combinations(range(8),2):
  if Q[i]&Q[j]:continue
  ov=sorted((len(Q[k]&(Q[i]|Q[j])),k)for k in range(8)if k not in (i,j))
  if [a for a,b in ov]!=[1,1,1,1,2,2]or Q[ov[-1][1]]&Q[ov[-2][1]]:continue
  def signed_adj(p,v):return (W[max(p,v)-8]>>min(p,v)&1)if min(p,v)<8<=max(p,v)else 0
  if any(2-int(p in Q[a])-int(p in Q[b])-sum(signed_adj(p,v)for v in Q[a])<0 for a,b in ((i,j),(j,i))for p in range(16)):continue
  key,o=keyify(Q,i,j);rooted+=1;classes.setdefault(key,[]).append((index,tuple(bm(Q[v])for v in o)))
assert rooted==34 and len(classes)==6
J=list(combinations(range(6),2))
@lru_cache(None)
def part(sig):
 # Four labeled columns, sorted up to relabeling.
 found=set()
 for rows in product(*(combinations(range(4),r) for r in sig)):
  C=tuple(bm(g for g,r in enumerate(rows)if k in r)for k in range(4))
  if C!=tuple(sorted(C))or any(not 1<=z.bit_count()<=4 for z in C)or any((u&v).bit_count()>1 for u,v in combinations(C,2)):continue
  found.add(C)
 return sorted(found)
def overlaps(C):return tuple(sum((z>>i&1)*(z>>j&1)for z in C)for i,j in J)
def wedge(C):return sum(comb(z.bit_count()-1,2)for z in C)
def incidences(key):
 S=[[0]*8 for _ in range(8)]
 for (i,j),n in zip(combinations(range(8),2),key):S[i][j]=S[j][i]=n
 XA=part(tuple(2-x for x in S[0][2:]));XB=part(tuple(2-x for x in S[1][2:]))
 heavy=[i for i in range(6)if S[0][2+i]+S[1][2+i]==2];light=sorted(set(range(6))-set(heavy))
 for a in range(16):
  M=tuple(bm(heavy)+bm(i for g,i in enumerate(light)if a>>g&1==v)for v in (0,1))
  if M[0]>M[1]or any(not 3<=x.bit_count()<=5 for x in M):continue
  rem=[2-S[2+i][2+j]-k for (i,j),k in zip(J,overlaps(M))]
  for A in XA:
   if any((x&y).bit_count()>2 for x in A for y in M):continue
   ch=[v-k for v,k in zip(rem,overlaps(A))]
   if min(ch)<0:continue
   for B in XB:
    if any((x&y).bit_count()>2 for x in A+M for y in B):continue
    if any(k>v for v,k in zip(ch,overlaps(B))):continue
    if wedge(A)+wedge(B)+sum(comb(x.bit_count()-2,2)for x in M)>4:continue
    yield (3,)+tuple(1+(x<<2)for x in A)+tuple(2+(x<<2)for x in B)+tuple(x<<2 for x in M)
def zforests(H):
 d=[x.bit_count()-2 for x in H];E=[0]*11
 def dfs(i):
  while i<11 and not d[i]:i+=1
  if i==11:
   for t,Q0 in enumerate(H):
    for h in range(8):
     add=int((h==0 and bool(Q0&2))or(h==1 and bool(Q0&1)))
     if add+sum(H[j]>>h&1 for j in bits(E[t]))>2-(Q0>>h&1):return
    if any((Q0&H[q]).bit_count()+(E[t]&E[q]).bit_count()>2-(E[t]>>q&1)for q in range(t)):return
    S=1<<t
    while True:
     c=S
     for q in bits(S):c|=E[q]
     if c==S:break
     S=c
    if S.bit_count()>4 or sum(E[x].bit_count()for x in bits(S))>=2*S.bit_count():return
   yield tuple(E);return
  n=d[i]
  for ns in combinations([j for j in range(i+1,11)if d[j]and(H[j]&H[i]).bit_count()<=1],n):
   d[i]-=n
   for j in ns:d[j]-=1;E[i]|=1<<j;E[j]|=1<<i
   yield from dfs(i+1)
   for j in ns:d[j]+=1;E[i]^=1<<j;E[j]^=1<<i
   d[i]+=n
 yield from dfs(0)
def star(A,h):
 n=len(A)
 def R(i,j):return (12 if i==j else 0)+2-(A[i]>>j&1)-(A[i]&A[j]).bit_count()
 tar=[R(h,i)for i in range(n)]; rr=[[R(i,j)for j in range(n)]for i in range(n)]
 if min(map(min,rr))<0:return False
 pool0=[]
 for p in range(8):
  for q in range(8,16):
   for a,b in combinations(range(24,35),2):
    xs=(p,q,h,a,b);w=bm(xs)
    if any(tar[i]<=0 for i in xs)or any(rr[i][j]<=0 for i,j in combinations(xs,2)):continue
    if any((w&A[i]).bit_count()>2-(w>>i&1)for i in range(n)):continue
    pool0.append(w)
 col=[bm(j for j,w in enumerate(pool0)if w>>i&1)for i in range(n)];bad=[bm(j for j,x in enumerate(pool0)if (w&x).bit_count()>=3)for w in pool0];stack=[]
 def dfs(pool):
  if len(stack)==4:
   if any(tar):return False
   if any(sum((w>>i&1)*(w>>j&1)for w in stack)>rr[i][j]for i,j in combinations(range(n),2)):return False
   free=[x for x in stack if not(x&A[h])]
   def pair(z):
    if not z:return True
    for k,y in enumerate(z[1:],1):
     x=z[0]
     if (x&y).bit_count()!=1:continue
     if any((v&A[i]).bit_count()+(u>>i&1)+(v>>i&1)>2 for v,u in ((x,y),(y,x))for i in range(n)):continue
     if pair(z[1:k]+z[k+1:]):return True
    return False
   return pair(free)
  needs=[(pool&col[i],tar[i])for i in range(n)if tar[i]]
  if not needs or any(c.bit_count()<t for c,t in needs):return False
  c,t=min(needs,key=lambda v:comb(v[0].bit_count(),v[1]))
  def fill(c,p,t):
   if not t:return dfs(p)
   c&=p
   while c.bit_count()>=t:
    bit=c&-c;c-=bit;j=bit.bit_length()-1;w=pool0[j];pp=p&~bad[j];ok=True
    for i in bits(w):
     tar[i]-=1
     if not tar[i]:pp&=~col[i]
     if tar[i]<0:ok=False
    stack.append(w);hit=ok and fill(c,pp,t-1);stack.pop()
    for i in bits(w):tar[i]+=1
    if hit:return True
   return False
  return fill(c,pool,t)
 return dfs((1<<len(pool0))-1)
from collections import Counter
K=Counter()
for key,phys in classes.items():
 inc=list(incidences(key));K['geometry']+=bool(inc);K['incidence']+=len(inc);K['physicalInc']+=len(inc)*len(phys)
 for H in inc:
  Fs=list(zforests(H));assert len(Fs)==89
  for E in Fs:
   for ix,QQ in phys:
    A=[0]*35
    def ed(i,j):A[i]|=1<<j;A[j]|=1<<i
    for n,w in enumerate(W):
     for p in bits(w):ed(p,8+n)
    for g,w in enumerate(QQ):
     for p in bits(w):ed(16+g,p)
    ed(16,17)
    for z,w in enumerate(H):
     for g in bits(w):ed(24+z,16+g)
     for y in bits(E[z]):
      if y<z:ed(24+z,24+y)
    assert not(star(A,16)and star(A,17))
    K['eliminated']+=1
assert K=={'geometry':1,'incidence':2,'physicalInc':4,'eliminated':356},K
print('rank-free PASS',rooted,len(classes),K)
