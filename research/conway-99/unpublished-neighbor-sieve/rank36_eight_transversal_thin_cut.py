"""Rank 36: no genuine 18|18 wing cut at a triangle with eight transversal triangles. Python 3, NumPy. All tests are integer."""
from itertools import permutations,product,combinations
from collections import Counter,defaultdict
def part(n,k=1):
    if not n:yield ()
    for i in range(k,n+1):
        for q in part(n-i,i):yield (i,)+q
def match(s):
    if not s:yield ();return
    a=s[0]
    for i,b in enumerate(s[1:],1):
        for z in match(s[1:i]+s[i+1:]):yield ((a,b),)+z
M=tuple(match(tuple(range(6))));Mids={m:i for i,m in enumerate(M)}
def graphs():
 for L in range(1,7):
  for rest in part(6-L):
   chunks=(L,)+rest
   pi=[];i=0
   for j in chunks:
    pi+=list(range(i+1,i+j))+[i];i+=j
   p,q=0,6+pi[0]
   group=[]
   for rr in permutations(range(1,6)):
    g=(0,)+rr
    if any(g[pi[i]]!=pi[g[i]] for i in range(6)):continue
    group.append(tuple(Mids[tuple(sorted(tuple(sorted((g[x],g[y]))) for x,y in m))] for m in M))
   for mm in product(range(15),repeat=3):
    if any(tuple(g[i] for i in mm)<mm for g in group):continue
    rows=[0]*21
    def add(i,j):rows[i]|=1<<j;rows[j]|=1<<i
    for a in range(6):
      add(a,12+a);add(6+a,12+a)
      if a:add(a,6+pi[a])
    for a,m in enumerate(mm):
      for i,j in M[m]:add(6*a+i,6*a+j)
      for x in range(6*a,6*a+6):add(18+a,x)
    add(18,19);add(18,20);add(19,20)
    if any((rows[i]&rows[j]).bit_count()>2-(rows[i]>>j&1) for i,j in combinations(range(21),2)):continue
    if rows[p]&rows[q]:continue
    yield chunks,mm,p,q,rows
def connected3(p,q,R):
    S=range(18); mask=(1<<18)-1;n=[t&mask for t in R[:18]]
    n[p]|=1<<q;n[q]|=1<<p
    es=[(i,j) for i in S for j in S if i<j and n[i]>>j&1]
    def conn():
      a=1;l=1
      while l:
        nbr=0
        while l:
          u=l&-l;l-=u;nbr|=n[u.bit_length()-1]
        l=nbr&~a;a|=l
      return a==mask
    if not conn():return False
    for (a,b),(c,d) in combinations(es,2):
      n[a]^=1<<b;n[b]^=1<<a;n[c]^=1<<d;n[d]^=1<<c
      ok=conn()
      n[a]^=1<<b;n[b]^=1<<a;n[c]^=1<<d;n[d]^=1<<c
      if not ok:return False
    return True
def bits(z):return [i for i in range(21) if z>>i&1]
def atlas(p,q,R):
    cap=R[p]&((1<<18)-1)|R[q]&((1<<18)-1)
    P=(1<<p)|(1<<q);assert cap.bit_count()==4
    ab=[{} for _ in range(2)]
    for sign,L in enumerate((2,4)):
      for ids in combinations(range(18),L):
        word=sum(1<<i for i in ids)
        if any(sum(i//6==c for i in ids)>2 for c in range(3)):continue
        if not sign and word&(P|cap):continue
        if any((R[i]&R[j]).bit_count()>=2-(R[i]>>j&1) for i,j in combinations(ids,2)):continue
        if any((R[i]&word).bit_count()>2-(word>>i&1) for i in range(21)):continue
        ab[sign].setdefault(word&P,[]).append(word)
    return cap,ab
def rankcols(G):
    a=G.copy()%7;n=len(G);i=0;cols=[]
    for j in range(n):
        hs=np.flatnonzero(a[i:,j])
        if not len(hs):continue
        v=i+hs[0];a[[i,v]]=a[[v,i]]
        a[i]=a[i]*pow(int(a[i,j]),-1,7)%7
        col=a[:,j].copy();col[i]=0;a=(a-col[:,None]*a[i])%7
        i+=1;cols.append(j)
    return cols

def popcount64(w):
    if hasattr(np,'bitwise_count'):return np.bitwise_count(w)
    lut=np.array([i.bit_count() for i in range(256)],dtype=np.uint8)
    return lut[w.view(np.uint8).reshape(-1,8)].sum(axis=1)
import numpy as np
ALL=(1<<18)-1
def matinv(G):
    a=np.concatenate((G%7,np.eye(len(G),dtype=np.int64)),axis=1)
    det=1
    for j in range(len(G)):
        hits=np.flatnonzero(a[j:,j])
        if not len(hits):return None
        v=j+hits[0];a[[j,v]]=a[[v,j]];det=det*int(a[j,j])*(-1 if v!=j else 1)%7
        a[j]=a[j]*pow(int(a[j,j]),-1,7)%7
        col=a[:,j].copy();col[j]=0;a=(a-col[:,None]*a[j])%7
    return (det,a[:,len(G):])
def sidesample(k,mm,p,q,r):
    n=[h&ALL for h in r[:18]]; cap,ab=atlas(p,q,r)
    def pack(lst):
        out=defaultdict(list)
        for w in lst:out[tuple((w>>(i*6)&63).bit_count() for i in range(3))].append(w)
        return out
    return mm,p,q,n,pack(ab[0].get(0,[])),{m:pack(v) for m,v in ab[1].items()}
def full(u,v):
    D=[]
    for j,(x,y) in enumerate(((u,v),(v,u))):
      _,p,q,n,*_=x;_,p2,q2,*_=y
      a=[w<<(j*18) for w in n]
      a[p]|=1<<((1-j)*18+q2);a[q]|=1<<((1-j)*18+p2)
      D.extend(a)
    return D
def wordaxes(u,v):
    d=full(u,v)
    W=[(63<<(6*i))|(63<<(18+6*i)) for i in range(3)]
    masks=[];groups=[];roles=[];phys=[];p=u[1];q=u[2]
    Mark=(1<<p)|(1<<q)|(1<<(18+p))|(1<<(18+q))
    for s,(m,n) in enumerate(((u,v),(v,u))):  # sign+ -> small U, big V
      for j in range(3,8):
       # far plus vectors j. Their far opposite id never literal shared; nA=2,nB=1.
       a,b=n[1:3]
       edge= ((1<<a) if j&(2 if not s else 1) else 0) | ((1<<b) if j&(1 if not s else 2) else 0)
       local4=n[5].get(edge,{})
       gd=[]
       for c,ws in m[4].items():
        ds=local4.get(tuple(2-i for i in c),[])
        for i,l in product(ws,ds):
          w=i+(l<<18) if s==0 else l+(i<<18)

          arr=tuple(w&h for h in W)
          gd.append(len(masks));masks.append(w);roles.append((s,j));phys.append(arr)
       groups.append(gd)
    mat=((np.array(masks,dtype=np.uint64)[:,None] >> np.arange(36,dtype=np.uint64)) & 1).astype(np.int16)
    return masks,groups,roles,phys,mat,d,Mark
def wrapped(u,v):
    masks,gps,roles,phys,X,d,mark=wordaxes(u,v);dim=36
    assert all(gps)
    G=3*np.eye(dim,dtype=np.int64)-np.array([[(h>>i)&1 for i in range(dim)] for h in d],dtype=np.int64)+4
    ids=rankcols(G);left=[i for i in range(36) if i not in ids];r=len(left)
    assert r in (0,1)
    det,B=matinv(G[np.ix_(ids,ids)])
    if r==0 and det in (1,2,4):return 'square determinant'
    A0=X;P=4-X;Xs=P[:,ids].astype(np.int16);Z0=Xs@B.astype(np.int16)%7
    q=(-np.sum(Z0*Xs,axis=1))%7
    if r:
        diff=(P[:,left]-Z0@G[np.ix_(ids,left)].astype(np.int16))%7
        t=3 if det in (1,2,4) else 1
        ix,ys=np.nonzero((diff==0)&(q[:,None]==(t*np.arange(7)**2%7)[None,:]))
        Raw=A0[ix];X=np.column_stack((Xs[ix,:],ys)).astype(np.int16);Z=np.column_stack((Z0[ix,:],t*ys%7)).astype(np.int16)
    else:
        ix=np.flatnonzero(q==0)
        Raw=A0[ix];X=Xs[ix,:];Z=Z0[ix,:]
    masks=[masks[i] for i in ix];roles=[roles[i] for i in ix];ph=[phys[i] for i in ix]
    gps=[[j for j,(s,k) in enumerate(roles) if s*5+k-3==i] for i in range(10)]
    assert all(gps)
    from functools import lru_cache
    x=np.array(masks,dtype=np.uint64);rg=np.array([s*5+j-3 for s,j in roles]);sigs=np.array(ph,dtype=np.uint64);MM=np.uint64(mark)
    @lru_cache(None)
    def compat(i):
        s,j=roles[i]
        w=x&x[i];vv=np.array([t!=s and (j&k).bit_count()%2 for t,k in roles],dtype=np.int8)
        same=(rg//5==s)
        ok=((X@Z[i])%7==4-vv)&(popcount64(w)<=2-vv)&(~same|((w&~MM)==0))&(sigs!=sigs[i,:]).all(axis=1)
        return int.from_bytes(np.packbits(ok,bitorder="little").tobytes(),"little")
    ff=np.zeros(36,dtype=np.int64);ff[u[1]]=ff[u[2]]=1;ff[18+v[1]]=ff[18+v[2]]=-1
    req=-4*ff-(3*np.eye(36,dtype=np.int64)+4-G)@ff
    def csp(todo,used):
      if not todo:
        sg=np.array([1 if roles[i][0]==0 else -1 for i in used])
        return bool(np.all(Raw[used].T@sg==req))
      cs=min(todo,key=int.bit_count);to=list(todo);to.remove(cs)
      while cs:
        bit=cs&-cs;cs-=bit;i=bit.bit_length()-1
        cc=compat(i);ss=[st&cc for st in to]
        if all(ss) and csp(ss,used+[i]):return True
      return False
    assert not csp([sum(1<<j for j in gg) for gg in gps],[])
    return 'corank one' if r else 'full rank nonsquare'

# Optional --shard INDEX COUNT splits first-half indices; the unsharded run checks all 1378 pairs.
if __name__=='__main__':
    import sys
    h=[sidesample(k,mm,p,q,r) for k,mm,p,q,r in graphs() if k==(2,1,1,1,1) and connected3(p,q,r)]
    assert len(h)==52
    ix,step=(0,1) if len(sys.argv)==1 else (int(sys.argv[2]),int(sys.argv[3]))
    assert 0<=ix<step
    tot=Counter()
    for i in range(ix,len(h),step):
        for j in range(i,len(h)):tot[wrapped(h[i],h[j])]+=1
    print(dict(tot))
    if step==1:assert tot=={'square determinant':547,'full rank nonsquare':642,'corank one':189}
