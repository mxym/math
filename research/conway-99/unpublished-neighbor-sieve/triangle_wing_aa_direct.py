"""Two A current planes never meet. Pure integer replay; requires the preceding
triangle_wing_twelve_currents.py and twelve_sites.py. No optimization package.
"""
from collections import Counter
from itertools import permutations, product
import base64, json, zlib
from twelve_sites import MATES, chart, multiplicities
from triangle_wing_twelve_currents import line, labelsum, cross, kernel, vecs, inventory


def normal(h,k):
    d=pow(next(v for v in h if v),-1,7)
    return tuple(d*v%7 for v in h),tuple(d*v%7 for v in k)


def inverse(p):return tuple(p.index(i) for i in range(len(p)))


def charts():
    g=chart(MATES[0],MATES[1],MATES[0],(0,2,1,3))
    ed={e:v for e,v in multiplicities(g).items() if v}
    L=[[3*int(i==j)-int(j in g[i]) for j in range(12)] for i in range(12)]
    V=vecs(kernel(L+[[1]*12]));P=list(permutations(range(3)))
    aut=[]
    for axis in P:
        a,b,c=axis
        for order in permutations(range(4*a,4*a+4)):
            st=[next(v for v in g[i] if v//4==b) for i in order]
            th=[next(v for v in g[i] if v//4==c) for i in st]
            d=list(order)+st+th
            if all({d[j] for j in g[i]}==g[d[i]] for i in range(12)):
                aut.append((axis,d))
    assert len(aut)==12
    pending={(p,h,k) for p in P for h in set(map(line,V)) for k in V}
    stat=Counter();out=[]
    while pending:
        pp,h,k=min(pending);orbit=set()
        for a,f in aut:
            for b,g0 in aut:
                p=tuple(inverse(a)[pp[j]] for j in b)
                u,v=normal([h[i] for i in f],[k[i] for i in g0])
                orbit.add((p,u,v));u,v=normal(v,u);orbit.add((inverse(p),u,v))
        assert orbit<=pending
        pending-=orbit
        s=cross(ed,ed,pp,[labelsum(e,h) for e in ed],[labelsum(e,k) for e in ed])
        stat[s]+=1
        if s=='pass':out.append((pp,h,k))
    assert stat=={'hist':16,'pass':4,'parity':2,'cell':1}
    return g,ed,out


def data(ed,rep):
    pp,h,k=rep;E=list(ed);n=len(E)
    D=[(i,j) for i,e in enumerate(E) for j,f in enumerate(E)
       if labelsum(e,h)==labelsum(f,k)
       and max(Counter([v//4 for v in e]+[pp[w//4] for w in f]).values())<=2]
    R=[(i,n+j,*(2*n+12*s+t for s in E[i] for t in E[j])) for i,j in D]
    rhs=list(ed.values())*2+[2-int(s//4==pp[t//4]) for s in range(12) for t in range(12)]
    return E,D,R,rhs


def farkas(R,rhs):
    B=json.loads(zlib.decompress(base64.b64decode(WIT)))
    ct=[0,0]
    def verify(z,cols,b):
        if type(z) is dict:
            ct[1]+=1;w={int(i):v for i,v in z.items()}
            assert all(0<=i<len(b) and type(v) is int for i,v in w.items())
            assert sum(v*b[i] for i,v in w.items())>sum(max(0,sum(w.get(r,0) for r in R[j])) for j in cols)
        else:
            ct[0]+=1;i,z0,z1=z;assert i in cols;nextcols=cols-{i}
            verify(z0,nextcols,b);b1=b[:]
            for r in R[i]:b1[r]-=1
            verify(z1,nextcols,b1)
    verify(B,set(range(len(R))),rhs)
    assert ct==[152,153]


def admissible_row(root,tab,D,E,g):
    i,j=D[root]
    q=tuple(2-int(v in E[a])-len(g[v].intersection(E[a])) for a in (i,j) for v in range(12))
    assert all(x in (0,1,2) for x in q) and sum(q)==32
    mask=lambda a,b:sum(1<<v for v in E[a])+sum(1<<(12+v) for v in E[b])
    home=mask(i,j);c=[mask(*D[y]) for y in tab if y!=root and (mask(*D[y])&home).bit_count()<=1]
    def rec(opts,q):
        if not any(q):return True
        opts=[t for t in opts if all(q[v] or not(t>>v&1) for v in range(24))]
        active=[v for v in range(24) if q[v]]
        v=min(active,key=lambda j:sum(t>>j&1 for t in opts)-q[j])
        if sum(t>>v&1 for t in opts)<q[v]:return False
        for t in opts:
            if t>>v&1 and rec([z for z in opts if z!=t and (z&t).bit_count()<=1],
                                 tuple(x-(t>>j&1) for j,x in enumerate(q))):
                return True
        return False
    return rec(c,q)


def contact_search(E,D,R,rhs,g):
    masks=[0]*len(rhs)
    for j,rows in enumerate(R):
        for r in rows:masks[r]|=1<<j
    N=len(D);flag=1<<N;ct=[0,0,0]
    def walk(active,chosen,b):
        ct[0]+=1
        while True:
            must=ban=0;opt=None
            for m,z in zip(masks,b):
                t=active&m;n=t.bit_count()
                if z<0 or n<z:return
                if z==0:ban|=t
                elif n==z:must|=t
                else:
                    cost=n if z==1 else n*(n-1)//2
                    if opt is None or cost<opt[0]:opt=(cost,t)
            if not any(b):
                ids=[i for i in range(N) if chosen>>i&1];assert len(ids)==60
                ct[1]+=1
                ct[2]+=all(admissible_row(j,ids,D,E,g) for j in ids)
                return
            if not(must or ban):
                basis={}
                for z,m in zip(b,masks):
                    t=(m&active)|(flag if z%2 else 0)
                    while t&~flag:
                        p=t&-t
                        if p not in basis:basis[p]=t;break
                        t^=basis[p]
                    if t==flag:return
                piv=sorted(basis,reverse=True)
                for i,p in enumerate(piv):
                    t=basis[p]
                    for a in piv[i+1:]:
                        if basis[a]&p:basis[a]^=t
                for p,t in basis.items():
                    if t==p:ban|=p
                    elif t==(p|flag):must|=p
            if must&ban:return
            if not(must or ban):break
            chosen|=must;active&=~(must|ban)
            while must:
                p=must&-must;must-=p
                for r in R[p.bit_length()-1]:b[r]-=1
        assert opt is not None
        t=opt[1]&-opt[1];i=t.bit_length()-1;b1=b[:]
        for r in R[i]:b1[r]-=1
        walk(active^t,chosen|t,b1);walk(active^t,chosen,b[:])
    walk(flag-1,0,rhs[:])
    return ct


def main():
    g,ed,cases=charts();census=[]
    for k,rep in enumerate(cases):
        E,D,R,rhs=data(ed,rep)
        assert len(D)==(366,336,328,324)[k]
        if k==0:farkas(R,rhs)
        else:census.append(contact_search(E,D,R,rhs,g))
    print(census)
    assert census==[[1033,0,0],[1389,0,0],[673,1,0]]
    ts,_=inventory();old,new=Counter(),Counter()
    from itertools import combinations_with_replacement
    for tr in combinations_with_replacement(ts,3):
        names=[x[0] for x in tr];a=names.count('A');b=names.count('B')
        c=max([0]+([1] if b else [])+([2] if a or b>=2 else [])+([3] if a and (a>=2 or b) else []))
        for s,out in [(c,old),(max(c,4 if a>=2 else 0),new)]:
            rank=34-2*a-b+2*s;sign=tr[0][1]*tr[1][1]*tr[2][1]*(-1)**s
            if rank>36 or (rank==36 and sign!=-1):out[''.join(sorted(names))]+=1
    assert sum(old.values())==58 and sum(new.values())==66
    print('66 of 455 rejected;',dict(new))

from pathlib import Path
WIT=Path(__file__).with_name('triangle-wing-aa-farkas.b64').read_text().strip()

if __name__=='__main__':main()
