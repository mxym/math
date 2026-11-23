"""Exact 12-fiber exclusions. Python standard library only; no LP solver."""
from itertools import combinations, product

def run(missing,path):
    M=list(map(frozenset,missing))
    E=[frozenset(f) for f in combinations(range(6),2) if frozenset(f) not in M]
    n=len(E);p=[9]*6+[3]*3;d=len(p)
    W=[[int(a in f) for f in E] for a in range(6)]+[[int(not e&f) for f in E] for e in M]
    dis=[[int(not f&g) for g in E] for f in E]
    c=[[v+2*(i==j) for j,v in enumerate(z)] for i,z in enumerate(dis)]
    grids=[t for t in combinations(range(n),3) if all(dis[i][j] for i,j in combinations(t,2))]
    hit=[sum(2**i for i in t) for t in grids]
    assert set(sum(x*2**i for i,x in enumerate(w)) for w in W)=={
        s for s in range(2**n) if all((s&g).bit_count()==1 for g in hit)}
    for e in M:
        assert any(not f&g and len(f|g|e)==6 for f,g in combinations(E,2))
    tri=[]
    for a in range(6):
        for b,z in combinations(set(range(6))-{a},2):
            q=list(map(frozenset,((a,b),(a,z),(b,z))))
            if all(f in E for f in q):
                tri.append(tuple(E.index(f) for f in q)); break
        else: raise AssertionError("present graph needs a triangle at every index")
    def rows(y,deg):
        for ve in product(range(4),repeat=3):  # 0..3 is exact population capacity
            r=[yy-sum(q*w[i] for q,w in zip(ve,W[6:])) for i,yy in enumerate(y)]
            v=[r[i]+r[j]-r[k] for i,j,k in tri]
            if any(q<0 or q%2 for q in v):continue
            h=tuple(q//2 for q in v)+ve
            if sum(h)==deg and all(sum(q*w[i] for q,w in zip(h,W))==yy for i,yy in enumerate(y)):
                yield h
    O=[]
    for j,w in enumerate(W):
        y=[6-3*w[i]-sum(x*k for x,k in zip(w,dis[i])) for i in range(n)]
        O.append([h for h in rows(y,14-sum(w)) if all(x<=p[k]-(k==j) for k,x in enumerate(h))])
    assert all(O)
    off=set(range(6))-set().union(*M)
    if path:
        assert len(off)==2
        assert all(sum(h[6:])>=1 for j in off for h in O[j])
        assert all(h[i]<=1 for j in range(6,9) for h in O[j] for i in off)
        assert all(h[i]==1 for i in off for h in O[i] if sum(h[6:])==1)
        print('P4 exterior domains:',list(map(len,O)),'odd class with forced degree 1')
        return
    assert off=={5} and all(h[5] in (0,1) and h[5]*2+sum(h[6:])==3 for h in O[5])
    H=[]
    for i,f in enumerate(E):
        y=[(16 if f==g else 5 if not f&g else 6)-sum(x*t for x,t in zip(c[i],c[k])) for k,g in enumerate(E)]
        H.append([h for h in rows(y,14-sum(c[i])) if all(not x or W[k][i] for k,x in enumerate(h))])
    assert all(H)
    # Aggregate classes 0={0}; 1={1,2,3,4}; 2={5}; 3=all exceptional.
    bins=(0,1,1,1,1,2,3,3,3);P=[9,36,9,9]
    def pack(v):return [sum(x for x,b in zip(v,bins) if b==i) for i in range(4)]
    cells=[(bins[j],pack(h)) for j,v in enumerate(O) for h in v]+[(4+i,pack(h)) for i,v in enumerate(H) for h in v]
    # Coefficients of a verified dual. r(a,b) uses outgoing degree from class a to b minus reverse.
    po=[405,-332,-1346,-268,-126,-126,-39,-297,-297,-297,192,-297,-297,192,-48,-48]
    inc={(6,1):-80,(9,1):-80}
    re={(1,0):64,(2,0):174,(2,1):120,(3,0):58,(3,2):-126}
    gram={(1,0):6,(1,1):8,(2,0):6,(3,1):2,(3,2):-4,(3,3):-3}
    def slack(j,h):
        v=po[j]+sum(a*h[t] for (i,t),a in inc.items() if j==4+i)
        v+=sum(a*((j==t)*h[k]-(j==k)*h[t]) for (t,k),a in re.items())
        v+=sum(a*(h[t]*h[k]+(j==t)*h[k]) for (t,k),a in gram.items())
        return v-15*(j==2)*h[3]
    assert min(slack(j,h) for j,h in cells)>=0
    upper=sum(x*y for x,y in zip(po,P+[3]*n))
    upper+=sum(a*sum(z*w[i] for t,z,w in zip(bins,p,W) if t==k) for (i,k),a in inc.items())
    upper+=sum(a*(2*P[i]*P[j]+12*(i==j)*P[i]) for (i,j),a in gram.items())
    assert upper==153
    print('P3+K2 exterior domains:',list(map(len,O)),'core domains:',list(map(len,H)))
    print('15E <=',upper,'while E>=9 and E=3(mod4) force E>=11.')

if __name__=='__main__':
    run(((0,1),(0,2),(1,3)),True)
    run(((0,1),(0,2),(3,4)),False)
