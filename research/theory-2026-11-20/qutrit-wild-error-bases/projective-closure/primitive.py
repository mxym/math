from itertools import permutations, product
from collections import Counter, deque
def prod(x,y):return tuple(x[i] for i in y)
def inv(x):return tuple(x.index(i) for i in range(len(x)))
def cliques(G, report=True):
    G=set(G);e=tuple(range(len(next(iter(G))))); O3=sorted([p for p in G if p!=e and prod(prod(p,p),p)==e])
    idx={p:j for j,p in enumerate(O3)}; ns=[sum(1<<j for j,y in enumerate(O3) if prod(inv(x),y) in idx) for x in O3]
    stats=Counter(); records=[];maxc=0
    def rec(w,poss,ex):
        nonlocal maxc
        if not (poss or ex):
            stats[len(w)+1]+=1;maxc=max(maxc,1+len(w))
            if len(w)>=8:records.append(tuple(O3[j] for j in w))
            return
        ulist=poss|ex;u=(ulist&-ulist).bit_length()-1
        opts=poss & ~ns[u]
        while opts:
            bit=opts&-opts;v=bit.bit_length()-1;opts-=bit
            rec(w+[v],poss&ns[v],ex&ns[v])
            poss^=bit;ex|=bit
    rec([], (1<<len(ns))-1,0)
    Hs={}
    for w in records:
        wl=set(w)
        if any(wl<=h for h in Hs):continue
        h={e};q=deque([e])
        while q:
            a=q.popleft()
            for b in w:
                c=prod(a,b)
                if c not in h:h.add(c);q.append(c)
        Hs[frozenset(h)]=True
    if report:print("group",len(G),"O3",len(O3),"anchored maximal cliques",sorted(stats.items()),"hulls",Counter(map(len,Hs)))
    return stats,Hs
def An(n):return [p for p in permutations(range(n)) if sum(a>b for j,a in enumerate(p) for b in p[j+1:])%2==0]
def gl32():
    G=[]
    for a,b,c in permutations(range(1,8),3):
        if a^b==c:continue
        G.append(tuple(((a if x&1 else 0)^(b if x&2 else 0)^(c if x&4 else 0))-1 for x in range(1,8)))
    return G
def psl27():
    els=set()
    # Eight projective points represented by 0,...,6 and the point at infinity.
    for a,b,c,d in product(range(7),repeat=4):
        if (a*d-b*c)%7!=1:continue
        row=[]
        for x in range(8):
            n,h=(a,c) if x==7 else ((a*x+b)%7,(c*x+d)%7)
            row.append(7 if not h else n*pow(h,-1,7)%7)
        els.add(tuple(row))
    return list(els)
def asl23():
    G=[]
    for a,b,c,d in product(range(3),repeat=4):
        if (a*d-b*c)%3!=1:continue
        for e,f in product(range(3),repeat=2):
            G.append(tuple(3*((a*x+b*y+e)%3)+((c*x+d*y+f)%3) for x,y in product(range(3),repeat=2)))
    return G
if __name__=='__main__':
    cases=[('A5',An(5),60,{3:10,4:20},{}),
           ('PSL2(7)',psl27(),168,{3:28,4:784},{}),
           ('A6',An(6),360,{5:60,9:10},{9:10}),
           ('ASL2(3)',asl23(),216,{27:4},{27:4})]
    for name,G,n,stats,hulls in cases:
        print(name)
        if len(set(G))!=n:raise ValueError('group order')
        w,H=cliques(G)
        if dict(w)!=stats or dict(Counter(map(len,H)))!=hulls:raise ValueError('wrong table')

