#!/usr/bin/env python3
"""Independent projective-kernel census for elementary abelian K3,3 covers."""
from collections import defaultdict
from functools import cache
from itertools import combinations,product


def require(test,msg):
    if not test:raise AssertionError(msg)


Z=(0,0,0,0)
cotree={(1,4):0,(1,5):1,(2,4):2,(2,5):3}
ADJ=[[] for _ in range(6)]
for i in range(3):
    for j in range(3,6):
        k=cotree.get((i,j))
        v=tuple(int(t==k) for t in range(4))
        ADJ[i].append((j,v));ADJ[j].append((i,tuple(-x for x in v)))


def vadd(a,b):
    return tuple(x+y for x,y in zip(a,b))


def trace_words(length):
    # K3,3 is simple: forbid immediate reversal and the cyclic last-to-first reversal.
    for root in range(6):
        def dfs(layers,shifts):
            if len(layers)==length:
                v=layers[-1]
                if layers[-2]==root or layers[1]==v:return
                for j,d in ADJ[v]:
                    if j==root:yield layers,shifts,vadd(shifts[-1],d)
                return
            for v,d in ADJ[layers[-1]]:
                if len(layers)<2 or v!=layers[-2]:
                    yield from dfs(layers+(v,),shifts+(vadd(shifts[-1],d),))
        yield from dfs((root,),(Z,))


@cache
def all_classes(p):
    inverse=[0]+[pow(i,-1,p) for i in range(1,p)]
    @cache
    def normalize(d):
        if not any(d):return Z
        s=inverse[next(x for x in d if x)]
        return tuple(s*x%p for x in d)
    lines=[d for d in product(range(p),repeat=4) if any(d) and normalize(d)==d]
    lid={d:1<<i for i,d in enumerate(lines)}
    buckets=[]
    for length,expected in [(4,72),(8,648),(16,133128)]:
        table=defaultdict(set)
        count=0
        for V,S,total in trace_words(length):
            count+=1
            T=tuple(x%p for x in total)
            occ=[set() for _ in range(6)]
            cc=0
            for v,s in zip(V,S):
                t=tuple(x%p for x in s)
                if t in occ[v]:break
                for r in occ[v]:
                    d=normalize(tuple((a-b)%p for a,b in zip(r,t)))
                    cc |= lid[d]
                occ[v].add(t)
            else:
                table[lid.get(normalize(T),0)].add(cc)
        require(count==expected,("rooted walk coverage",length,count))
        buckets.append(table)
    return lid,normalize,buckets


def kern_bases(p,d):
    for piv in combinations(range(4),d):
        free=[(i,j) for i in range(d) for j in range(piv[i]+1,4) if j not in piv]
        for x in product(range(p),repeat=len(free)):
            K=[[int(j==v) for j in range(4)] for v in piv]
            for (i,j),a in zip(free,x):K[i][j]=a
            yield K


def ker_mask(p,K,lid,normalize):
    d=len(K)
    ans=0
    for j in range(d):
        for u in product(range(p),repeat=d-j-1):
            coeff=(0,)*j+(1,)+u
            vec=tuple(sum(a*k[t] for a,k in zip(coeff,K))%p for t in range(4))
            ans |= lid[normalize(vec)]
    return ans


def order_stat(p):
    lid,norm,buckets=all_classes(p)
    rows=[]
    passing=[]
    for rank in range(1,5):
        count=ok=0
        for K in kern_bases(p,4-rank):
            k=ker_mask(p,K,lid,norm)
            count+=1
            possible=False
            for table in buckets:
                for w,C in table.items():
                    if w and not w&k:continue
                    if any(not c&k for c in C):
                        possible=True
                        break
                if possible:break
            if not possible:
                ok+=1
                passing.append((rank,K))
        rows.append((count,ok))
    print(p,rows)
    return rows,passing


def f3_independent():
    P=((0,0),(1,0),(0,1))
    W=(0,1,0,1,2,1,0,2)
    pos=(0,0)
    seen=[set(),set()]
    for i,w in enumerate(W):
        require(pos not in seen[i%2],"primitive F3^2 word is simple")
        seen[i%2].add(pos)
        pos=tuple((a+(-1)**i*b)%3 for a,b in zip(pos,P[w]))
    require(pos==(0,0) and W[-1]!=W[0],"F3^2 closes")


def f7_example():
    p=7
    V=((1,0,0),(0,1,0),(0,0,1),(1,2,2))
    # 113=1+2*7+2*49; kernel rank one.
    K=[[(-1)%p,(-2)%p,(-2)%p,1]]
    lid,norm,buckets=all_classes(p)
    k=ker_mask(p,K,lid,norm)
    require(not any((w==0 or w&k) and any(not cc&k for cc in C)
                    for table in buckets for w,C in table.items()),"F7^3 concrete cover")
    require(all(sum(a*v[i] for a,v in zip(K[0],V))%p==0 for i in range(3)),
            "example kernel")


if __name__=="__main__":
    f3_independent()
    EXPECT={3:[(40,0),(130,0),(40,0),(1,0)],
            5:[(156,0),(806,0),(156,0),(1,1)],
            7:[(400,0),(2850,0),(400,52),(1,1)]}
    for prime,rows in EXPECT.items():
        a,_=order_stat(prime)
        require(a==rows,(prime,a))
    f7_example()
    print("PASS all three projective censuses and the concrete F7^3 witness")
