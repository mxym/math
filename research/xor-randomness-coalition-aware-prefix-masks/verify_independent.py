"""Literal finite execution and exact transcript histograms."""

from collections import Counter
from functools import reduce
from itertools import combinations, product
from operator import xor


def fold(xs):
    return reduce(xor,xs,0)


def make_tree(indices):
    if len(indices)==1:
        return indices[0]
    k=len(indices)//2
    return (make_tree(indices[:k]),make_tree(indices[k:]))


def children_first(node):
    if isinstance(node,int):
        return []
    a,b=node
    return children_first(a)+children_first(b)+[node]


def schedule(n,t,mode):
    if mode=="chain":
        return None
    A=make_tree(tuple(range(t)))
    B=make_tree(tuple(range(t,n)))
    root=(A,B)
    topological=children_first(root)
    mapping={v:i for i,v in enumerate(children_first(A)+[root]+children_first(B))}
    assert len(mapping)==n-1
    return root,mapping,topological


def execute(n,t,mode,structure,x,masks,seeds):
    tx=[]
    phase=[0]*n
    for d,S in enumerate(masks):
        for i,(a,b) in enumerate(zip(S,S[1:])):
            bit=a^b
            phase[i]^=bit
            if d!=i:
                tx.append((d,i,bit))
    leaf=[v^m for v,m in zip(x,phase)]
    if mode=="chain":
        prev=0
        for i,y in enumerate(leaf):
            prev^=y
            if i+1<n:
                tx.append((i,i+1,prev))
        root_owner=n-1
    else:
        root,owner,order=structure
        value=dict(enumerate(leaf))
        for node in order:
            u,v=node
            target=owner[node]
            for w in (u,v):
                sender=w if isinstance(w,int) else owner[w]
                if sender!=target:
                    tx.append((sender,target,value[w]))
            value[node]=value[u]^value[v]
        prev=value[root]
        root_owner=owner[root]
    assert prev==fold(x)
    tx.extend((root_owner,i,prev) for i in range(n) if i!=root_owner)
    # Private tapes are incident only to their source; this includes
    # any randomness used in a local non-sent setup bit.
    tx.extend((d,d,b) for d,tape in enumerate(seeds) for b in tape)
    return tx


def verify(n,t,mode,width,M):
    S=schedule(n,t,mode)
    tapes=list(product(*(tuple(product((0,1),repeat=t+w)) for w in width)))
    masks=[]
    for tape_tuple in tapes:
        ss=[]
        for d in range(t):
            u=sum(b<<i for i,b in enumerate(tape_tuple[d][t:]))
            ss.append((0,)+tape_tuple[d][:t]+tuple((u&k).bit_count()%2 for k in M[d])+(0,))
        masks.append(tuple(ss))
    Cs=[C for k in range(t+1) for C in combinations(range(n),k)]
    first=execute(n,t,mode,S,(0,)*n,masks[0],tapes[0])
    visible=[sum(1<<j for j,(a,b,_) in enumerate(first) if a in C or b in C) for C in Cs]
    hist={}
    total=checked=0
    message_roles=tuple(m[:2] for m in first)
    for x in product((0,1),repeat=n):
        views=[Counter() for _ in Cs]
        for s,raw in zip(masks,tapes):
            messages=execute(n,t,mode,S,x,s,raw)
            assert tuple(m[:2] for m in messages)==message_roles
            transcript=sum(bit<<j for j,(_,_,bit) in enumerate(messages))
            for v,a in zip(visible,views):
                a[transcript&v]+=1
            total+=1
        for C,V in zip(Cs,views):
            label=(C,tuple(x[i] for i in C),fold(x))
            if label in hist:
                assert V==hist[label], (C,x)
                checked+=1
            else:
                hist[label]=V
    print(f"Literal {mode} n={n}, t={t}: {total} complete executions, "
          f"{len(Cs)} coalitions, {checked} equal-view comparisons")


if __name__=="__main__":
    verify(4,1,"tree",(2,),((1,2),))
    verify(3,2,"tree",(0,0),((),()))
    verify(6,2,"chain",(3,2),((1,2,4),(1,2,3)))
    verify(6,2,"tree",(3,3),((1,2,4),(1,2,4)))
