"""Rooted seed coverage for every graph on four vertices and every small-vertex mask."""
from itertools import combinations
n=4
V=set(range(n))
edges=list(combinations(range(n),2))
valid=seeds=mixed=0
for code in range(1<<len(edges)):
    nbr={i:set() for i in V}
    for i,(a,b) in enumerate(edges):
        if code>>i&1: nbr[a].add(b); nbr[b].add(a)
    def grow(R,S):
        R=set(R)
        while True:
            new=R|{y for x in R for y in nbr[x]&S}
            if new==R: return R
            R=new
    for mask in range(1,1<<n):
        S={i for i in V if mask>>i&1}
        unseen=set(S); comps=[]
        while unseen:
            C=grow({min(unseen)},unseen);comps.append(C);unseen-=C
        for s in (2,3,4):
            if min(map(len,comps))<s: continue
            for bits in range(1<<n):
                small={i for i in S if bits>>i&1}
                allslots=set()
                types=set()
                for C in comps:
                    if C&small:
                        slots=C&small;types.add("small")
                    else:
                        p=min(C);slots={p};types.add("large")
                        while len(slots)<s:
                            choices={y for x in slots for y in nbr[x]&C}-slots
                            assert choices
                            slots.add(min(choices))
                        assert grow({p},slots)==slots and len(slots)==s
                        seeds+=1
                    assert not allslots&slots
                    allslots|=slots
                    assert grow(slots,C)==C
                assert grow(allslots,S)==S
                mixed+=len(types)==2
                valid+=1
print("PASS: rooted component decompositions",valid,"large cores",seeds,
      "mixed configurations",mixed)
