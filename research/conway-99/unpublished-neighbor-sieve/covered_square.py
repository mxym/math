"""Enumerate the short covered-triangle list and check the cyclic exclusions."""
from collections import Counter
from itertools import combinations, permutations, product


def matchings(labels):
    if not labels:
        yield {}
        return
    u,*rest = labels
    for v in rest:
        for other in matchings([x for x in rest if x!=v]):
            yield {u:v,v:u,**other}


def fixed_parts(n):
    labels = tuple(range(n))
    centralizer = [g for g in permutations(labels) if all(g[i^1]==(g[i]^1) for i in labels)]
    seen = set()
    for q,r in product(matchings(labels),repeat=2):
        if any(len({i^1,q[i],r[i]})==2 for i in labels):
            continue
        key = min(tuple(g.index(perm[g[i]]) for perm in (q,r) for i in labels) for g in centralizer)
        if key not in seen:
            seen.add(key)
            yield tuple(q[i] for i in labels),tuple(r[i] for i in labels)


def cycles(count,minimum=(2,0)):
    if not count:
        yield ()
    for length in range(2,count+1):
        for sign in (0,1):
            part = length,sign
            if part>=minimum:
                for rest in cycles(count-length,part):
                    yield (part,*rest)


def chart(q,r,u):
    graph = [set() for _ in range(39)]
    def edge(i,j):
        graph[i].add(j)
        graph[j].add(i)
    for i,j in combinations(range(3),2):
        edge(i,j)
    for i in range(12):
        for w,mate in enumerate((i^1,q[i],r[i])):
            base=3+12*w
            edge(w,base+i)
            edge(base+i,base+mate)
        edge(3+i,15+i)
        edge(3+i,27+i)
        edge(15+i,27+u[i])
    return graph


def templates():
    for t in (0,2,4,6):
        for q,r in fixed_parts(t):
            for parts in cycles((12-t)//2):
                u = list(range(t))
                for length,sign in parts:
                    start = len(u)
                    for i in range(length):
                        for s in (0,1):
                            u.append(start+2*((i+1)%length)+(s^(sign if i==length-1 else 0)))
                tail = tuple(i^1 for i in range(t,12))
                yield t,parts,chart(q+tail,r+tail,u)


def pair_weight(w,i,v,j):
    offset=(j-i)%6
    if w==v:
        return (-194,-194,-59,-14,-59,-194)[offset]
    cross=(-194,1,106,121,46,-119)
    if (w,v)==(0,2):
        offset=-offset
    if (w,v)==(1,2):
        offset-=1
    return cross[offset % 6]


def cyclic_certificate(graph):
    axes=list(combinations(range(6),2))
    required=0
    for a,b in combinations(range(3,39),2):
        w,i=divmod(a-3,12)
        v,j=divmod(b-3,12)
        demand=2-int(b in graph[a])-len(graph[a]&graph[b])
        assert demand>=0
        required+=demand*pair_weight(w,i//2,v,j//2)
    totals=[]
    for first,second,third in product(axes,repeat=3):
        i,j,k=map(set,(first,second,third))
        aligned=len(i&j)+len(i&k)+len({(s+1)%6 for s in j}&k)
        if aligned>1:
            continue
        contacts=[(w,z) for w,pair in enumerate((first,second,third)) for z in pair]
        totals.append(sum(pair_weight(w,x,v,y) for (w,x),(v,y) in combinations(contacts,2)))
    assert required==900 and len(totals)==1053 and max(totals)==0
    return required,len(totals),max(totals)


if __name__=="__main__":
    counts=Counter()
    for t,parts,graph in templates():
        counts[t]+=1
        if not t and len(parts)==1:
            print(parts,cyclic_certificate(graph))
    assert counts=={0:13,2:6,4:10,6:8}
    print("Covered triangle templates by prism count:",sorted(counts.items()))
