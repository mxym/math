"""Independent maximal-clique reconstruction (standard library)."""
from collections import Counter
from primitive import An, gl32, asl23

def check(condition):
    if not condition:
        raise ValueError("census mismatch")

def mul(p,q):
    return tuple(p[k] for k in q)

for name, G, expected in [
    ("A5", An(5), {3:10, 4:20}),
    ("GL(3,2) = PSL(2,7)", gl32(), {3:28, 4:784}),
    ("A6", An(6), {5:60, 9:10}),
    ("ASL(2,3)", asl23(), {27:4}),
]:
    G=set(G)
    e=tuple(range(len(next(iter(G)))))
    V={p for p in G if p != e and mul(mul(p,p),p) == e}
    H={p:{q for q in V if mul(mul(p,p),q) in V} for p in V}
    def maximal(R,P,X):
        if not (P or X):
            yield R
            return
        u=max(P|X,key=lambda x:(len(P&H[x]),x))
        for v in sorted(P-H[u],reverse=True):
            yield from maximal(R|{v},P&H[v],X&H[v])
            P.remove(v)
            X.add(v)
    sizes=Counter()
    for K in maximal(set(),set(V),set()):
        L=set(K)|{e}
        sizes[len(L)]+=1
        if len(L)>=9:
            check(all(mul(p,q) in L for p in L for q in L))
    check(sizes==expected)
    print(name, dict(sorted(sizes.items())), "all large maximal cliques closed")
