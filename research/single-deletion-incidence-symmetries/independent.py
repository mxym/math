"""Independent exact enumeration of color-preserving graph automorphisms.

Input graph is generated from raw deletion positions, no word order, weight,
reversal or other structural information is passed into the search.
Only at the end do we compare counts with the predicted closed form.
"""
from itertools import product
from collections import Counter
from math import factorial, comb

def check(ok, msg):
    if not ok:
        raise ValueError(msg)

def deletion_graph(q,n):
    words = list(product(range(q),repeat=n))+list(product(range(q),repeat=n-1))
    idx={w:i for i,w in enumerate(words)}
    adj=[set() for w in words]
    for i,w in enumerate(words[:q**n]):
        for k in range(n):
            j=idx[w[:k]+w[k+1:]]
            adj[i].add(j); adj[j].add(i)
    return adj,[len(w)==n for w in words]

def automorphisms(adj,colors):
    def search(x,y):
        while True:
            ids={}
            def refine(c):
                sig=[(c[i],tuple(sorted(c[j] for j in ns))) for i,ns in enumerate(adj)]
                return [ids.setdefault(v,len(ids)) for v in sig]
            a,b=refine(x),refine(y)
            groups=Counter(a)
            if groups!=Counter(b): return 0
            if len(groups)==len(set(x)): break
            x,y=a,b
        if len(groups)==len(adj):
            yi={v:j for j,v in enumerate(b)}
            p=[yi[v] for v in a]
            check(all({p[j] for j in row}==adj[p[i]] for i,row in enumerate(adj)),
                  'refined singleton match did not preserve graph')
            return 1
        _,v=min((cnt,v) for v,cnt in groups.items() if cnt>1)
        i=a.index(v); candidates=[j for j,val in enumerate(b) if val==v]
        fresh=max(a)+1; aa=a[:];aa[i]=fresh
        total=0
        for j in candidates:
            bb=b[:];bb[j]=fresh
            total+=search(aa,bb)
        return total
    return search(colors,colors)

def run():
    counter=0
    for q,ns in [(2,range(1,10)),(3,range(1,7)),(4,range(1,5))]:
        for n in ns:
            graph,colors=deletion_graph(q,n);ans=automorphisms(graph,colors)
            pred=factorial(q)*(1 if n==1 else (2**comb(q,2) if n==2 else 2))
            check(ans==pred,(q,n,ans,pred))
            print(f'q={q}, n={n}: {len(graph)} vertices, |Aut|={ans}')
            counter+=1
    print(f'PASS: {counter} exact graph-automorphism counts.')
if __name__=='__main__':run()
