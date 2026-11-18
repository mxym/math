"""Check the deterministic MIS representation and test-avoidance reduction exhaustively.
Not a substitute for the asymptotic probability bounds. Python standard library.
"""
from itertools import product
def require(x):
    if not x: raise ArithmeticError("disagreement")
def test(m,l,L):
    q=m*l
    n=q+L
    full=(1<<n)-1
    core=(1<<q)-1
    reservoir=full^core
    cl=[((1<<l)-1)<<(l*j) for j in range(m)]
    edges=[(j,k) for j in range(q) for k in range(q,n)]
    full_reps=[sum(1<<(j*l+v) for j,v in enumerate(idx)) for idx in product(range(l),repeat=m)]
    nmis=0
    for bits in range(1<<len(edges)):
        neigh=[0]*n
        for j in range(q): neigh[j]=cl[j//l]^(1<<j)
        for i,(j,k) in enumerate(edges):
            if bits>>i&1: neigh[j]|=1<<k;neigh[k]|=1<<j
        nbr=[0]*(1<<n)
        for v in range(1,1<<n):
            vmin=v&-v
            nbr[v]=nbr[v^vmin]|neigh[vmin.bit_length()-1]
        independent=[v for v in range(1<<n) if not v&nbr[v]]
        # Compare two distinct definitions: among all independent sets, no single
        # extension exists; separately reconstruct maximal sets from clique parts.
        maximal={v for v in independent if not any((v|(1<<i)) in independent
                      for i in range(n) if not v>>i&1)}
        partial=list(v for v in range(1<<q) if all((v&c).bit_count()<=1 for c in cl))
        reconstructed=set()
        for s in partial:
            j=s|(reservoir & ~nbr[s])
            if (core & ~(j|nbr[j]))==0: reconstructed.add(j)
        require(reconstructed==maximal)
        require(len({j&core for j in maximal})==len(maximal)<=(l+1)**m)
        nmis+=len(maximal)
        complete={j for j in maximal if all(j&c for c in cl)}
        for t in range(1<<n):
            brute=any(not (t&j) for j in complete)
            direct=any(not (t&core&s) and (t&reservoir&~nbr[s])==0 for s in full_reps)
            require(brute==direct)
    graphs=1<<len(edges)
    print(f'PASS m={m}, clique size={l}, reservoir={L}: {graphs} graphs, '
          f'{graphs*(1<<n)} mixed tests, {nmis} maximal sets')
for size in [(2,2,2),(3,1,2),(2,2,3)]: test(*size)
