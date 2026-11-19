"""Finite, exact sanity tests for trace counting, edit recovery and dotted extensions.
Python 3.10+ standard library. These are not proofs of limit theorems."""
from collections import Counter, defaultdict
from itertools import product,combinations,permutations
from functools import lru_cache
from math import comb,factorial

def need(x,label):
    if not x: raise ArithmeticError(label)

def cnt(w,s):
    return tuple(w.count(a) for a in range(s))

def trace(w, projections):
    return tuple(tuple(a for a in w if a in B) for B in projections)

def code(w,z,s):
    marks=tuple(i for i,(a,b) in enumerate(zip(w,z)) if a!=b)
    stops=(-1,)+marks+(len(w),)
    return (tuple((w[i],z[i]) for i in marks),
            tuple(cnt(w[i+1:j],s) for i,j in zip(stops,stops[1:])))

def decode(t,C,proj):
    changes,blocks=C
    dst=[]
    for B,old in zip(proj,t):
        out=[];lo=0
        for j,v in enumerate(blocks):
            n=sum(v[a] for a in B);out.extend(old[lo:lo+n]);lo+=n
            if j<len(changes):
                a,b=changes[j]
                if a in B:
                    need(old[lo]==a,'pair projection: marked old letter');lo+=1
                if b in B:out.append(b)
        need(lo==len(old),'projection end');dst.append(tuple(out))
    return tuple(dst)

def all_graphs():
    s=3; A=tuple(range(s)); pairs=tuple(combinations(A,2))
    ty=blocks=edits=0
    for mask in range(1<<len(pairs)):
        dep=[p for i,p in enumerate(pairs) if mask>>i&1]
        proj=tuple((a,) for a in A)+tuple(dep)
        cliques=[Q for k in range(1,s+1) for Q in combinations(A,k)
                 if all(p not in dep for p in combinations(Q,2))]
        @lru_cache(None)
        def count(v):
            if not any(v):return 1
            return sum((-1)**(len(Q)+1)*count(tuple(v[a]-(a in Q) for a in A))
                       for Q in cliques if all(v[a] for a in Q))
        for n in range(7):
            by=defaultdict(set)
            for w in product(A,repeat=n):
                by[cnt(w,s)].add(trace(w,proj))
            for v,ts in by.items():
                need(count(v)==len(ts),'multivariate clique recurrence');ty+=1
        table={}
        for w in product(A,repeat=6):
            key=(cnt(w[:3],s),trace(w,proj))
            value=(trace(w[:3],proj),trace(w[3:],proj))
            need(table.setdefault(key,value)==value,'two-block recovery');blocks+=1
        words=list(product(A,repeat=4))
        for w in words:
            old=trace(w,proj)
            for z in words:
                need(decode(old,code(w,z,s),proj)==trace(z,proj),'edit recovery');edits+=1
    print(f'All eight three-letter dependence graphs: {ty} exact type counts, {blocks} prescribed cuts, {edits} edit decodings.')

def empirical():
    # Test direct row/column encoding against sampled ordered centers in a weak-profile limit.
    # Different orientations cover both signs and all rows and columns; words may omit entire strips.
    A=((0,0),(0,1),(1,0),(1,1));tested=0
    for sx,sy in [((1,-1),(-1,1)),((-1,-1),(1,1)),((1,1),(1,1))]:
        for w in product(range(4),repeat=5):
            c=[A[a][0] for a in w];r=[A[a][1] for a in w]
            def ox(i):return (c[i],sx[c[i]]*i)
            def oy(i):return (r[i],sy[r[i]]*i)
            X,Y=[],[]
            for i in range(len(w)):
                for v,S,vals in [(c,sx,X),(r,sy,Y)]:
                    low=sum(t<v[i] for t in v)
                    depth=sum(t==v[i] for t in v[:i])
                    pos=depth if S[v[i]]==1 else v.count(v[i])-1-depth
                    vals.append(2*(low+pos)+1)  # midpoint numerator, denominator 2n
            for inds in combinations(range(len(w)),3):
                need(sorted(inds,key=ox)==sorted(inds,key=X.__getitem__) and
                     sorted(inds,key=oy)==sorted(inds,key=Y.__getitem__),'ordered restriction')
                tested+=1
    print(f'Signed strip pushforward, including zero cells: {tested} exact three-position restrictions.')

def deletion():
    cases=0
    for n in range(2,8):
        for j in range(1,min(3,n-1)+1):
            count=Counter()
            for w in permutations(range(n)):
                for inds in combinations(range(n),n-j):
                    sub=[w[i] for i in inds]
                    val={a:i for i,a in enumerate(sorted(sub))}
                    count[tuple(val[a] for a in sub)]+=1
            B=comb(n,j)**2*factorial(j)
            need(len(count)==factorial(n-j) and set(count.values())=={B},'marked extension bound')
            cases+=len(count)
    print(f'Dotted extension count bound attained with marked deletions in {cases} (n,j,pattern) cases.')

if __name__=='__main__':
    all_graphs();empirical();deletion()
