"""Unlabeled norm-18 support shapes with named sign sides (no graph assumed).
Enumerate multisets of 9 column words, recursively appending weight-four rows.
Refine symmetrically then individualize rows; once rows are fixed columns are
handled by sorting. Every child of each isomorphism class is considered.
"""
from itertools import combinations
from collections import Counter


def transpose(v, n):
    return tuple(sum(1<<j for j,w in enumerate(v) if w>>i&1) for i in range(n))


def canonical(v,n):
    rows=transpose(v,n)
    def search(colors):
        while True:
            k=max(colors)+1
            ccol=[tuple(sum(w>>i&1 for i in range(n) if colors[i]==c)
                        for c in range(k)) for w in v]
            rank={x:j for j,x in enumerate(sorted(set(ccol)))}
            col=[rank[x] for x in ccol]
            sig=[(colors[i],tuple(sorted(col[j] for j in range(9) if r>>j&1)))
                 for i,r in enumerate(rows)]
            rank={x:j for j,x in enumerate(sorted(set(sig)))}
            new=tuple(rank[x] for x in sig)
            if new==colors:break
            colors=new
        classes=[[j for j in range(n) if colors[j]==c] for c in sorted(set(colors))]
        nonsingle=[x for x in classes if len(x)>1]
        if nonsingle:
            return min(search(tuple(max(colors)+1 if i==j else c for i,c in enumerate(colors)))
                       for j in min(nonsingle,key=len))
        order=[i for c in classes for i in c]
        return tuple(sorted(sum((w>>j&1)<<i for i,j in enumerate(order)) for w in v))
    return search((0,)*n)


def children(v,n):
    rows=transpose(v,n)
    for h in combinations(range(9),4):
        # Each choice from an equal-column block can use its initial segment.
        if any(j and v[j]==v[j-1] and j-1 not in h for j in h):continue
        mask=sum(1<<j for j in h)
        if any((r&mask).bit_count()>2 for r in rows):continue
        w=tuple(sorted(u+((j in h)<<n) for j,u in enumerate(v)))
        if any(not (n-4<=r.bit_count()<=4) for r in w):continue
        if any((x&y).bit_count()>2 for x,y in combinations(w,2)):continue
        yield w


def main():
    catalog={(0,)*9}
    for n in range(9):
        raw={w for v in catalog for w in children(v,n)}
        catalog={canonical(w,n+1) for w in raw}
    counts=Counter()
    for v in catalog:
        score=lambda side:sum(any(i!=j and x&y==0 for j,y in enumerate(side))
                              for i,x in enumerate(side))
        counts[tuple(sorted((score(v),score(transpose(v,9)))))]+=1
    assert counts=={(0,0):9,(2,2):6,(4,4):7,(6,6):3,(8,8):1}
    print('26 support types:',sorted(counts.items()))

if __name__=='__main__': main()
