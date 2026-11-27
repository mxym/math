#!/usr/bin/env python3
"""Exact coverage and stress checks for the 50 ten-vertex four-box templates."""
from itertools import combinations, permutations, product
from collections import Counter, defaultdict

RIGID = {
    (0,1,2,3,4,5,6,7,8,15): [[2,5],[5,3],[7,3],[19,3],[35,3],[74,3],[76,3],[78,5],[86,9],[87,9]],
    (0,1,2,3,4,5,6,8,11,13): [[0,4],[1,6],[3,4],[9,4],[12,4],[28,10],[29,9],[38,3],[39,2],[40,2],[48,8],[49,4],[50,3],[58,3],[59,2],[60,2],[67,5],[69,6],[72,6],[73,6],[76,8],[77,7],[79,8],[80,7]],
    (0,1,2,3,4,5,6,9,10,12): [[0,4],[1,4],[5,4],[15,6],[16,6],[17,5],[28,6],[29,12],[43,3],[44,7],[45,3],[48,12],[49,12],[50,3],[63,5],[64,7],[71,7],[73,5],[75,6],[76,6],[79,6],[80,6],[83,6],[84,6]],
    (0,1,2,3,4,5,6,9,10,15): [[1,4],[4,6],[6,9],[12,10],[25,8],[31,3],[33,6],[39,5],[54,5],[55,2],[56,4],[57,3],[59,4],[60,2],[64,4],[65,3],[68,2],[72,6],[73,8],[76,6],[77,8],[80,7],[81,7]],
    (0,1,2,3,4,5,6,11,13,14): [[0,4],[1,4],[3,7],[4,4],[9,12],[10,6],[17,5],[19,5],[20,12],[21,12],[30,3],[36,7],[42,6],[43,6],[52,3],[55,7],[67,7],[75,6],[76,6],[79,6],[80,6],[83,6],[84,6]],
    (0,1,2,3,4,5,8,10,13,14): [[11,3],[22,7],[31,7],[37,2],[39,3],[41,3],[42,6],[43,2],[45,7],[56,2],[57,7],[59,8],[60,2],[61,7],[70,2],[74,7],[76,8],[77,7],[78,7],[81,7],[82,7]],
    (0,1,2,3,4,5,8,11,13,14): [[9,6],[10,7],[15,7],[24,2],[26,2],[28,6],[29,3],[32,3],[39,2],[40,6],[46,3],[49,4],[50,3],[54,4],[55,3],[60,4],[61,6],[66,4],[68,8],[71,6],[73,6],[76,6],[77,8]],
    (0,1,2,3,4,5,8,11,13,15): [[0,9],[8,9],[11,5],[29,5],[31,5],[36,5],[45,9],[51,10],[60,9],[61,5],[66,5],[69,4],[77,13],[81,10]],
    (0,1,2,3,4,7,8,11,12,15): [[0,9],[34,9],[44,3],[55,3],[60,3],[71,5],[76,5],[82,3],[83,3],[85,3]],
    (0,1,2,3,4,7,9,10,12,13): [[0,3],[1,2],[12,2],[26,4],[27,5],[28,7],[31,4],[33,6],[40,6],[42,8],[50,7],[51,4],[52,2],[55,6],[57,3],[62,6],[63,3],[64,4],[69,8],[71,3],[75,6],[76,4],[77,6]],
    (0,1,2,3,4,7,9,12,13,14): [[0,3],[4,5],[12,4],[17,6],[21,8],[25,2],[28,6],[30,4],[31,4],[33,10],[37,6],[38,7],[50,6],[52,4],[57,6],[58,2],[59,4],[63,5],[65,8],[69,3],[74,7],[79,4],[80,8]],
    (0,1,2,3,4,7,9,12,13,15): [[0,12],[3,7],[6,4],[9,6],[11,5],[23,4],[25,6],[27,12],[30,12],[32,7],[35,4],[37,6],[38,6],[51,6],[57,5],[62,3],[65,7],[66,6],[74,6],[76,6],[77,3],[81,6],[82,7]],
    (0,1,2,3,4,7,9,12,14,15): [[0,8],[3,6],[4,6],[11,9],[18,6],[19,6],[20,5],[23,3],[30,10],[32,4],[38,8],[51,8],[57,4],[59,4],[60,4],[64,7],[65,5],[69,2],[70,4],[71,3],[78,7],[80,2]],
    (0,1,2,4,7,9,10,11,12,13): [[0,2],[1,2],[2,8],[11,4],[19,4],[20,3],[21,8],[26,4],[27,10],[28,2],[33,4],[34,9],[35,3],[41,8],[51,2],[53,8],[57,9],[58,4],[59,2],[65,9],[68,8],[71,2],[72,4]],
    (0,1,2,4,7,9,10,11,13,14): [[1,9],[4,9],[6,2],[10,10],[18,2],[19,10],[27,10],[28,4],[32,8],[33,4],[34,4],[35,4],[41,2],[51,9],[55,2],[60,2],[61,2],[65,8],[68,4],[71,8],[73,4]],
    (0,1,2,4,7,9,10,13,14,15): [[3,3],[4,4],[6,3],[7,6],[8,4],[16,8],[17,6],[24,6],[26,5],[27,5],[33,6],[34,4],[38,7],[40,3],[41,2],[47,2],[49,5],[56,8],[64,6],[65,2],[69,2],[71,6],[72,4],[74,3]],
}

FLEX = {
    (0,1,2,3,4,5,6,7,8,11): [[0,3],[27,3],[39,3],[65,3],[68,3],[69,3],[70,3],[71,3]],
    (0,1,2,3,4,7,12,13,14,15): [[0,3],[27,3],[34,3],[35,3],[36,3],[37,3],[46,3],[71,3]],
    (0,1,2,3,4,9,12,13,14,15): [[8,3],[17,3],[20,3],[26,3],[47,3],[56,3],[64,3],[67,3]],
}

SPECIAL = (0,1,2,4,9,10,11,12,13,14)
X = tuple(product((0,1), repeat=4))
ID = {p: i for i,p in enumerate(X)}


def diff(a,b):
    return tuple(x-y for x,y in zip(a,b))


def add(a,b):
    return tuple(x+y for x,y in zip(a,b))


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def rank(rows, prime=101):
    if not rows:
        return 0
    a = [[v%prime for v in row] for row in rows]
    r = 0
    for c in range(len(a[0])):
        j = next((i for i in range(r,len(a)) if a[i][c]),None)
        if j is None:
            continue
        a[r],a[j]=a[j],a[r]
        inv=pow(a[r][c],-1,prime)
        a[r]=[(v*inv)%prime for v in a[r]]
        for i in range(r+1,len(a)):
            if a[i][c]:
                t=a[i][c]
                a[i]=[(x-t*y)%prime for x,y in zip(a[i],a[r])]
        r+=1
        if r==len(a):
            break
    return r


def witness_directions(S):
    by_dir=defaultdict(list)
    by_sum=defaultdict(list)
    for a,b in combinations(S,2):
        by_dir[diff(X[b],X[a])].append(X[a])
        by_sum[add(X[a],X[b])].append(diff(X[a],X[b]))
    for bases in by_dir.values():
        if rank([diff(x,bases[0]) for x in bases])==3:
            return 'segment-product'
    if any(rank(ds)==4 for ds in by_sum.values()):
        return 'central'
    return None


def prod33(S):
    for I in combinations(range(4),2):
        J=tuple(x for x in range(4) if x not in I)
        P={tuple(X[i][k] for k in I+J) for i in S}
        pats=tuple(product((0,1),repeat=2))
        for rows in combinations(pats,3):
            for cols in combinations(pats,3):
                if all(a+b in P for a,b in product(rows,cols)):
                    return True
    return False


def rectangle_rank(S):
    by_sum=defaultdict(list)
    for i,j in combinations(range(10),2):
        by_sum[add(X[S[i]],X[S[j]])].append((i,j))
    B=[]
    for pairs in by_sum.values():
        for (i,j),(k,l) in combinations(pairs,2):
            for u,v in [(i,j),(k,l)]:
                w=diff(X[S[u]],X[S[v]])
                row=[0]*40
                for g,s in ((i,1),(j,1),(k,-1),(l,-1)):
                    row[4*g:4*g+4]=[s*a for a in w]
                B.append(row)
    assert len(B)==30
    return rank(B)


def right(S):
    X0=[X[i] for i in S]
    return [(i,j,k) for j in range(10)
            for i,k in combinations((x for x in range(10) if x!=j),2)
            if dot(diff(X0[i],X0[j]),diff(X0[k],X0[j]))==0]


def filled_shapes(S):
    table=list(FLEX)
    assert len(table)==3
    kind=table.index(S)
    # Every forced angle numerator is homogeneous quadratic in the four
    # weights, so these ten tests find every coefficient. Three t values
    # suffice for the polynomial shifts; five slope values suffice for the
    # degree-at-most-four numerators of the planar-circle flex.
    E=[tuple(int(i==j) for i in range(4)) for j in range(4)]
    for a,b,c,d in E+[add(u,v) for u,v in combinations(E,2)]:
        base=[tuple(s*t for s,t in zip(X[i],(a,b,c,d))) for i in S]
        if kind<2:
            for t in range(3):
                Z=list(base)
                for j in ((8,9) if kind==0 else (4,5)):
                    Z[j]=add(Z[j],(0,b*t,0,0))
                yield Z
        else:
            for slope in range(5):
                R=1+slope*slope
                t=a*slope+d
                r=slope*t
                Z=[tuple(R*v for v in w) for w in base]
                Z[4]=(r,R*b,0,t)
                Z[5]=(R*a-r,0,0,R*d-t)
                yield Z


def verify_stress(S, isflex):
    selected=right(S)
    if isflex:
        tests=list(filled_shapes(S))
        selected=[(i,j,k) for i,j,k in selected if all(
            dot(diff(Z[i],Z[j]),diff(Z[k],Z[j]))==0 for Z in tests)]
        assert len(selected)==72
    cert=dict((FLEX if isflex else RIGID)[S])
    assert all(0<=x<len(selected) and w>0 for x,w in cert.items())
    G=[]
    X0=[X[i] for i in S]
    for i,j,k in selected:
        u,v=diff(X0[i],X0[j]),diff(X0[k],X0[j])
        row=[0]*40
        row[4*i:4*i+4]=v
        row[4*k:4*k+4]=u
        row[4*j:4*j+4]=[-x-y for x,y in zip(u,v)]
        G.append(row)
    assert rank(G)==(25 if isflex else 26)
    assert all(sum(cert.get(i,1)*g[c] for i,g in enumerate(G))==0 for c in range(40))


def main():
    group=[[ID[tuple(x[p]^f for p,f in zip(perm,flip))] for x in X]
           for perm in permutations(range(4)) for flip in X]
    seen=set()
    cnt=Counter()
    for S in combinations(range(16),10):
        if S in seen:
            continue
        seen.update(tuple(sorted(g[i] for i in S)) for g in group)
        assert rank([diff(X[i],X[S[0]]) for i in S[1:]])==4
        w=witness_directions(S)
        if w:
            cnt[w]+=1
        elif prod33(S):
            cnt['triangle-product']+=1
        elif S in RIGID or S in FLEX:
            verify_stress(S,S in FLEX)
            cnt['flex' if S in FLEX else 'rigid']+=1
        else:
            assert S==SPECIAL and rectangle_rank(S)==20, S
            cnt['rectangle']+=1
    assert len(seen)==8008
    assert cnt==Counter({'segment-product':23,'central':6,'triangle-product':1,
                        'rigid':16,'flex':3,'rectangle':1}), cnt
    print('PASS: 8008 subsets in 50 orbits; all six exact certificate classes verified.')


if __name__=='__main__':
    main()
