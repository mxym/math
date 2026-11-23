"""Clean-square participation check for the final simple eleven-grid core.

Read eleven-grid-simple-closure.md. This independently tests all row decks
on the one remaining axis shape and its three Gram menus; it does not
assign graph edges. The analytic square sum and BX-center contradiction
are in the note.
"""
from itertools import product, combinations_with_replacement
from functools import lru_cache
# The preceding certificate gives the dirty-cell fields and shared groups.
from eleven_grid_axis_moments import choose, shape, gram, plus, times, E

a,b,c,d,x,y,z = range(7)
PATHS = (
    (a,d), (a,x,b), (a,y,z,c), (b,c), (b,d), (c,x,d)
)
D, G = choose('K', PATHS)
COORDS = tuple(product(range(-2,3),range(-2,3),range(-1,2)))
ENTRIES = tuple(combinations_with_replacement(range(3),2))

def bound(e,f,degree):
    if e == f:
        return degree-2, degree-2
    common = set(e)&set(f)
    if not common:
        return -1,3
    s, = common
    return (0,2) if e in D and G[e,s] == G[f,s] else (0,0)

def moment(row):
    return tuple(row[i]*row[j] for i,j in ENTRIES)

@lru_cache(maxsize=None)
def decks(e, degrees, target):
    choices = []
    for d0 in degrees:
        B = [(vec,*bound(e,f,d0)) for f,vec in D.items()]
        choices.append([row for row in COORDS
                        if all(lo <= times(row,v) <= hi for v,lo,hi in B)])
    result = {}
    for rows in product(*choices):
        if plus(*rows) != target:
            continue
        result.setdefault(plus(*(moment(r) for r in rows)),set()).add(tuple(sorted(rows)))
    return result

def profiles(E,M,e):
    if e in D:
        v = D[e]
        m = 4-gram(v,M,v)//2
        target = tuple(-sum(M[i][j]*v[j] for j in range(3)) for i in range(3))
        L = shape(m)
    else:
        target = (0,0,0)
        L = ((2,2,2,2),)
    out = {}
    for deg in L:
        for mom,rows in decks(e,deg,target).items():
            out.setdefault(mom,set()).update(rows)
    return out

def can_sum(choices, target):
    L = sorted(choices,key=len)
    lo, hi = [(0,)*6], [(0,)*6]
    for C in L[::-1]:
        lo.append(tuple(lo[-1][i]+min(row[i] for row in C) for i in range(6)))
        hi.append(tuple(hi[-1][i]+max(row[i] for row in C) for i in range(6)))
    @lru_cache(maxsize=None)
    def search(j,rem):
        n = len(L)-j
        if any(v<lo[n][i] or v>hi[n][i] for i,v in enumerate(rem)):
            return False
        if not n:
            return True
        return any(search(j+1,tuple(v-w for v,w in zip(rem,r))) for r in L[j])
    return search(0,target)

def check(alpha,beta):
    M = ((alpha,0,-2),(0,beta,-2),(-2,-2,4))
    mats = [profiles(E,M,e) for e in E]
    target = tuple(7*M[i][j] for i,j in ENTRIES)
    true = {}
    for i,e in enumerate(E):
        part = set()
        for m,rows in mats[i].items():
            if can_sum(mats[:i]+mats[i+1:],tuple(t-u for t,u in zip(target,m))):
                part.update(rows)
        assert part
        true[e] = part
    for e in E:
        if e in D:
            continue
        for rows in true[e]:
            assert all(r[2] == 0 for r in rows)
            assert e==(c,y) or all(r[0] == 0 for r in rows)
            assert e==(a,z) or all(r[1] == 0 for r in rows)
    p_sq = {sum(r[0]**2 for r in row) for row in true[c,y]}
    t_sq = {sum(r[1]**2 for r in row) for row in true[a,z]}
    assert p_sq == ({2,4} if alpha==4 else {4})
    assert t_sq == ({2,4} if beta==4 else {4})
    for rows in true[c,y]:
        assert all(-1 <= r[0] <= 1 for r in rows)
    for rows in true[a,z]:
        assert all(-1 <= r[1] <= 1 for r in rows)
    print((alpha,beta),sorted(p_sq),sorted(t_sq))

if __name__=='__main__':
    for alpha,beta in ((4,4),(4,6),(6,4)):
        check(alpha,beta)
