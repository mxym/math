"""Exact vertex certificate for the rank-six reflected midpoint bound."""
from fractions import Fraction as F
from itertools import combinations

N = 6
ZERO = (0,)*N
ONE = (1,)*N

def vec(i, v=1, j=None, w=1):
    a = list(ZERO)
    a[i] = v
    if j is not None:
        a[j] = w
    return tuple(a)

def vertex(rows):
    a = [[F(x) for x in co]+[F(r)] for co,r in rows]
    for i in range(N):
        j = next((j for j in range(i,N) if a[j][i]),None)
        if j is None:
            return None
        a[i],a[j] = a[j],a[i]
        t = a[i][i]
        a[i] = [u/t for u in a[i]]
        for j in range(N):
            if j != i:
                r = a[j][i]
                if r:
                    a[j] = [u-r*v for u,v in zip(a[j],a[i])]
    return tuple(a[i][-1] for i in range(N))

def pair(i,j,sgn=1):
    return vec(i,sgn,j,sgn), F(sgn,2)

def c6(x):
    def low(t):
        return min(t,1-t)
    # Triple partitions are represented uniquely by the side containing x[0].
    return (-1+sum(low(sum(y)) for y in combinations(x,2))
               -sum(low(x[0]+sum(y)) for y in combinations(x[1:],2)))

base = ([(vec(0,-1),0)]+[(vec(i,1,i+1,-1),0) for i in range(N-1)]
        +[(vec(N-1),F(1,2))])
cases = [('empty',[pair(4,5)],9,F(1,4))]
star_counts = [6,6,6,7,8]
for j in range(5):
    co = [pair(3,4),pair(j,5,-1)]
    if j:
        co.append(pair(j-1,5))
    cases.append((f'star {j+1}',co,star_counts[j],F(1,4)))
cases.append(('triangle',[pair(3,4,-1),pair(2,5)],6,F(0)))
for name,extra,want_count,want_max in cases:
    ineq = base+extra
    points = set()
    for active in combinations(ineq,N-1):
        x = vertex([(ONE,1),*active])
        if x is not None and all(sum(u*v for u,v in zip(a,x))<=b for a,b in ineq):
            points.add(x)
    got = (len(points),max(map(c6,points),default=None))
    if got != (want_count,want_max):
        raise ArithmeticError((name,got,want_count,want_max))
    print(name,got)
