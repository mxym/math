#!/usr/bin/env python3
"""Exact checks for the near-singular antiperiodic cutoff."""
from fractions import Fraction as F
from itertools import product


def prefix(x):
    u = [F(x[0]-sum(x[1:]),2)]
    for j in x[1:]:
        u.append(u[-1]+j)
    return tuple(u)


def charges(u):
    return (u[0]+u[-1],)+tuple(u[i]-u[i-1] for i in range(1,len(u)))


def entries(d,r):
    return [[(r**abs(i-j)-r**(d-abs(i-j)))/(1+r**d)
             for j in range(d)] for i in range(d)]


def bilinear(A,x,y):
    return sum(a*b*A[i][j] for i,a in enumerate(x) for j,b in enumerate(y))


def matrix_check(d,r):
    e = 1-r
    K = entries(d,r)
    c = (1+r)/(2*r)
    H = [[c*((i==j)-e/(1+r)*K[i][j]) for j in range(d)] for i in range(d)]
    E = [tuple(int(i==j) for j in range(d)) for i in range(d)]
    for i,j in product(range(d),repeat=2):
        assert bilinear(K,charges(E[i]),charges(E[j]))/(2*e)==H[i][j]
    return d*d


def branch_check():
    count = 0
    for d in (2,4,6):
        for x in product(range(-2,3),repeat=d):
            u = prefix(x)
            assert charges(u) == x
            residues = {z%1 for z in u}
            assert residues in ({F(0)},{F(1,2)})
            assert next(iter(residues)) == F(sum(x)%2,2)
            count += 1
    for d in (4,6,8):
        for j in range(d):
            u = tuple(int(i==j) for i in range(d))
            x = charges(u)
            assert len([v for v in x if v]) == 2
            assert x[j] == 1 and x[(j+1)%d] == (1 if j==d-1 else -1)
            assert prefix(x) == u
    return count


def line(r,s,positions):
    return sum(a*b*r**abs(positions[i]-positions[j])
               for i,a in enumerate(s) for j,b in enumerate(s))


def gaps_check():
    count = 0
    for r in (F(3,4),F(9,10),F(99,100),F(999,1000)):
        e = 1-r
        for g,h,i in product(range(1,8),repeat=3):
            a,b,c = r**g,r**h,r**i
            p = (0,g,g+h,g+h+i)
            expected = (2*(1-a)+2*(1-c)-2*b*(1-a)*(1-c),
                        2*(1-a)+2*(1-c)+2*b*(1-a)*(1-c),
                        4+2*(a+c)-2*b*(1+a)*(1+c))
            for s,v in zip(((1,-1,1,-1),(1,-1,-1,1),(1,1,-1,-1)),expected):
                assert line(r,s,p) == v and v/(2*e) >= F(5,4)
                count += 1
        for h in range(1,8):
            v=line(r,(1,-1),(0,h))/(2*e)
            assert (v==1 if h==1 else v>=1+r)
    return count


if __name__=="__main__":
    m=sum(matrix_check(d,r) for d,r in product((4,6,8,12),(F(1,2),F(3,4),F(99,100))))
    b,g=branch_check(),gaps_check()
    print(f"PASS: {m} exact prefix matrix entries, {b} integer/half-integer branches, "
          f"{g} four-charge gap checks and wrap signs")
