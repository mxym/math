#!/usr/bin/env python3
"""Fractions/recurrence verification of the primal and pointwise dual."""
from fractions import Fraction as F
from math import sqrt, floor

def row(n,s):
    y=[F(1),F(-s,n)]
    for j in range(1,n):
        y.append((-s*y[j]-j*y[j-1])/(n-j))
    return y

nt=nd=nc=ng=0
for n in tuple(range(6,38))+(46,62,63,64,65,95,96,127,128):
    grid=list(range(2+n%2,n+1,2))
    R={s:row(n,s) for s in range(-n,n+1,2)}
    for s in grid:
        x,y=F(s,n),F(s*s-n,n*(n-1))
        assert x+y>0
        for j in range(1,n+1):
            assert R[s][j] <= (j-2)*x+(j-1)*y
            nd+=1
    c0=F(1,n+n%2)
    caps={c0,F(1,2),(c0+F(1,2))/2}
    caps.update(F(1,2**k) for k in range(1,n.bit_length()+1) if F(1,2**k)>=c0)
    caps.update(c0+(F(1,2)-c0)*F(j,17) for j in (1,2,5,16))
    for c in caps:
        def constraint(s):
            x,y=F(s,n),R[s][2]
            return (c+(1-c)*y)/(x+y)
        s0=min(grid,key=constraint)
        u=constraint(s0)
        q=[c,u,1-c-u]
        assert sum(q)==1 and min(q)>=0
        for s0a in R:
            assert sum(x*y for x,y in zip(q,R[s0a]))>=0
            nc+=1
        dual_x,dual_y=F(s0,n),R[s0][2]
        dist=q[1]+2*q[2]
        assert -2*dual_x-dual_y+(dual_x+dual_y)*dist+(1+2*dual_x+dual_y)*c==0
        assert sum(x*y for x,y in zip(q,R[s0]))==0
        # Floating-point locator, checked against exact rational extrema.
        xstar=(float(c)+sqrt(max(0.,float(c-(1-c)/n))))/float(1-c)
        loc=(n*xstar-grid[0])/2
        g={grid[min(len(grid)-1,max(0,floor(loc)+d))] for d in (0,1)}
        assert min(map(constraint,g))==u
        ng+=1
        if c==F(1,8):
            assert n>=7 and dist<F(3,2)
        nt+=1
print("EXACT:",nt,"cap instances;",nd,"row-majorant inequalities;",nc,"exact primal inequalities")
print("EXACT:",ng,"two-neighbor checks; redundancy-three relaxation obstruction PASS")
