from fractions import Fraction as F
from itertools import product,combinations
from math import prod
if not __debug__:
    raise SystemExit("Certificate assertions require ordinary Python (no -O or -OO).")
for n,diag,off,expected in [(4,-1,1,(F(1,4),F(-1,2))),(9,1,F(-1,8),(F(1,512),F(21,16384)))]:
    vals=[]
    for edges in [[(0,1),(1,2),(2,3),(3,0)],list(combinations(range(4),2))]:
        s=sum(prod(diag if v[i]==v[j] else off for i,j in edges) for v in product(range(n),repeat=4))
        vals.append(F(s,n**4))
    assert tuple(vals)==expected;print(n,vals)
