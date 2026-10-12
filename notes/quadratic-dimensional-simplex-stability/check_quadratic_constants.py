#!/usr/bin/env python3
"""Numerical regression checks; unrestricted proof is in the three markdown files."""
import math, json
rows=[]
for d in range(3,10001):
    n=d+1; C=n**3*(n+1); H=3*d*d*C
    root=math.exp(math.log(H)/(d-1))
    G=16*n*n*root
    assert C<4*d**4
    assert H<12*d**6
    assert G<=4096*d*d
    assert 1/(3*d*d)<1/(2*d)
    # In both endpoint regimes the global maximal-simplex bound is dominated.
    assert G/root>=n
    if d in [3,4,5,10,20,50,100,1000,10000]:
        rows.append(dict(d=d,C=C,H=H,G=G,G_over_d2=G/d**2,
            realized_lower=n*math.exp(math.log(d*n)/(d-1))))
# Relative-deficit union bound is checked on a wide grid.
for d in [3,4,10,100,1000]:
    for j in range(10001):
        r=(j/10001)
        actual=-math.expm1(math.log1p(-r)-d*math.log1p(r)-math.log1p(r/4))
        assert actual<=(d+1.25)*r+2e-14
        h=r/(2*d)
        assert (d+1.25)*r<=3*d*d*h+2e-14
print(json.dumps({'status':'PASS','dimensions_checked':'3..10000','relative_bound_grid':50005,'selected':rows},indent=2))
