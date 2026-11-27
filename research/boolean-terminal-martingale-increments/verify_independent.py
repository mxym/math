#!/usr/bin/env python3
"""Checks on rational, branch-dependent probability spaces (not dyadic trees)."""
from fractions import Fraction as F
from itertools import product


def verify(n, split, terminal, thresholds):
    leaves=tuple(product((0,1),repeat=n))
    mass={():F(1)}
    rows={0:[()]}
    for i in range(n):
        rows[i+1]=[]
        for h in rows[i]:
            p=split(h)
            for b,c in enumerate((1-p,p)):
                j=h+(b,)
                rows[i+1].append(j)
                mass[j]=mass[h]*c
    assert sum(mass[l] for l in leaves)==1
    x=dict(zip(leaves,terminal))
    for i in range(n-1,-1,-1):
        for h in rows[i]:
            x[h]=sum(mass[h+(b,)]*x[h+(b,)] for b in (0,1))/mass[h]
    if x[()]>F(1,2):
        x={h:1-t for h,t in x.items()}
    mu=x[()]
    V=lambda x:x*(1-x)
    v=sum(mass[l]*V(x[l]) for l in leaves)
    paths={l:[x[l[:i]] for i in range(n+1)] for l in leaves}
    d={l:[abs(path[j]-path[j-1]) for j in range(1,n+1)] for l,path in paths.items()}
    hits={l:next((i for i,q in enumerate(p) if q>=F(1,2)),n+1)
          for l,p in paths.items()}
    hit=sum(mass[l] for l in leaves if hits[l]<=n)
    assert hit>=mu-2*v
    positive=condchecks=exact_gap=0
    for a in thresholds:
        theta=F(1,4)-(n+1)*a*a
        assert theta>0
        gap=sum(mass[l] for l in leaves if max(d[l])>=a)
        assert gap>=max(0, theta*mu-(1+2*theta)*v)
        positive+=int(theta*mu-(1+2*theta)*v>0)
        exact_gap+=sum(a in d[l] for l in leaves)
        # Conditional weighted energy via explicit leaf sums at each node.
        for i,level in rows.items():
            for h in level:
                acc=check_future=end=F(0)
                for l in leaves:
                    if l[:i]!=h:
                        continue
                    ds=d[l]
                    t=next((j for j in range(i+1,n+1) if ds[j-1]>=a),n)
                    e=sum(s*s for s in ds[i:t])+V(paths[l][t])
                    acc+=mass[l]*e
                    end+=mass[l]*V(paths[l][-1])
                    check_future+=mass[l]*any(z>=a for z in ds[i:])
                assert acc==mass[h]*V(x[h])
                assert acc<=mass[h]*(n-i)*a*a+end+check_future
                condchecks+=1
    return positive,condchecks,exact_gap


p1=lambda h:F(1,3) if not h else (F(1,4) if h[-1]==0 else F(2,5))
p2=lambda h:F(2,3) if not h else (F(3,5) if h[-1]==0 else F(5,7))
grid=(F(0),F(1,8),F(1,2),F(7,8),F(1))
trees=positive=conditions=equal=0
for law in (p1,p2):
    for t in product(grid,repeat=4):
        a,b,c=verify(2,law,t,(F(1,8),F(1,6)))
        trees+=1; positive+=a; conditions+=b; equal+=c
    for t in product((F(0),F(1)),repeat=8):
        a,b,c=verify(3,law,t,(F(1,8),F(1,6)))
        trees+=1; positive+=a; conditions+=b; equal+=c

# Three- to five-step stochastic examples with dust inside (0,1).
# Terminal labels are deterministic arithmetic patterns, not random samples.
for n in (3,4,5):
    for s in range(29):
        t=tuple(grid[(i*i+(s+1)*i+s*s+i//3)%len(grid)] for i in range(1<<n))
        a,b,c=verify(n,p1,t,(F(1,8),F(1,10)))
        trees+=1; positive+=a; conditions+=b; equal+=c

# Equality is observable, including the very last step, on a non-Boolean
# martingale moving by exactly 1/8 on either outcome. Verify separately.
assert verify(1,lambda h:F(1,2),(F(0),F(1,4)),(F(1,8),))[2]==2

print(f"PASS independent: {trees} branch-dependent rational trees; "
      f"{conditions} stopped conditional identities, {positive} positive impurity "
      f"bounds, {equal} threshold-equality paths; first/last exact-gap control")
