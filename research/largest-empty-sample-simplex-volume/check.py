"""Finite witnesses for the vertex replacement and core-occupancy steps, not a proof of the limit."""
from fractions import Fraction as F
from itertools import permutations, product
from math import comb

def check(ok, msg):
    if not ok:
        raise ArithmeticError(msg)

def det(cols):
    # Fractional elimination on a copy. Transposition preserves determinant.
    a=[list(c) for c in cols]; v=F(1)
    for i in range(len(a)):
        p=next((j for j in range(i,len(a)) if a[j][i]),None)
        if p is None: return F(0)
        if p!=i: a[i],a[p]=a[p],a[i]; v=-v
        pivot=a[i][i]; v*=pivot
        for j in range(i+1,len(a)):
            h=a[j][i]/pivot
            for k in range(i+1,len(a)): a[j][k]-=h*a[i][k]
    return v

def corner_test(d):
    t=d+1; rho=F(1,5)
    # Three points in each corner, from outer vertex towards barycenter.
    ys=[tuple(tuple((1-h)*int(q==i)+h/F(t) for q in range(t))
              for h in (F(0),rho/2,rho)) for i in range(t)]
    total=bad=improves=0; minimum=None; count_min=0; min_empty=None
    for sel in product(*ys):
        v=det(sel)
        check(v>0,"orientation")
        occupied=False
        for j,group in enumerate(ys):
            for x in group:
                if x==sel[j]: continue
                nums=[det(sel[:k]+(x,)+sel[k+1:]) for k in range(t)]
                check(sum(nums)==v,"sum of Cramer numerators")
                if all(y>0 for y in nums):
                    occupied=True; check(0<nums[j]<v,"strict replacement")
                    improves+=1
        bad+=occupied; total+=1
        if minimum is None or v<minimum:
            minimum=v; count_min=1; min_empty=not occupied
        elif v==minimum: count_min+=1; min_empty=not occupied and min_empty
    check(min_empty and bad>0 and count_min==1,"minimum emptiness")
    check(minimum==(1-rho)**d,"homothetic minimum")
    return total,bad,improves

for d in (2,3):
    total,bad,dec=corner_test(d)
    print(f"d={d}: {total} selections, {bad} nonempty, {dec} strict matched-corner replacements, empty minimum.")

# Eight equiprobable cells, one forbidden core and three single-cell corners;
# compare direct enumeration of five labels with conditioning on core emptiness.
N,m,h=5,4,8; universe=range(h)
event=lambda v: 0 not in v and all(i in v[:m] for i in (1,2,3))
hit=sum(event(x) for x in product(universe, repeat=N))
exact=F(hit,h**N)
conditional=sum((-1)**j*comb(3,j)*F(h-1-j,h-1)**m for j in range(4))
check(exact==F(h-1,h)**N*conditional,"block event probability")
bound=F(h-1,h)**N*(1-3*F(h-2,h-1)**m)
check(exact>=bound,"union bound")
print(f"Block event: {h**N} sequences; exact probability {exact}, conditional formula agrees.")
