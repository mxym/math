"""Optional third proof check, over Q[q]. Independent of both standard-library implementations."""
from collections import Counter
from functools import cache
from itertools import product
from math import factorial
from pathlib import Path
import json
import sympy
from sympy.polys.domains import QQ
from sympy.polys.rings import ring

R, q = ring("q", QQ)
def require(ok, detail):
    if not ok:
        raise ArithmeticError(detail)

@cache
def gaussian_factorial(n):
    p = R.one
    for j in range(1, n + 1):
        p *= sum(q**a for a in range(j))
    return p

@cache
def product_flags(d, fixed_n, ranks):
    # fixed_n=None means n=q^3. Distribute each rank increment among the factors.
    dg = tuple(y - x for x,y in zip((0,) + ranks, ranks))
    n = q**3 if fixed_n is None else R(fixed_n)
    total = R.zero
    for geom in product(*(range(i+1) for i in dg)):
        ag = sum(geom)
        if ag > d:
            continue
        aux = tuple(i-j for i,j in zip(dg,geom))
        ab = sum(aux)
        if fixed_n is not None and ab > fixed_n:
            continue
        term = gaussian_factorial(d).exquo(gaussian_factorial(d-ag))
        for i in geom:
            term = term.exquo(gaussian_factorial(i))
        for i in range(ab):
            term *= n-i
        for i in aux:
            term = term.quo_ground(factorial(i))
        total += term
    return total

@cache
def universal(r):
    # P,Z as rank-flag functionals; only proper, nonempty flat ranks get stored.
    if r == 0:
        return [Counter({(): 1})], [Counter({(): 1})]
    z = [Counter() for _ in range(r+1)]
    for f in range(1,r+1):
        pp = universal(r-f)[0]
        for j,row in enumerate(pp):
            for flag,coeff in row.items():
                z[f+j][((f,) if f < r else ()) + tuple(f+i for i in flag)] += coeff
    p = [Counter() for _ in range((r+1)//2)]
    for i,row in enumerate(p):
        row.update(z[r-i])
        row.subtract(z[i])
        z[i].update(row)
    return p,z

def check(k, reference):
    rank = k+3
    blocks = q**6
    for a in range(k):
        blocks *= q**3-a
    blocks = blocks.quo_ground(factorial(k))
    def flags(seq):
        ans = product_flags(6,None,seq)
        if seq and seq[-1] == rank-1:
            ans += blocks*(product_flags(3,k,seq[:-1])-product_flags(3,k,seq))
        return ans
    z = [sum((mult*flags(flag) for flag,mult in row.items() if mult),R.zero)
         for row in universal(rank)[1]]
    require(z == z[::-1] and z[0] == 1, ('not normalized/palindromic', rank))
    a,b,c = z[1:4]
    delta = b*b-a*c
    leads = [[v.degree(),str(v.LC)] for v in (a,b,c)]
    require(leads == reference[f'rank{rank}-leading-degrees-and-coefficients'], leads)
    require((delta.degree(), str(delta.LC)) ==
            ((35,'-1/72') if k == 3 else (41,'-1/360')), 'Turan leading term')
    for param in ((149,257) if k == 3 else (103,)):
        row = reference[f'rank{rank}-q{param}']
        vals = [v.evaluate(q,param) for v in (a,b,c,delta)]
        require(vals == [row[i] for i in ('z1','z2','z3','T2')] and vals[-1] < 0, vals)
    print('Verified symbolic Z and its leading terms, rank',rank)

if __name__ == '__main__':
    print('SymPy',sympy.__version__)
    fixture = json.loads(Path(__file__).with_name('certificate.json').read_text())
    for k in (3,4):
        check(k,fixture)
