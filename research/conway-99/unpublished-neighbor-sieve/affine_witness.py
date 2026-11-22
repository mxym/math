"""Verify the short affine-eigenvector identity in the rank-52 A8 gluing.

Requires python-flint. All coefficients and row operations are rational.
"""
from collections import Counter, defaultdict
from functools import cache
from itertools import product
from math import comb, isqrt

from flint import fmpq as Q, fmpq_mat as Matrix

CUTOFF = 20


def character(n):
    return (0, 1, 1, -1, 1, -1, -1)[n % 7]


@cache
def bernoulli(k):
    if k == 0:
        return Q(1)
    return -sum(comb(k+1, i)*bernoulli(i) for i in range(k))/(k+1)


@cache
def eisenstein(k, orientation):
    constant = Q(0)
    if orientation:
        constant = -Q(7**(k-1), 2*k) * sum(
            character(a)*comb(k,i)*bernoulli(i)*Q(a,7)**(k-i)
            for a in range(1,7) for i in range(k+1))
    return [constant] + [
        sum(d**(k-1)*character(d if orientation else n//d)
            for d in range(1,n+1) if n % d == 0) for n in range(1,CUTOFF+1)]


def convolve(a, b):
    return [sum(a[i]*b[n-i] for i in range(n+1)) for n in range(CUTOFF+1)]


def cusp_space(degree):
    weight = 26 + degree
    rows = []
    for a in range(3,weight//2+1,2):
        b = weight-a
        for p,q in product((0,1), repeat=2):
            first = convolve(eisenstein(a,p), eisenstein(b,q))
            other = convolve(eisenstein(a,1-p), eisenstein(b,1-q))
            scale = Q(7)**(12+(2*p-1)*((a-1)//2)+(2*q-1)*((b-1)//2))
            rows.append([v for x,y in zip(first,other) for v in (x,scale*y)])
    mat, rank = Matrix(rows).rref()
    assert rank == 1 + 2*(weight//3)
    return mat, rank


def admissible(a, j, side):
    rate = 1 if side == 1 else 7
    if (j-rate*5*a*a) % 9:
        return False
    mass, remainder = divmod(14*j//rate + 11*a*a, 9)
    assert not remainder
    if mass < 11*a or (mass-11*a) % 2:
        return False
    return a != 0 or mass == 0 or mass >= 14


def variables():
    return [(a,j,s) for s in (0,1) for a in range(5) for j in range(9*CUTOFF+1)
            if j+(1 if s else 7)*a*(9-a)//2 <= 9*CUTOFF and admissible(a,j,s)]


@cache
def partial_sums(number, limit):
    ways = {(0,0):1}
    for _ in range(number):
        new = Counter()
        for (total,norm),count in ways.items():
            bound = isqrt(limit-norm)
            for z in range(-bound,bound+1):
                new[total+z,norm+z*z] += count
        ways = new
    return ways


@cache
def a8_moments(a):
    limit = (18*CUTOFF+a*a)//9
    shells = defaultdict(lambda:[0]*9)
    for (total, norm), count in partial_sums(8,limit).items():
        first = a-total
        if norm+first*first > limit:
            continue
        r = (9*(norm+first*first)-a*a)//2
        pairing = 9*first-a
        for k in range(0,9,2):
            shells[r][k] += count*pairing**k
    return shells


def harmonic_rows(keys, degree):
    ix = {v:i for i,v in enumerate(keys)}
    mat, rank = cusp_space(degree)
    pivots = [next(j for j in range(mat.ncols()) if mat[i,j]) for i in range(rank)]
    coords = []
    for n in range(CUTOFF+1):
        for side in (0,1):
            rate = 1 if side else 7
            row = [Q(0)]*(len(keys)+1)
            for a in range(5):
                for r,powers in a8_moments(a).items():
                    j = 9*n-rate*r
                    idx = ix.get((a,j,side))
                    if idx is None:
                        continue
                    coefficient = Q(1)
                    for i in range(degree//2+1):
                        m = degree-2*i
                        row[idx] += (1 if not a else 2)*coefficient*(144*n)**i*rate**(m//2)*powers[m]
                        if m:
                            coefficient *= Q(-m*(m-1),2*(i+1)*(52+2*degree-2*i-4))
            coords.append(row)
    for j,row in enumerate(coords):
        if j in pivots:
            continue
        yield [v-sum(mat[t,j]*coords[p][i] for t,p in enumerate(pivots) if mat[t,j])
               for i,v in enumerate(row)]


def check_rank_average():
    # Start with x^2 + y^2 over F_7, then adjoin xy one plane at a time.
    plane = Counter((x*y) % 7 for x,y in product(range(7), repeat=2))
    counts = Counter((x*x+y*y) % 7 for x,y in product(range(7), repeat=2))
    constants = []
    for m in range(1,5):
        size = 7**(m-1)
        assert counts[0]-1 == (7**m+1)*(size-1)
        for s in range(1,7):
            assert counts[s] == 7**(2*m-1)+size
            assert Q(8*size,counts[s]) == Q(8,7**m+1)
        constants.append(98*(7**m+1))
        counts = Counter({s: sum(counts[t]*plane[(s-t) % 7] for t in range(7))
                          for s in range(7)})
    assert constants == [784,4900,33712,235396]
    assert constants[-1]-2*(77616+24*851) == 39316


def main():
    keys = variables()
    ix = {k:i for i,k in enumerate(keys)}
    rows = []
    for side in (0,1):
        row = [0]*(len(keys)+1)
        row[ix[0,0,side]], row[-1] = 1,-1
        rows.append(row)
    for a,j,side in keys:
        if side and (a,7*j,0) in ix:
            row = [0]*(len(keys)+1)
            row[ix[a,j,1]],row[ix[a,7*j,0]] = 1,-1
            rows.append(row)
    for degree in range(0,9,2):
        rows.extend(harmonic_rows(keys,degree))
    # X counts are per charge, over all 7-primary classes. The final entry
    # is the constant in an affine equation with right side zero.
    terms = {(0,108,0):1, (1,107,0):2, (2,86,0):2, (2,104,0):1,
             (1,14,1):-8, (0,81,0):-2, (1,62,0):-2, (1,71,0):-2,
             (1,80,0):-1, (2,95,0):-2, (3,108,0):-1, (4,110,0):-1,
             (1,44,0):84, (1,53,0):2}
    target = [terms.get(k,0) for k in keys]+[8]
    assert set(terms) <= set(keys)
    basis, rank = Matrix(rows).rref()
    for t in range(rank):
        j = next(j for j in range(basis.ncols()) if basis[t,j])
        multiple = target[j]
        if multiple:
            target = [x-multiple*basis[t,i] for i,x in enumerate(target)]
    assert not any(target)
    assert all(j % 7 for (a,j,s) in terms if s == 0)
    check_rank_average()
    print(f"Verified the identity in {len(keys)} shell variables using {rank} independent equations.")
    print("Verified the finite quadratic-space counts for ranks 36, 38, 40 and 42.")


if __name__ == "__main__":
    main()
