"""Exact finite illustrations. No floating point, random samples, or dependencies."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import comb, lcm


def require(ok):
    if not ok:
        raise ArithmeticError('exact check failed')


def miss(group, requests, nonwin):
    # Track only teams short of their requirement; absorbing success drops out.
    pmf = {0: F(1)}
    for r in requests:
        p = nonwin[r]
        q = {}
        for s, w in pmf.items():
            q[s] = q.get(s, 0) + w*p
            if s+r < group:
                q[s+r] = q.get(s+r, 0) + w*(1-p)
        pmf = q
    return sum(pmf.values())


def main():
    total = equal = 0
    for group in range(1,6):
        k = group+1
        m = lcm(*range(1,k+1))
        for h in [m,2*m]:
            # t=m*log(1+1/h) strictly in (0,1), since log(1+1/h)<1/h.
            w = F(h,h+1)
            nonwin = {a:w**(m//a) for a in range(1,k+1)}
            for requests in combinations_with_replacement(range(1,k+1),group):
                f = miss(group,requests,nonwin)
                is_group_request = all(a==group for a in requests)
                require(f == w**m if is_group_request else f > w**m)
                total += 1
                equal += is_group_request
    print(f'Grouped finite-profile checks: {total}; group-request equalities: {equal}.')
    # t=2 log 3>1, g=20. An all-two deviation beats the all-twenty value 8/9.
    f = miss(20,[2]*20,{2:F(1,3)})
    require(f==F(sum(comb(20,j)*2**j for j in range(10)),3**20) and f < F(1,9))
    print(f'At t=2 log 3, g=20: all-two failure = {f} < 1/9 (group-request failure).')
    print('PASS. The analytic proof, not these examples, establishes the theorem.')


if __name__ == '__main__':
    main()
