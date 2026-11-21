#!/usr/bin/env python3
"""Exact rail corners and finite sharp canonical-order/neck checks (works under -O)."""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod


def require(ok, context):
    if not ok:
        raise AssertionError(context)


def check_rails():
    theta = F(7,32)
    eps = F(4,10000)
    axes = [('0.10','0.14'),('0.088','0.098'),('0.116','0.236'),
            ('0.4999','0.5001'),('0','0.0001')]
    maxima = [F(0) for _ in range(4)]
    for sig,a,b,t,l in product(*[list(map(F, vals)) for vals in axes]):
        c = t-a-b
        require(c>0, (sig,a,b,t,l))
        require(sig+c-b>0, ('theta monotonicity',sig,a,b,t,l))
        w = (a+l,2*sig+b+2*c,theta+sig+a+l+5*b+2*c,
             sig+a+l+5*b+2*c+2*theta*(sig+c-b))
        maxima = [max(x,y) for x,y in zip(maxima,w)]
        require(w[0] < sig-eps, ('first',w))
        require(w[1] < 1-8*eps, ('second',w))
        require(w[2] < 2-15*eps, ('third',w))
        require(w[3] < 2-15*eps, ('fourth',w))
    require(maxima == list(map(F,['.0981','.9882','1.97905','1.79534375'])),maxima)
    return maxima


def check_order():
    # Integer labels model exact prime-order comparisons, not asymptotic size.
    count = 0
    for n in range(4,8):
        for ps in combinations([2,3,5,7,11,13,17,19],n):
            for s1,s2 in product([2,4,5,15],[3,7,11,21]):
                i = next((j for j in range(1,n+1) if prod(ps[:j]) >= s1),n+1)
                j = next((j for j in range(i+1,n+1) if prod(ps[i:j]) >= s2),n+1)
                if j>=n:
                    continue
                groups=ps[:i],ps[i:j],ps[j:]
                a,b,c=(prod(g) for g in groups)
                require(prod(ps)==a*b*c,groups)
                require(a//max(groups[0]) < s1 <= a,groups)
                require(b//max(groups[1]) < s2 <= b,groups)
                require(max(groups[0]) < min(groups[1]) and max(groups[1]) < min(groups[2]),groups)
                count += 1
    return count


if __name__ == '__main__':
    print(f'32 exact rail corners {check_rails()}, {check_order()} canonical integer cases')
