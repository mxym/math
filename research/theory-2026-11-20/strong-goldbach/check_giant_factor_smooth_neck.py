#!/usr/bin/env python3
"""Exact moving rail corner checks for the high-atom modulus chart."""
from fractions import Fraction as F
from itertools import product


def require(truth, context):
    if not truth:
        raise AssertionError(context)


if __name__ == '__main__':
    theta, eps = F(7,32), F('.0002')
    params = [('0.10','0.14'),('0.088','0.098'),('0.4999','0.5001'),('0','0.0001')]
    maxima = [F(0) for _ in range(4)]
    bmin = F(1)
    corners = 0
    for sig,a,t,ell in product(*[list(map(F, p)) for p in params]):
        for c in [F('.236'), F('.585')-2*sig]:
            b=t-a-c
            bmin=min(bmin,b)
            corners+=1
            vals=(a+ell,2*sig+b+2*c,theta+sig+a+ell+5*b+2*c,
                  sig+a+ell+5*b+2*c+2*theta*(sig+c-b))
            maxima=[max(v,w) for v,w in zip(maxima,vals)]
            require(b>0 and sig+c-b>0, ('positivity',sig,a,t,ell,c,b))
            for v,cap in zip(vals,[sig-eps,1-8*eps,2-15*eps,2-15*eps]):
                require(v<cap, ('rail',sig,a,t,ell,c,b,vals))
    require(maxima==list(map(F,['.0981','.9971','1.79935','1.66805625'])),maxima)
    require(bmin==F('.0169'),bmin)
    # Affine rails attain maxima at these endpoints also for the correlated
    # slanted side c=.585-2 sigma (not at an independent spurious sigma=.14,c=.385).
    print(f'{corners} correlated exact corners; maxima={maxima}; min B={bmin}')
