"""Exact finite checks of the margins and finite-difference in §2, not a prime test."""
from fractions import Fraction as F
from itertools import combinations
from random import Random


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def divisor_logs(vs):
    for r in range(len(vs) + 1):
        for w in combinations(vs, r):
            yield sum(w, F(0)), (-1)**r


def cutoff_sum(vs, t):
    return sum(mu for s, mu in divisor_logs(vs) if s < t)


def hinge_sum(vs, t):
    return sum((mu * max(t-s, F(0)) for s, mu in divisor_logs(vs)), F(0))


def literal_high(vs):
    mid = sum(vs, F(0))/2
    if any(t == mid for t, _ in divisor_logs(vs)):
        return None
    return sum((mu*(2*mid-t) for t, mu in divisor_logs(vs) if t > mid), F(0))


def check(vs, w):
    p, c, a, b = vs
    high = literal_high(vs+w)
    if high is None:
        return False
    Delta = F(1, 2)-p
    delta = Delta-c
    g = (c, a, b)+w
    mu_g = (-1)**len(g)
    c_count = cutoff_sum(g, Delta)
    c_hinge = hinge_sum(g, Delta)
    require(high == (c_count if mu_g == 1 else 2*c_hinge), 'macro-bit formula')
    s, h, j = -1, -delta, 0
    for u, mu in divisor_logs(w):
        v = Delta-u
        D = int(v>0)-int(v>a)-int(v>b)+int(v>a+b)
        E = max(v, 0)-max(v-a, 0)-max(v-b, 0)+max(v-a-b, 0)
        require(abs(D)<=1 and abs(E)<=min(a,b), 'pointwise differences')
        s += mu*D
        h += mu*E
        j += 0 <= v <= a+b
    require((s,h)==(c_count,c_hinge), 'exact finite-difference normalizations')
    require(max(s,0)<=j*(j-1)/2, 'two necks necessary in count branch')
    require(max(h,0)<=min(a,b)*j, 'single neck error in hinge branch')
    if j == 0:
        require(high < 0, 'negative plateau in both parities')
    return True


def main():
    beta=F('0.1011')
    v1, v2, v3=F('0.01244'), F('0.218001'), F('0.282002')
    theta=F(7,32)
    actual=[
        v1-F('0.1009'),
        2*beta+v2+2*v3,
        theta+beta+v1+5*v2+2*v3,
        (1+2*theta)*beta+v1+(5-2*theta)*v2+(2+2*theta)*v3,
    ]
    published=[F('-.08846'),F('.984205'),F('1.986299'),F('1.840')]
    require(all(a <= b for a,b in zip(actual,published)), 'Proposition 5.2 rails')
    rng=Random(131617)
    samples=0
    p, c, a, b=[F(s) for s in ('0.218', '0.2819', '0.000204', '0.000226')]
    target=(p,c,a,b)
    W=1-sum(target)
    for r in range(1,9):
        for i in range(64):
            ks=[F(rng.randrange(100,2000),1000) for _ in range(r)]
            w=tuple(x*W/sum(ks) for x in ks)
            if min(w)>F('.004'):
                samples+=check(target,w)
    Delta=F(1,2)-p
    near_one=Delta-F('.00005')
    ga=F('.13201')
    v=near_one-ga
    mid=(
        ga,
        v,
        v + F('0.000011'),
        W-(ga+2*v+F('0.000011')),
    )
    require(min(mid)>F('.004'), 'explicit two-neck shape')
    require(check(target,mid), 'explicit two-neck check')
    require(samples>250, 'non-trivial sample count')
    print(f"{samples} exact log-profile checks plus an explicit two-neck profile; rails pass")


if __name__=="__main__":
    main()
