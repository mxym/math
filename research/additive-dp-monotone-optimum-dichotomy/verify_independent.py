"""Independent affine primitives, fractional powers, and interval dual."""
from decimal import Decimal as D, localcontext
from fractions import Fraction as F


def affines(c, a):
    # Direct normalized template: (lower end, upper end, slope, intercept).
    for u,v,s,b in ((-1,F(-1,2),-1,-1), (F(-1,2),0,3,1),
                    (0,F(1,2),-3,1), (F(1,2),1,1,-1)):
        yield c+a*u,c+a*v,F(s)/a,F(b)-F(s)*c/a


def dec(x):
    return D(x.numerator)/D(x.denominator)


def absolute_power_affine(x,y,m,b,p):
    # p is fractional; split at 0 and reflect the negative side.
    if x < 0:
        if y > 0:
            return (absolute_power_affine(x,0,m,b,p)
                    + absolute_power_affine(0,y,m,b,p))
        return absolute_power_affine(-y,-x,-m,b,p)
    x,y,m,b = map(dec,(F(x), F(y), F(m), F(b)))
    exponent = dec(p)
    return (m*(y**(exponent+2)-x**(exponent+2))/(exponent+2)
            + b*(y**(exponent+1)-x**(exponent+1))/(exponent+1))


def halfline_weight_check():
    cases = 0
    for k in range(1,17):
        W = [max(0,k-abs(j+1)) for j in range(-k,k)]
        assert sum(W) == k*k
        for s in range(-7*(k+1),7*(k+1)+1):
            x = F(s,7)
            c = sum(W[j+k]*max(0,min(j+1,x)-max(j,x-1)) for j in range(-k,k))
            assert c == max(0,k-abs(x))
            cases += 1
        delta = F(1,2*k)
        assert k-delta*k*k == F(k,2)
    for s in range(16,32):
        delta = F(s,32)
        a = 2*delta-1
        assert 1-delta == (1-a)/2
        assert a+(1-a)/2 == delta
    return cases


def p_opt(delta, p):
    a = max(F(0),(1+p)*delta-p)
    return (1-a)/(delta-a), a


def check_costs():
    trials = 0
    with localcontext() as ctx:
        ctx.prec = 65
        for p in (F(1,10),F(1,2),F(9,10),F(11,10),F(3,2),F(3)):
            for d in (F(1,7),F(1,3),F(2,5),F(1,2),F(10,13),F(99,100)):
                L, alpha = p_opt(d,p)
                m = int(L)
                r = L-m
                a = (1-r)/2
                c = (1+r)/2-L/2
                if p < 1:
                    A = a/4
                    centers = [c+j+z*a/2 for j in range(m) for z in (-1,1)]
                    sign = -1
                    assert all(abs(q)>A for q in centers)
                else:
                    A = a
                    centers = [c+j for j in range(m)]
                    sign = 1
                integral = sum(absolute_power_affine(x,y,q,b,p)
                               for t in centers for x,y,q,b in affines(t,A))
                # The gap is strictly negative by a margin many orders above roundoff.
                decrease = -dec((1-alpha)*A/(4*L*L)*sign)*integral
                assert decrease > D('1e-16')
                if p == F(1,2) and d == F(1,2):
                    assert integral > D('1e-9')  # the *unnegated* bump is worse.
                trials += 1
    return trials


if __name__ == '__main__':
    print('independent: interval-dual identity at', halfline_weight_check(),
          'rational points, exact endpoint budgets and losses PASS')
    print('independent: high-precision affine primitives in', check_costs(),
          'power/privacy profiles, including both signs and mixed laws PASS')
