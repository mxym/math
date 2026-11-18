"""Exact finite certificates for FIVE.md and THREE.md (standard library only)."""
from fractions import Fraction as F
from math import comb


def require(condition, label):
    if not condition:
        raise ValueError(label)


def multiply(a, b):
    result = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def bernstein_on_interval(poly, left, right):
    """Convert power coefficients in t to Bernstein coefficients on [left,right]."""
    n = len(poly) - 1
    # First use t = left + (right-left)*u, then convert powers of u.
    powers = [
        sum(poly[j] * comb(j, i) * left**(j-i) * (right-left)**i
            for j in range(i, n+1)) for i in range(n+1)
    ]
    return [
        sum(powers[i] * F(comb(k, i), comb(n, i)) for i in range(k+1))
        for k in range(n+1)
    ]


def log_range(x, n):
    """Bounds for log(x) when x >= 1 via the atanh series."""
    require(x >= 1, 'log range domain')
    y = (x-1) / (x+1)
    lower = 2 * sum(y**(2*j+1) / (2*j+1) for j in range(n))
    return lower, lower + 2*y**(2*n+1) / ((2*n+1)*(1-y*y))


def check_qubit_polynomials():
    h4 = [F(1, 2*i+1) for i in range(5)]
    h7 = [F(1, 2*i+1) for i in range(8)]
    p = multiply(h4, [1, 6, -3])
    p[0] -= 1
    p[1] -= 6
    require(p[0] == 0, 'numerator divisible by t')
    p = p[1:]
    q = multiply(h7, [1, F(-1, 2)])
    q[0] -= F(13, 14)
    expected = [
        (F(51971,322560), F(701,10080), F(67,1152), F(8363,107520)),
        (F(193143913,5904138240), F(45761,7687680),
         F(1951291,1291530240), F(1342581,131203072)),
    ]
    for name, poly, values in zip(('P', 'Q'), (p, q), expected):
        minima = tuple(min(bernstein_on_interval(poly, F(i, 4), F(i+1, 4)))
                       for i in range(4))
        require(minima == values and min(minima) > 0, 'Bernstein minima '+name)
        print(name, 'Bernstein minima:', ', '.join(map(str, minima)))
    require(F(107,12) < 9, 'qutrit row-diameter polygon')


def check_five():
    a, b = F(27,14), F(13,7)
    require(F(9,4)**2 > 5 and (5+F(9,4))/10 < (b-1)**2
            and (7+F(9,4))/10 < (a/2)**2, 'radical upper bounds')
    require((a-b)/(2-b) == F(1,2), 'threshold split')
    S = 2*b + 2*(a-b)**2/(2-b)
    require(S == F(53,14), 'integral')
    n = 10
    lo2, _ = log_range(F(2), n)
    _, hi43 = log_range(F(4,3), n)
    h_lower = (lo2 - sum(F(1, 2**k * 2*k*(2*k-1)) for k in range(1,n+1))
               - F(1, 2**n * (2*n+2)*(2*n+1)))
    gap_lower = h_lower - F(3,2)*hi43 + lo2/4*(2-S/2)
    require(gap_lower > F(3,1000), 'strict Qian (18) gap')
    print('Exact envelope integral:', S, '; family (8) gap > 3/1000 nats')


if __name__ == '__main__':
    check_qubit_polynomials()
    check_five()
    print('All exact certificates passed.')
