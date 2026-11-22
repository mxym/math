"""Exact piecewise chord and nested multilinear interval upper in §2."""
from fractions import Fraction as F
from itertools import product


def validate():
    n, h, scale = 32, 4, 10**14
    n4 = n**4
    # x=i/h has trapezoid weight xw/(2h) for a convex upper.
    nodes = [(i, 1 if i in (0, h) else 2) for i in range(h + 1)]
    answer = 0
    for d, c, b, a in product(range(n), repeat=4):
        # a,b,c,d are lower indices on the four outer ratio axes.
        # dl,cl,bl,al are minima of D,DC,DCB,DCBA scaled by n^4.
        dl = d * n**3
        cl = d * c * n**2
        bl = d * c * b * n
        al = d * c * b * a
        # Mean DCB is bn/(8*n^4), exact on a fixed cube.
        bn = (2*d+1) * (2*c+1) * (2*b+1) * n
        start = h * (n4 + dl + cl)
        for xi, xw in nodes:
            for zeta, zw in nodes:
                ax = h - 2*xi
                by = h - 2*zeta
                # D1 minimum nested from A outward, scaled by h*n^4.
                q = by*n + ax*(a if ax >= 0 else a+1)
                r = h*n*n + q*(b if q >= 0 else b+1)
                s = h*n**3 + r*(c if r >= 0 else c+1)
                den1 = h*n4 + s*(d if s >= 0 else d+1)
                # D2 positive coefficients: all lower endpoints.
                den2 = start + (h-xi)*al + (h-zeta)*bl
                if min(den1, den2) < h*n4:
                    raise ValueError("nonpositive denominator reserve")
                # 2*(mean b)/(D1_min D2_min) times the two node weights.
                numer = bn*n4*xw*zw
                denom = 16*den1*den2
                answer += (numer*scale + denom - 1)//denom
    if answer != 6674950756087897698:
        raise ValueError(("unexpected exact accumulator", answer))
    bound = F(answer, scale*n4)
    if not bound < F(63658, 10**6):
        raise ValueError("chord bound")
    cap = F(200, 53) * (F(63658, 10**6) + F(51800, 10**6))
    if not cap == F(57729, 132500) < F(436, 1000):
        raise ValueError("normalized bound")
    print(f"exact upper accumulator {answer}; I(K+) bound {float(bound):.12f}; final cap {cap}")


if __name__ == "__main__":
    validate()
