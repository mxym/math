"""Independent replay. Algebra is exact; direct Fourier eigensolver is numerical."""
import itertools
import math
import numpy as np
import sympy as sy


def require(condition, label):
    if not condition:
        raise ValueError(label)


def check_polynomials():
    t = sy.Symbol('t')

    def partial_h(n):
        return sum(t**j / sy.Integer(2*j+1) for j in range(n+1))

    for name, expr, endpoints in [
        ('P', sy.cancel((partial_h(4)*(1+6*t-3*t*t)-1-6*t)/t),
         (sy.Rational(1,3), sy.Rational(47,315))),
        ('Q', partial_h(7)*(1-t/2)-sy.Rational(13,14),
         (sy.Rational(1,14), sy.Rational(7417,90090))),
    ]:
        p = sy.Poly(expr, t, domain=sy.QQ)
        require((p.eval(0),p.eval(1)) == endpoints, name+' endpoints')
        chain = p.sturm()

        def variations(point):
            signs = [sy.sign(poly.eval(point)) for poly in chain]
            signs = [v for v in signs if v]
            return sum(1 for a, b in zip(signs, signs[1:]) if a != b)

        v0, v1 = variations(0), variations(1)
        require(v0 == v1 and p.eval(0) > 0, name+' Sturm positivity')
        print(name, 'Sturm variations:', v0, v1, '; endpoints:', endpoints)


def check_determinants():
    X, Z, d, a, b = sy.symbols('X Z delta a b')
    T = X+Z
    det = ((a*(1-X)+d*(T-X))*(b*(1-Z)+d*(T-Z)) - (1-d)**2*X*Z)
    vertex_a = Z*(d*(1-Z)/3+(2*d-1)*X)
    vertex_b = a*a*(1-T)+a*d*T*(1-T)+(a*a+2*a*d+2*d-1)*X*Z
    require(sy.expand(det.subs({a: 0, b: sy.Rational(1,3)})-vertex_a) == 0,
            'asymmetric determinant')
    require(sy.expand(det.subs(b,a)-vertex_b) == 0, 'symmetric determinant')


def corroborate_fourier():
    n = 5
    ix = np.arange(n)
    U = np.exp(2j*np.pi*ix[:,None]*ix/n)/np.sqrt(n)
    lines = []
    for bits in itertools.product((0,1), repeat=2*n):
        p = np.diag(bits[:n])
        q = (U*np.array(bits[n:])) @ U.conj().T
        ev = np.linalg.eigvalsh(p+q)
        lo, hi = ev[0], ev[-1]
        lines.append((hi-lo, -hi-lo))

    def maximum(t):
        return max(intercept+slope*t for intercept, slope in lines)

    c = math.sqrt((5+math.sqrt(5))/10)
    C = math.sqrt((7+math.sqrt(5))/10)
    B, E = 1+c, 2*C
    star = (E-B)/(2-B)
    for t in (0,star,0.5,1):
        require(abs(maximum(t)-max(E-2*t,B*(1-t))) < 5e-14,
                'Fourier spectral envelope (floating point)')
    total = 2*((maximum(0)+maximum(star))*star+(maximum(star)+maximum(1))*(1-star))
    require(len(lines) == 1024 and 3.76964 < total < 3.76965, 'numerical integral')
    print('Numerical corroboration: 1024 Fourier subset pairs; split, integral:', star, total)


if __name__ == '__main__':
    check_polynomials()
    check_determinants()
    # Trapezoids of width 1/2 with endpoints (a,13/14,0); four directed/layer units.
    s = 4*((sy.Rational(27,14)+sy.Rational(13,14))/4+sy.Rational(13,14)/4)
    require(s == sy.Rational(53,14), 'rational trapezoids')
    print('Exact symbolic determinants and rational integration passed:', s)
    corroborate_fourier()
