"""Rational bounds for the actual rank-three angular measure."""
from fractions import Fraction as F

def need(ok, message):
    if not ok:
        raise ArithmeticError(message)

def logbox(x):
    need(F(1) <= x <= F(2), "log input")
    t = (x-1)/(x+1)
    n = 13
    s = 2*sum((t**(2*j+1)/F(2*j+1) for j in range(n)), F())
    err = 2*t**(2*n+1)/((2*n+1)*(1-t*t))
    k = 10**15
    return F(s*k//1, k), F(-(-(s+err)*k//1), k)

def bounds(a, n=1024):
    delta = (F(1,3)-a)/n
    lo,hi = F(),F()
    d = 10**17
    for i in range(n):
        x, y = a+i*delta, a+(i+1)*delta
        l = delta*logbox((1-2*y)/y)[0]/(y*(1-y))
        h = delta*logbox((1-2*x)/x)[1]/(x*(1-x))
        lo += F(l*d//1,d)
        hi += F(-(-h*d//1),d)
    return lo,hi

for a, target in ((F(".25005"),F(".660")),(F(".265"),F(".378"))):
    l,h = bounds(a)
    need(0<l<h<F(".148"), "rank-three measure, strict")
    need(1-4*a+F(9,2)*l>target, "majorant dyadic lower")
    print(f"alpha {float(a):.5f}: I3 in ({float(l):.12f}, {float(h):.12f}), mean lower {float(1-4*a+F(9,2)*l):.12f}")
