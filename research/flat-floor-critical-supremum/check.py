"""Exact consistency check for the critical failure term. Python standard library."""
from fractions import Fraction as Q
from math import factorial

# A monomial a*(sqrt(pi))^k, with rational a and integer k.
def mul(x, y):
    return (x[0]*y[0], x[1]+y[1])

def power(x, n):
    return (x[0]**n, x[1]*n)

def div(x, y):
    return mul(x, power(y, -1))

def m(x):
    return (Q(x), 0)

def gamma(k):
    # Gamma(k/2)
    if k == 1: return (Q(1), 1)
    if k == 2: return m(1)
    return mul(m(Q(k-2, 2)), gamma(k-2))

def formula(d):
    V = div((Q(1), d), gamma(d+2))
    directions = div(power(gamma(d), d), mul((Q(1), 1), power(gamma(d+1), d-1)))
    return div(mul(m(Q(2*(d+1),factorial(d))*Q(d,d+1)**d), directions), V)

def gauss(d):
    # Independent radial-integral derivation for the QR determinant of iid
    # Gaussian columns with density proportional to exp(-|x|^2).
    # I_j=integral_0^infty r^j exp(-r^2) dr; E|G_k|=I_k/I_(k-1).
    I=[(Q(1,2),1),m(Q(1,2))]
    V=[m(1),m(2)]  # volumes V_k=2*pi*V_(k-2)/k
    for j in range(2,d+1):
        I.append(mul(m(Q(j-1,2)),I[-2]))
        V.append(mul((Q(2,j),2),V[-2]))
    det=m(1)
    for k in range(1,d+1):
        det=mul(det, div(I[k],I[k-1]))  # successive perpendicular lengths
    sphere=div(det,power(div(I[d],I[d-1]), d))
    return div(mul(m(Q(2,factorial(d))*(d+1)*Q(d,d+1)**d),sphere),V[d])

def main():
    if formula(2)!=(Q(8,3),-4) or formula(3)!=(Q(27,512),0):
        raise ArithmeticError("planar or spatial check failed")
    for d in range(2,65):
        x,y=formula(d),gauss(d)
        if x!=y:
            raise ArithmeticError((d,x,y))
        if d<=5: print(f"d={d}: 1 - sup = {x[0]} * sqrt(pi)^({x[1]})")
    print("PASS: 63 exact dimension cross-checks (d=2,...,64), including two fixed low-dimensional values.")
if __name__=="__main__": main()
