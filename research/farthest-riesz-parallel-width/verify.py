"""Exact low-dimensional regression tests, not substitutes for the proofs."""
from fractions import Fraction as F


def check(name, actual, expected):
    if actual != expected:
        raise ArithmeticError(f"{name}: {actual!r} != {expected!r}")


# Truncated power series to order two.
def product(A, B):
    return tuple(sum(A[k] * B[j-k] for k in range(j+1)) for j in range(3))


def power(A, exponent):
    exponent = F(exponent)
    if A[0] != 1:
        raise ValueError("power() expands about constant coefficient one")
    return (F(1), exponent*A[1],
            exponent*A[2] + exponent*(exponent-1)*A[1]**2/2)


# K=[-e,e] in R^3. z=1/t, a=|u.e| uniform on [0,1] on the two caps.
# The exact cap integrand in 4 sigma is 4(1+2az)/[D(1+D)^2],
# D=sqrt(1+4az+4z*z). The normalized lateral contribution is averaged
# over axial s uniform on [-1,1]: 4z/[D(1+D)^2], D=sqrt(1+(1+|s|)^2z^2).
def capsule(a):
    D = power((1, 4*a, 4), F(1, 2))
    H = (1, D[1]/2, D[2]/2)
    cap = product((1, 2*a, 0), product(power(D, -1), power(H, -2)))
    E = power((1, 0, (1+a)**2), F(1, 2))
    I = (1, E[1]/2, E[2]/2)
    barrel = product((0, 1, 0), product(power(E, -1), power(I, -2)))
    return cap, barrel


for i in range(32):
    a = F(i, 31)
    cap, barrel = capsule(a)
    check('cap jet', cap, (1, -2*a, -4+7*a*a))
    check('barrel jet', barrel, (0, 1, 0))
# Each jet coefficient is polynomial of degree <=2 in a. Integrate by
# the exact three-point Simpson formula, not sampling a physical measure.
jets = [capsule(F(j, 2)) for j in range(3)]
integrals = tuple(sum((jets[j][0][k]+jets[j][1][k])*w
                      for j, w in enumerate((1,4,1)))/6 for k in range(3))
check('capsule integrated', integrals, (1, 0, -F(5, 3)))
print("PASS: exact two-jet capsule cap/barrel tests (32 rational parameters); "
      "integrated jet (1,0,-5/3).")


# Axially symmetric constant width profiles h=1+eta*f(x), x=u.e uniform
# on [-1,1]. Exact KNS flux for such a body is 4 sigma=|boundary|/(4pi).
# The curvature perturbations in the meridian/azimuth directions are
# (1-x^2)f'' - xf'+f and f-xf'. Compute their product and the Dirichlet
# deficit independently in the ring Q[x].
def add(A,B):
    return tuple((A[k] if k<len(A) else 0)+(B[k] if k<len(B) else 0)
                 for k in range(max(len(A), len(B))))


def mul(A,B):
    C = [F(0)] * (len(A)+len(B)-1)
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            C[i+j] += a*b
    return tuple(C)


def der(A):
    return tuple(F(i)*A[i] for i in range(1, len(A))) or (F(0),)


def mean(A):
    return sum((F(a, k+1) for k,a in enumerate(A) if k%2==0), F(0))


for f,target in [((0,1), F(0)), ((0,-F(3,2),0,F(5,2)), -F(5,7))]:
    df=der(f)
    B=add(f,mul((0,-1),df))
    A=add(B, mul((1,0,-1),der(df)))
    area2=mean(mul(A,B))
    deficit=(2*mean(mul(f,f))-mean(mul((1,0,-1),mul(df,df))))/2
    check('linear curvature integral',mean(add(A,B)),0)
    check('exact integrated determinant',area2,target)
    check('odd-mode spectral coefficient',deficit,target)
print("PASS: exact odd P1 and P3 axisymmetric curvatures; quadratic "
      "coefficients 0 (translation) and -5/7.")


for m in range(2, 201):
    M=F(m)
    # Basis: e^2, |grad e|^2, o^2, |grad o|^2 in the area expansion.
    A2=(M*(M-1)/2, -(M-1)/2, M*(M-1)/2, -(M-1)/2)
    cross=(-M*M,M,0,0)
    residual=(M*(M+1)/2,-(M+2),0,0)
    check('area polynomial coefficients', tuple(x+y+z for x,y,z in
          zip(A2,cross,residual)), (0,-(M+3)/2,M*(M-1)/2,-(M-1)/2))
    n=m+1
    d=F(1,8*(n+1))
    if not (2*(d+4*d*d)<=4*d and (16+32*n)*d/9<F(1,2)):
        raise ArithmeticError(f"width bound failed at dimension {n}")
print("PASS: area coefficient cancellations and explicit width-class "
      "curvature margins in dimensions 3 through 201.")
