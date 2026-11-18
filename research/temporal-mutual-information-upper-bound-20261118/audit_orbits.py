"""Independent exact verification, compressed by relabeling basis words.
Only representatives of triples aaa, aab and abc are needed. All d supported.
Python + SymPy, no access to the author checker."""
from itertools import permutations
from math import comb
from collections import Counter
import sympy as S


def check(ok):
    if not ok:
        raise ArithmeticError("unexpected result in independent orbit check")


def orbit_spectrum(word, s):
    orbit=sorted(set(permutations(word)))
    # Read N(E_{h,k})=sum_i K_i E_{h,k}K_i^* for K_i=<i| tensor I.
    # Direct construction of Jam and rho tensor I on the orbit. Version
    # deliberately keeps a sum over Kraus outcomes rather than a cycle matrix.
    n=len(orbit)
    O=S.zeros(n)
    J=S.zeros(n)
    for u,(a,b,c) in enumerate(orbit):
        for v,(x,y,z) in enumerate(orbit):
            O[u,v]=int(c==z)*(int(a==x and b==y)+s*int(a==y and b==x))
            J[u,v]=sum(int(x==i)*int(c==y)*int(a==i)*int(z==b) for i in set(word))
    # O = d(d+s)*rho tensor I; projective test catches normalization.
    check(O**2==2*O and J**2==S.eye(n) and J.is_symmetric())
    Z=O*J+J*O
    X=S.symbols('X')
    P=Z.charpoly(X).as_poly()
    roots=S.polys.polytools.ground_roots(P)
    check(sum(roots.values())==n)
    return roots


def run(d,s):
    # Number of multisets: aaa has d choices, aab has d choices of a
    # and d-1 choices of b, abc corresponds to a 3-subset.
    specs=[((0,0,0),d),((0,0,1),d*(d-1)),((0,1,2),comb(d,3))]
    spectrum=Counter()
    for word,n_orbits in specs:
        for val,mult in orbit_spectrum(word,s).items():
            spectrum[val]+=n_orbits*mult
    k=d*(d+s)
    check(sum(spectrum.values())==d**3)
    check(sum(x*m for x,m in spectrum.items())==2*k)
    # Return rational coefficients of log2, log3 in I-log d.
    # |x|/2=2^p 3^q for all nonzero integer eigenvalues x of 2k*R.
    c2,c3=S.Integer(-1),S.Integer(0)
    for val,m in spectrum.items():
        if val:
            factors=S.factorint(abs(int(val)))
            check(all(p in (2,3) for p in factors))
            c2+=S.Rational(val*m,2*k)*(factors.get(2,0)-1)
            c3+=S.Rational(val*m,2*k)*factors.get(3,0)
    check((c2,c3)==(S.Rational(2*(s*d-1),3), S.Rational(1-s*d,2)))
    return dict(sorted(spectrum.items())),(c2,c3)

for d in (2,3,64,256):
    for s in (-1,1):
        print(d,s,run(d,s))
# Direct exact integer comparison of I_- versus 2 log d, I_+ versus 0
# and the padded I_- versus 4 log d, without using the draft's c>log2/9.
check(27**65>16**65*64**6)
check(27**63>16**63*64**6)
check(27**257>16**257*256**18)
print('All exact, including full d=64 and d=256 multiplicities by relabeling.')
