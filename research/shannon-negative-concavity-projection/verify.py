"""Small exact checks of identities in the limiting proof, not a finite-epsilon bound."""
from fractions import Fraction as Q


def check(truth):
    if not truth:
        raise ArithmeticError("An exact identity failed")

for D in (Q(3, 2), Q(2), Q(5), Q(16), Q(31)):
    e_neg_C = 1 / (1 + 1 / D**2)
    lower = D * (1 - e_neg_C)
    upper = e_neg_C / D
    check(lower == upper > 0 and lower / (lower + upper) == Q(1,2))
    t = 1/D
    # Sum for the angular correction; positive, with a uniform geometric tail bound.
    terms = [t**(2*j) / ((2*j-1)*2*j*(2*j+1)) for j in range(1, 11)]
    check(terms[0] == t*t/6)
    check(all(0 < b < a*t*t for a,b in zip(terms,terms[1:])))
    check(0 < sum(terms) < terms[0]/(1-t*t))
for eps in (Q(1),Q(1,2),Q(1,10),Q(1,31)):
    s = -1 / (2+eps)
    check(s > Q(-1,2) and s / (1+2*s) == -1/eps)
print("PASS: curvature conversion, two equal limiting weights, positive angular series")
