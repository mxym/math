"""Exact, fixed tests of the rational degree-sum lattice, without inputs."""
from fractions import Fraction as Q
from itertools import product

checks = 0
for a, b in ((2, 1), (3, 2), (5, 4), (11, 10)):
    ratio = Q(a,b)
    c = 0
    while ratio**c < b:
        c += 1
    for L in (3, 4, 5, 8, 13, 21, 55, 89):
        H = 0
        while ratio**(H+1) <= L:
            H += 1
        D = b**H
        assert ratio**H <= L < ratio**(H+1)
        assert D <= L**c
        for h1,h2 in product(range(min(7,H)+1),repeat=2):
            for weights in ((1,1,1),(2,1,1),(1,3,2),(1,2,4)):
                value = sum(w*ratio**h for w,h in zip(weights,(0,h1,h2)))
                if value > L:
                    continue
                J = D*value
                assert J.denominator == 1 and D <= J <= L*D
                checks += 1
print(f"PASS: {checks} exact degree-sum lattice cases for 4 fixed rational ratios")
