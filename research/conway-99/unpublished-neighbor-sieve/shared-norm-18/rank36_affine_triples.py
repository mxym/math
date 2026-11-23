"""Exact row-span check for the two rank-36 charge-three triples.

Run beside rank36_three_types.py (same python-flint dependency).
No optimization routine or numerical linear algebra is used.
"""
from fractions import Fraction
from math import ceil
from flint import fmpq_mat
from rank36_three_types import UNIT, P, short_equations


def main():
    keys, equations = short_equations()
    n24, g37 = (0,24), (3,37)
    identities = [
        ((1,21), {(1,21):56,(0,0):-1312,(0,14):-29,(1,23):-12,
                   (3,33):-16,(3,35):-8,(4,46):-3}),
        ((1,27), {(1,27):12,(0,0):-5568,(0,14):-123,(0,22):-48,
                   (1,23):-36,(3,35):-24,(4,46):-5}),
        ((1,27), {(3,37):1,(0,0):-321,(0,14):-7,(0,22):-4,
                   (1,23):-1,(3,35):-2}),
    ]
    for companion, coeffs in identities:
        active = [i for i,k in enumerate(keys)
                  if k not in UNIT-{companion,n24,g37}]
        rows = [[row[i] for i in active] for row in equations]
        assert set(coeffs) <= {keys[i] for i in active}
        target = [coeffs.get(keys[i],0) for i in active]
        assert fmpq_mat(rows+[target]).rank()==fmpq_mat(rows).rank()
    assert P==2402
    assert ceil(Fraction(P*(1312+12*99),56))==107233>693*64
    assert P*(321+99)==1008840
    assert ceil(Fraction(P*(321+99),4158))==243
    assert P*(5568+36*99)//12==1827922 and P*(5568+36*99)%12==0
    print("Three exact span identities verified.")
    print("{N24,U1,21,U3,37}: impossible at rank 36 (107233 > 44352).")
    print("{N24,U1,27,U3,37}: U1,27 >= 1827922, U3,37 >= 1008840.")

if __name__=='__main__':
    main()
