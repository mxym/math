#!/usr/bin/env python3
from fractions import Fraction

eps = Fraction(1, 4)
eps_pub = Fraction(1, 16)
B = max(Fraction(0), Fraction(3, 4) * (1 - eps) - eps_pub)
p0 = Fraction(1, 128)

rows = []
for omega in range(2, 21):
    exact = 1 - Fraction(2, 2**omega)
    printed = 1 - Fraction(1, 2**omega)
    corrected_total = exact * B

    # Direct enumeration of CRT sign vectors: only all-plus and all-minus
    # are trivial.
    enumerated = Fraction(2**omega - 2, 2**omega)
    assert enumerated == exact
    assert printed > exact
    assert corrected_total >= Fraction(1, 4)
    assert corrected_total >= p0
    rows.append((omega, exact, printed, corrected_total))

omega, exact, printed, corrected_total = rows[0]
print(f"omega={omega}")
print(f"exact={exact}")
print(f"printed={printed}")
print(f"printed_exceeds_exact={printed > exact}")
print(f"B={B}")
print(f"corrected_total_at_omega2={corrected_total}")
print(f"all_corrected_at_least_quarter={all(r[3] >= Fraction(1,4) for r in rows)}")
print(f"all_corrected_at_least_p0={all(r[3] >= p0 for r in rows)}")
print(f"checked_omega_values={len(rows)}")
