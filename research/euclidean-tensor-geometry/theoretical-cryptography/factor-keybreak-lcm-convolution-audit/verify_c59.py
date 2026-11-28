#!/usr/bin/env python3
"""Exact checks for the printed and repaired versions of KeyBreak (C.59)."""

from math import gcd, lcm

# Exact advertised counterexample.  Squaring twice converts the printed
# inequality to (r*s*H1*H2)^2 <= a*b*L^4.
ell = 11
r = 11
s = 3
H1 = H2 = 1
a = gcd(r, ell)
b = gcd(s, 2)
L = lcm(H1 * (r // a), H2 * (s // b))

printed_left = (r * s * H1 * H2) ** 2
printed_right = a * b * L**4
corrected_left = r * s * H1 * H2
corrected_right = a * b * L**2

assert L == 3
assert printed_left == 1089 and printed_right == 891
assert printed_left > printed_right
assert corrected_left == 33 and corrected_right == 99
assert corrected_left <= corrected_right

print("sample ell=11,H1=H2=1,r=11,s=3,L=3")
print("printed exact test: 1089 <= 891 ->", printed_left <= printed_right)
print("corrected exact test: 33 <= 99 ->", corrected_left <= corrected_right)

# Finite regression.  The repaired inequality follows generally from
# lcm(A,B)^2 >= A*B; this enumeration is only a replayable sanity check.
primes = [3, 5, 7, 11, 13, 17, 19]
count = 0
printed_failures = 0
first_printed_failure = None

for ell in primes:
    for r in range(2, 31):
        for s in range(2, 31):
            for H1 in range(1, 9):
                for H2 in range(1, 9):
                    a = gcd(r, ell)
                    b = gcd(s, 2)
                    L = lcm(H1 * (r // a), H2 * (s // b))
                    H = H1 * H2

                    # Repaired inequality, squared once.
                    assert r * s * H <= a * b * L * L

                    # Printed inequality, squared twice.
                    printed_ok = (r * s * H) ** 2 <= a * b * L**4
                    if not printed_ok:
                        printed_failures += 1
                        if first_printed_failure is None:
                            first_printed_failure = (ell, r, s, H1, H2, L)
                    count += 1

assert count == 376768
assert printed_failures == 5172
assert first_printed_failure == (3, 2, 2, 1, 2, 2)

print("enumerated tuples:", count)
print("printed failures:", printed_failures)
print("first printed failure:", first_printed_failure)
print("corrected failures: 0")
