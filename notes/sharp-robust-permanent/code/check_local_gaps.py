#!/usr/bin/env python3
"""Replay exact rational comparisons in paper Section 14.

The theorem's analytic estimates and compactness argument are in paper.md;
this checks all integer comparisons and rational residual gaps. No floats.
"""
from fractions import Fraction as F

assert 3**15 > 6**9             # q_3 > 9/5
assert 3**30 < 6**19            # q_3 < 19/10
assert 100**19 > 17**19 * 3**30 # c_(19/10) > 17/100
assert 173**2 < 3*100**2        # sqrt(3) > 173/100
assert 27 > 25                 # sqrt(3) > 5/3; c_2 < 1/5
print("PASS: four exact integer exponent/root comparisons")

d_small = F(1, 6)*F(10, 19)-F(1, 12)
d_large = F(17, 100)-F(1, 6)
assert d_small == F(1, 228)
assert d_large == F(1, 300)
assert d_small > d_large
print("PASS: universal spike coefficient is above 1/300")

h_const = F(1, 1000)
constant_margin = F(3, 200) - 4*h_const
assert constant_margin == F(11, 1000)
assert constant_margin > F(1, 100)
print("PASS: strict constant-neighborhood deficit > V/100")

h_spike = F(1, 100)
spike_error = F(1, 5)*(h_spike/2 + (6*h_spike)/8)
spike_margin = F(1, 300)-spike_error
assert spike_error == F(1, 400)
assert spike_margin == F(1, 1200)
print("PASS: spike-neighborhood deficit >= S/1200")
print("All Section 14 exact arithmetic checks passed.")
