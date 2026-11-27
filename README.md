# A sharp 41-doubling window and two-sided cap-12 Littlewood rigidity

This archive records three distinct statements in the 2-adic Littlewood continued-fraction B variant.

1. For every irrational alpha, some dyadic multiple has B at least 13.
2. For nonquadratic alpha, the least universal window is exactly j=0 through 41. A compact returning-loop certificate witnesses failure through j=40.
3. For the intrinsic two-sided invariant in [Giraudin, Section 9 and Proposition 11](https://hexagonmath.org/pdf/2611.00009v1), 41 <= N(12) < infinity. We do not compute its exact value.

This does not settle the full 2-adic Littlewood conjecture. See the [base proof](FactorLittlewoodBDoublingBound13.md) and the [sharpness and rigidity supplement](FactorLittlewoodB13SharpnessAndRigidity.md). For the compact checks run `node verify_factor_littlewood_b13_supplement.js`. The separate cap-12 full graph replay is `node --expose-gc verify_factor_littlewood_b13.js 12 41 8000000` (requires more memory).
