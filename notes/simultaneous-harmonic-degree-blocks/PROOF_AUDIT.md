# Proof audit: simultaneous harmonic-degree blocks

## Claim audited

For epsilon > 0, beta > 1, and A > 1 satisfying

    A beta^2 < 9/4,

one metric supplied at degree k by the pinned three-dimensional OpenAI/math
counterexample gives an A-factor harmonic-dimension excess at every integer

    k <= d <= floor(beta (k+1)) - 1.

## Dependency check

1. **Upstream quantitative input.** The inspected source states a
   near-Euclidean corollary for every epsilon > 0 and every 1 < c < 9/4,
   for all sufficiently large integers k. It retains the main theorem's
   lower bound h_k >= c (k+1)^2.
2. **Euclidean count.** In dimension three,
   h_d(R^3,g_E)=(d+1)^2 for integer d >= 0, by summing the dimensions
   2l+1 of homogeneous spherical harmonics for 0 <= l <= d.
3. **Monotonicity.** If d >= k, the defining pointwise growth bound for
   H_k is also a degree-d bound, so H_k is contained in H_d and h_d >= h_k.
4. **Endpoint arithmetic.** If
   d <= floor(beta (k+1)) - 1, then d+1 <= beta(k+1).
5. **Strict margin.** Choose c strictly between A beta^2 and 9/4. Then
   h_d >= c(k+1)^2 > A beta^2(k+1)^2 >= A(d+1)^2.

No step reverses an inequality, changes the metric while d varies, or uses
a limit statement at an endpoint.

## Edge cases

- beta > 1 guarantees that the block is nonempty for all sufficiently
  large k.
- Strict A beta^2 < 9/4 is required to choose c; the proof does not cover
  equality.
- The integer endpoint floor(beta(k+1))-1 is safe whether or not
  beta(k+1) is an integer.
- The argument only moves to larger growth degrees. It makes no claim for
  d < k.
- The same g_k is used throughout a fixed block, but it may still depend on
  its starting degree k.

## Computer assistance

The proof itself is exact and symbolic. checker.py is only an independent
exact-rational replay of Item 5 for finite test ranges. It is not evidence
for the imported analytic construction.

## Audit conclusion

Conditional only on the explicitly pinned upstream theorem, the
simultaneous-block theorem is a complete formal consequence. No
floating-point, numerical optimization, or unverifiable solver assumption
enters the deduction.
