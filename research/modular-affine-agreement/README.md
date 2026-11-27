# Affine agreement before and after prime reduction

This note separates a sign issue and a coefficient-domain obstruction in
Doerner–Haitner–Ishai–Makriyannis, ePrint 2025/1722, Definition 5.36 and
Conjecture 5.37, from a positive result for **rational** affine lines.
It is a finite weighted-incidence statement. No protocol claim is made.

* With the displayed difference in Definition 5.36, the maximum is zero:
  reduction can only improve the objective measured there.
* Reversing that difference is not enough. On the two inputs 0 and 2,
  assign outputs 1 and 2. Every odd-prime field admits the line through
  these points, but no integral affine line fits both. The expectation
  gap is exactly 1/2, even allowing negative integer coefficients.
  We also give sharp worst-case gaps in the stated large-prime regimes,
  separately for nonnegative and signed integer coefficients.
* With rational affine comparators instead, **every** prime exceeding
  the square of the box side preserves the best agreement exactly, even
  for randomized labels. For any box size and any nonempty finite set of
  primes, a weighted pair/triple argument bounds the upward change in
  terms of prime divisors of coordinate differences and determinants.
  A separate denominator bound controls the downward change. Over
  uniformly chosen k-bit primes this makes the expected upward change
  exponentially small for every fixed exponential box-growth rate.

The rational formulation is proposed here; it is not attributed to the
source authors. The AICR mirror already notes the printed sign issue.
See [PROOF.md](PROOF.md) for exact ranges and constants, and
[SOURCES.md](SOURCES.md) for prior art.

Run `sh replay.sh` with Python 3. Neither checker uses network access,
external datasets, or any instance of a protocol.
