# Prior art and scope

## Analytic input

Eric Bach, **“Explicit bounds for primality testing and related
problems,”** *Mathematics of Computation* 55 (1990), 355–380,
DOI [10.1090/S0025-5718-1990-1023756-8](https://doi.org/10.1090/S0025-5718-1990-1023756-8).

Under the extended/generalized Riemann hypothesis, Bach proves an
explicit \(O((\log m)^2)\) bound (constant \(2\) in the form used here)
for an integer outside a proper multiplicative subgroup modulo \(m\).
This is the only conditional analytic input to the proof.

A later sharper prime-outside-subgroup theorem is:

* Y. Lamzouri, X. Li, K. Soundararajan, **“Conditional bounds for the
  least quadratic non-residue and related problems,”** *Math. Comp.*
  84 (2015), 2391–2412,
  DOI [10.1090/S0025-5718-2015-02925-1](https://doi.org/10.1090/S0025-5718-2015-02925-1),
  with corrigendum DOI
  [10.1090/mcom/3261](https://doi.org/10.1090/mcom/3261).

That sharpening is not needed here; the proof deliberately uses Bach's
older all-integer subgroup bound.

## Closest repository predecessors

* Commit 4e0f3489260d13e8b3607d63fe8f29e3d3f94cdc constructs the exponent
  multiple from support advice and gives an unconditional
  largest-unlisted-prime bound.
* Commit 3c4258ea82dd571c4ddfedb077103af82685cfb7 combines small-factor
  removal, an unconditional smooth-subgroup scan, and ratio
  reconstruction to obtain a general \(L_N[2/3,1+o(1)]\) bound.

The present note replaces those unconditional escape/reconstruction
stages by Bach's GRH subgroup witness and obtains polynomial time.

## Distinctions

* The input is the complete prime support of \(\lambda(N)\), possibly
  with false positives. It is **not** merely a partial support and is
  not computed from \(N\).
* The exact value of \(\lambda(N)\) is not supplied.
* The conclusion is conditional on GRH and is not an unconditional
  polynomial-time factoring algorithm.
* No claim of absolute historical priority is made.
