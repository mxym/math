# M independent control history

All times below are UTC. This directory belongs to the same internal AI
reviewer agent that separately read L, not an external human or a Lean kernel.
No author script was run by the reviewer. No author mathematical source was
modified. Every listed run retains its executed script bytes and RESULT.json.

1. `20261015T083524.651443Z`: **FAIL** in the reviewer-written checker's
   tiny-order rank-rounding diagnostic. The checker imposed the unproved
   numerical condition `m^8 * loss/alpha < 10`. At m=3000, alpha=0.31 the
   correctly evaluated scaled loss is approximately 12.58928446058. The
   manuscript claims `O(alpha*m^-8)`, with no assertion that its constant is
   ten. The failed diagnostic therefore did not refute a manuscript claim.
   The exact second rank derivative gives leading absolute curvature
   `alpha*kappa^2/D^2`, hence maximal adjacent-rank loss is asymptotically
   bounded by `alpha/(2*d0^2*m^8)`, whose coefficient is about 15.89.

2. `20261015T083604.420048Z`: **PASS** after changing only that diagnostic
   condition to `m^8 * loss/alpha < 2/d0^2`, about 63.56. This run has four
   symbolic identities, 15 tiny-order/zero-limit cases, 15 growing-order
   actual-state comparisons, 45 exact derivative evaluations and 15 samples
   of one fixed state at later orders up to 1e30. The smallest positive
   tiny-order sample is 1e-500. The alpha=0 cases are analytic limits only.
   The successful script uses 220-digit arithmetic and factors out alpha
   before evaluating the small-order gain and rounding loss.

3. `20261015T084023.622885Z`: **PASS**, with exactly the same mathematical
   controls and three rejected variants. The previous reviewer-L constant
   result was copied into this review's own snapshot and the checker now
   reads that local copy rather than depending on a sibling review's
   runtime path. Its SHA and bytes are identical. One phi helper docstring
   was also clarified: its critical-equation evaluation uses alpha about
   0.55, and the exact formula is regular away from one, not restricted to
   alpha<=0.5. No calculation or bound changed. This final run makes the
   packaged independent control self-contained under this review directory.

Both successful runs execute three incorrect assertions and retain
their actual AssertionError records in separate `REJECTED-*.json` files:

- Omitting the head's trace-normalization logarithm predicts an order-two
  D-scaled head gain tending to three; the actual gain tends to one.
- A cutoff `2*log(m)/log(2)` does not let this one-state argument beat the
  universal `log(1+t)` bulk upper bound. At m=48000 the proposed state's
  deficit is about 3.90815e-6 whereas that upper bound is about 4.16667e-5.
  This rejects that proposed monotonicity bridge, not all conceivable
  arguments using a different state or a sharper bulk bound.
- An absolute `m^-8` error cannot be dominated uniformly by a leading
  `alpha*m^-3` advantage when alpha can be arbitrarily tiny. This is a
  rejected inference about error estimates, not a counterexample to the
  actual small-order APPT witness.

The reviewer wrote all scalar functions in the new checker. It imports no
author helper and performs no AST extraction of author functions. Its a_c
illustration is read from the reviewer's previous L diagnostic, whose full
RESULT bytes and SHA are retained in the successful run. Alpha_0 and d0 are
independently resolved anew from the three critical equations. None of
these decimal calculations is an interval certificate.

The separate author run `20261015T083026.400414Z` was read, copied and hash
checked only. It reports PASS for 18 tiny-order cases to 1e-1000, 15 growing
order cases, 45 exact derivative cases and 15 later-order samples to 1e12.
Its source openly AST-selects nine pure scalar functions from the author's
L checker without running L's execution body. That reuse belongs to the
author's checker, not to this reviewer's new implementation.

Finite calculations and rejected variants diagnose implementation and
proof sensitivities. They do not establish the manuscript's continuum,
unbounded-order, original-all-APPT or all-later-dimensions quantifiers.
Those quantifiers are assessed by the ordinary mathematical read in REVIEW.md.
