# Pre-handoff mathematical and reproduction checks

Date: 8 October 2026. This records author-side checks; it is not a claim of
independent journal refereeing or Lean verification.

## Mathematical scope checks

- C(A) deletes row i and column j, without transposition; inner products are
  linear-first. G_w therefore uses conjugate(w_i).
- Positivity, row sums, double-coset contraction positivity, and the indicator
  decomposition upper bound are included in the main paper, with no dependency
  on separate internal notes.
- The ring entropy lemma applies to every subset. Random signs are independent
  subset characters; coincident degree sums do not invalidate the expectation
  identity. The sign choice is finite for each N.
- The main lower construction uses exactly N rows, has rank two for every
  sufficiently large N, and fixes parameters before taking N to infinity.
- The real-direction lower bound uses w=Im z and sum z_i^2=0 in the sharp family;
  it does not assume a real eigenvector of a complex matrix.
- The explicit dyadic family has a nonzero size-two-ring second moment. Its
  separate (K+1) real-direction factor is retained, not replaced by K.
- Ramp sharpness is a limsup. Its cofactor upper bound is all-rank, but the S
  polynomial endpoint conversion and pi^2/8 assertion are rank-two statements.
- The CP1 lower construction uses bounded truncations before moment limits and
  cancels poles before applying concentration. The base is fixed before its
  repetition limit. No growing-k compound argument is used.
- Positive-definite perturbations do not retain rank two. Real-Rayleigh maxima
  allow complex A and are not maxima over real matrices.
- Lieb/Marcus are explicitly left unresolved. The Pate 2008 full-text limit is
  recorded without attributing an error to its theorem.

## Exact arithmetic reproduction

The primary verifier passed at (K,c)=(8,7),(10,5). The independent marked-product
verifier matched all five exact integers in each case, byte-for-byte through
the deterministic value JSONs. Their common value hashes are

- K8/C7: 50e9496db7b33781f128e5650744ccb87f3672e4205136e10412c8e93cae5f80
- K10/C5: 8148292bdf8b86b554bfc3f53ac5027bd3bac20283f7baf3f4ddbe0aa4920396

The independent checker additionally evaluated the order-eight Gaussian-integer
Gram matrix 20J+3tt*, its permanent, all 64 deleted cofactors, their row sums,
and both full Rayleigh quotients, agreeing exactly with the polynomial formulas.
The rank-two exclusion thresholds passed integer/fraction checks.

All 12 optimized-mode negative tests (-O, -OO, PYTHONOPTIMIZE=1, and =2 for each
of the three programs) exited nonzero with the expected rejection. All existing
JSON outputs remained unchanged. See OPTIMIZATION_GUARD_RESULT.json.

## Document checks

The final TeX compiles to nine pages. It has no overfull boxes, unresolved
references, or missing-glyph warnings. All pages were rendered for visual
inspection, with full-page inspection of the dense formula pages and the final
references page. No clipping, overlapping equations, or broken table cells were
observed. One harmless underfull bibliography-line diagnostic remains.

The PROOF.md text rendering was generated from the final TeX and has its
structural HTML wrappers removed. The TeX/PDF remains the typeset reference.
No third-party paper downloads or mirror directories are included.
