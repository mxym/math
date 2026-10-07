# Proof dependencies and self-review

The full mathematical deduction is in `paper.md`, Sections 2–6. The
sole non-elementary input is Kahn's small-codegree edge-colouring
theorem, stated as Theorem 3.1 of Kang–Kelly–Kühn–Methuku–Osthus.
Section 1.2 of the inspected primary manuscript explicitly allows
parallel edge identities; maximum degrees and codegrees count them.
The source hash and URL are recorded in `results/source.txt`.
No OpenAI/math theorem, degree-three preprint lemma or unverified
solver output is an input.

The preceding notes and Sivashankar Section 4 supply relevant context
for peeling, pair-excess deletion and matching covers. This note uses
different multiplicities: a size-d incidence block produces d-1 copies,
each of weight (d-2)/2. Linear retained blocks bound the copied degree
by the number of other original edges. Integer degree counts give a
piecewise linear cover envelope without needing parts.

Self-review checked all of the following points:

- Original edges are distinct; equal auxiliary blocks retain identities
  before deletion, and parallel copies retain identities afterwards.
- Deletion concerns auxiliary blocks, not original edges or their cover
  number. Each deletion decreases pair excess and loses at most g_D
  weight. The lower weight estimate may be negative and is used safely.
- A colour class selects each original block at most once; its cover
  saving and pairing ceiling are accounted for explicitly. Empty weight
  uses the empty matching. The copied maximum degree is bounded by
  q-1 even if retained blocks no longer cover every pair of points.
- The colouring input uses a declared degree upper bound, with fixed
  rank and bounded copy codegree. Below the finite threshold the proof
  uses pairing. Empty residuals and q at most r are separately covered.
- The integer vertex-count inequality holds for every positive integer
  degree, including degree one. All envelope breakpoints, the harmonic
  comparison and the strict peeling slope are written explicitly.
- Equality arguments fix the peeling threshold before limits and then
  send the colouring error to zero. Peeling does not depend on that
  error. Deleting o(r) original edges changes active-vertex counts by
  at most o(r²), permitting moments on the original family.
- Noninteger equality uses an L1 regularity estimate, not pointwise
  regularity. Removing o(r) bad auxiliary points costs o(r²) blocks
  because every point has degree at most r. The rank of the final
  matching system is fixed k+1. The quantitative proof fixes the peeling
  threshold 2k(k+1), bounds the integer degree defect by 2k²(k+1)²
  times the cover deficit, and gives an explicit conservative gap. A
  potentially negative matching-size lower bound is used safely.

The standard-library checker independently counts original intersections,
degree moments, copied degrees and codegrees, auxiliary deletion losses
and matching cover costs. It covers all 1051 intersecting set families
in two specified small universes, a nonpartite Fano family, a repeated
incidence core, five affine-space constructions and padded pair
constructions. Rational envelope diagnostics and an incorrect-copy
negative control are included. Its greedy colourings use their actual
colour counts; no finite example is assigned Kahn's asymptotic bound.
Both normal Python and Python -O replay are required; checks use explicit
exceptions rather than assertions.

Fourteen Lean exports verify the integer gap, copy weight, degree polynomial,
envelope crossings, harmonic identity, colouring error, peeling slope,
variance expansion and noninteger positive gap. Their recorded axioms
are only propext, Classical.choice and Quot.sound. These are universal
scalar statements, not a formalization of the entire proof.

The requested Luna agent performed a limited literature comparison;
it did not review the proof or establish priority. There is no outside
mathematician review. The payload includes a readable eight-page PDF,
source, reproducible diagnostics and pinned Lean replay. Hash verification
checks integrity. The general nonlinear problem, the best
noninteger gap and a superlinear growth rate remain open here.
