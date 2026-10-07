# Proof dependencies and verification scope

The complete deduction is in `paper.md`. Kahn's small-codegree theorem,
as stated in Kang--Kelly--Kühn--Methuku--Osthus Theorem 3.1, is an external
published input. Its rank-at-most-four hypothesis includes the mixed
three/four-block graph; the degree threshold and codegree-one condition
are checked in every application. The input is not re-proved or Lean-
formalized here. `results/source.txt` records its primary manuscript and
downloaded SHA256. Sivashankar's degree-three lemma is the other inherited
input and is included with its full attributed proof. Peeling, pair-excess
deletion and the four-block matching/star framework also follow his Section 4.

The new part is the weighted simultaneous three/four-block linearization,
coupling of retained weight to cover saving, and explicit global
intersection-excess penalty. The linear and near-linear coefficient and
quadratic-excess obstruction follow by stated limit operations. The earlier
13/4 and 10/3 packages remain unchanged; these are stages of one programme.

Self-review covered the original versus residual excess, nonnegative pair
summands, incidence multiplicity, initial repeated auxiliary blocks,
deletion weight at most one, linear mixed-block degree bounds, weighted
colour-class averaging, pairing ceilings, distinct original vertices
defining retained blocks, small-degree cases, q<=r, both scalar ranges,
negative target values, irrational constants and all additive errors.
Repeated original edges are removed before applying the simple theorem.

The exact checker verifies both scalar factorizations coefficientwise and
the constants in Q(sqrt(17)), including signed comparisons and a damaged
factor negative control. It independently implements the weighted deletion
budget and exact weighted matching search on every intersecting binary-width
family in ranks two and three and selected duplicate/F3/F2 examples.
Earlier exact finite-field and elementary diagnostics are also retained.
All arithmetic is integer/rational; no floating point, heuristic solver,
sampling assumption or assertion disabled by Python -O enters verification.
Finite examples are diagnostics, not the proof of the universal theorem.

Six Lean exports check the two factorizations, their range implications,
the defect-error comparison and the final cover algebra. Constants are
formalized through their explicit interval and quadratic hypotheses; the
written squaring argument and exact quadratic-field checker verify the
particular value. The combinatorial reductions, appendix graph cases and
Kahn input are not formalized in this file. The kernel output records only
propext, Classical.choice and Quot.sound; no unproved placeholder occurs.

`verify.py --lean` checks the 17-file frozen inventory, ordinary and
optimized exact replay, kernel replay and recorded axiom equality. Hashes
verify integrity, not the theorem. The PDF is generated from the Markdown
proof; equation labels in its appendix are distinct from the main text.

The separate explicitly requested Luna literature agent compared the global
excess penalty against named sources. Its limited negative search does not
establish priority or audit the proof. No external mathematician has
reviewed the note; no human peer review, novelty determination or major
conjecture resolution is claimed.
