# Fractional covering spectra and stability of intersecting extremizers

mxym/math research project. AI-assisted manuscript, 7 October 2026.

We determine the sharp asymptotic fractional vertex-cover frontier at every
finite edge/rank ratio, characterize the near-extremizers at its integer
design boundaries, and determine the entire frontier with any fixed matching
bound. A finite allocation formula also identifies the limit when the matching
number diverges. The finite upper bounds require no linearity or small-codegree
assumption. The near-design statement requires uniform edges; that hypothesis
is retained throughout Part D. These are fractional assertions except for the
explicitly designated integer-cover corollaries.

The paper has three connected parts, each with a complete proof. Definitions,
theorems, equations and sections are prefixed F, D or S. References within a part
use its own prefix; the common finite LP duality argument is included rather
than left to an external computational solver. The repeated local conventions
make the changes in hypotheses visible. Part S needs an anchored inequality,
not a partition into intersecting subfamilies: arbitrary pairs of edges in an
anchor group may be disjoint. Its common-rank constructions work at every
sufficiently large integer rank, which is essential for both sharpness claims.

Classical inputs are Wilson's fixed-block design existence theorem and Kahn's
small-intersection covering corollary, stated precisely in the proof. They enter
the sharpness constructions and designated integer-cover corollaries, not the
finite signed-counting upper bounds. Füredi--Kahn--Seymour is prior context and
is not claimed to be resolved in its general weighted nonuniform formulation.
The results neither settle Ryser's conjecture nor Kahn's triple-intersection
question. An exact finite maximum for every arithmetic pair of rank and edge
count is also outside the statements.

The accompanying reproduction guide pins the three source papers and their
checkers. Lean establishes the indicated finite incidence/anchor/extraction
lemmas, not Wilson's theorem, the LP duality appendix, all constructions, or the
asymptotic spectrum. The written proofs supply these remaining steps.
Literature comparison is provisional; no historical priority claim is made.
