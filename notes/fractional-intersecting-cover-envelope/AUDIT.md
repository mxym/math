# Proof and verification audit

The universal deduction is written in paper.md. This note does not
depend on an OpenAI/math mathematical claim, a numerical optimizer,
Kahn's rounding theorem, or the preceding integer-cover notes.

The proof was checked for: nonnegative dual weights; repeated
intersections in the star count; the strict threshold defining G;
the fact that a maximum-weight edge belongs to G; capacity k-1
for its other threshold edges; the full domain g<=m<=kr; positivity
of every division and substitution coefficient; and the separate
small-maximum branch. The finite numerator and comparison factor
are expanded explicitly rather than inferred numerically.

Equality uses all equality conditions: full threshold count, two
constant weight levels, star saturation and positive substitution
coefficient. The forbidden outside-edge calculation is strict.
After m=g is established, uniform positive weights let the same
star argument force linearity at every edge and degree k at every
active vertex. The converse has matching explicit primal/dual
certificates. It requires neither existence nor resolvability of
an arbitrary Steiner design.

The additional noninteger gap proof tracks the exact two-level mass
defect. Its near-equality branch excludes small maximum weights
before dividing by a_0. Both threshold margins, the fixed positive
low-weight bound and the capacity M are checked explicitly. The
count of vertices meeting low-good edges is a lower bound even
with repeated intersections. The limit order uses fixed constants
and subsequences only; no unproved uniform colouring claim enters.

The LP primal can be clipped into a compact cube. The dual cube
is compact since all original edges are nonempty. Appendix A gives
a finite cone-separation duality proof, naming its standard convex
separation input. It handles the possible zero separator component
explicitly. That background theorem is not formalized.

The checker replays ten fixed rational optimality certificates:
all primal constraints, all dual constraints and equality of the
objectives are verified independently. It also checks incidence,
uniformity, simplicity, the theorem's finite bound and equality
classification. The parameter grid uses exact Fractions, not floats.
An infeasible dual, an omitted finite correction and promotion to
integer covers are negative controls. Python -O preserves every
check because none uses assert.

Twelve Lean exports prove algebraic identities and inequalities,
including weighted elimination and the strict forbidden-edge
inequality. Their axioms are recorded. These are partial exports;
the full finite hypergraph counting and LP theorem are not in Lean.

The requested Luna agent performed limited prior-work comparison,
not proof review. There is no external mathematician review or
verified historical novelty. Frozen predecessor packages are
preserved, including the public Kahn prior-work corrections.
