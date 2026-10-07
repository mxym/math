# Twenty-edge obstruction: proof and verification scope

The universal finite deduction is in `paper.md`. It uses the known
lower bound f(6)>=13, equivalently a four-cover for every
six-partite intersecting family with at most twelve edges. The primary
Abu-Khazneh–Pokrovskiy manuscript Theorem 1.1 / Section 2.1 was read for
its assumptions and proof type. The independent ABW result is published.
AP's Lemma 2.9 is phrased for tau=5: the manuscript's greedy covers
and low-degree pair counts also exclude tau=6. Its lower bound imports
the earlier MSY exclusion of at most eleven edges; it is not a solver
result. Appendix A supplies a complete at-most-eleven reduction and
the short, explicitly attributed ABW twelve-edge proof. Thus the
full note needs no unproved external lemma.

Self-review checked active vertices only, the degree-one five-cover,
the precise maximum-degree implication of Input F, the first-edge
count excluding N<=16, integer rounding of the N=17 energy bound,
convex transfer and every permitted part width at N=19, and the
zero-excess argument when a part lacks a degree-six vertex.

In the new obstruction, four selected vertices leave at least three
uncovered edges. The union lower bound is valid with any higher overlaps.
Every selected pair occurs in exactly six four-subsets. Double counting
Q uses only vertices from different parts and original distinct edge
pairs. At total excess at most three, Q>=5 forces exactly one fourfold
intersection. That exceptional edge pair permits a repeated selected
vertex-pair only within its four shared parts. Selecting two of those
parts and both outside parts yields the contradictory sum at most seven.

The complete twenty-edge width budget is separate from the exclusion
theorem. Its maximum-degree and width deductions have full hypotheses;
edge criticality uses the new at-most-nineteen theorem. No timeout or
solver UNSAT output is promoted to a theorem.

The standard-library checker generates all relevant degree partitions
in two independent ways, checks all six-part degree choices and the
exact excess/support lists. An incorrect maximum is detected as a
negative control. The appendix degree identities and the attributed
thirteen-edge example's exact cover number are also checked. It runs
unchanged with Python -O. Nine Lean exports
prove universal scalar pieces; recorded axioms are standard logical
axioms only. Hypergraph reductions and the full appendix are not formalized.

The optional SAT source is included as a discovery experiment, outside
the proof dependency graph. The recorded 240-second run found no checked
counterexample and produced no nonexistence certificate. Its parameters,
source hash and output are recorded separately.

All prior frozen packages remain unchanged. The requested Luna agent
checked prior-source scope, not this proof. This is self-review plus
partial kernel checks and exact diagnostics, without external
mathematician review or a priority determination.
