# Proof and replay audit

The theorem concerns fractional vertex covers of a finite simple
intersecting family of nonempty edges, each of size at most r>=2.
The maximum feasible edge weight exists and lies in [0,1]. Finite
LP duality is stated and proved from finite-dimensional separation.
No OpenAI/math theorem or solver status is a proof input.

The star inequality allows repeated intersections because its weights
are nonnegative. The signed argument instead assigns each other edge
to exactly one intersection vertex. This preserves both its total
weight and edge count. Individual signed costs can be negative, so
replacing the partition by a repeated incidence sum would be invalid.
The checker contains an explicit negative-cost example distinguishing
these sums.

The bin proof splits integer counts at k-1/k. Its upper reciprocal
endpoint has B=0 and is included. Its lower endpoint is handled by the
average branch; empty bins satisfy the first case. Rank replacement
uses a positive factor, not a signed one. The remaining expression is
affine, so both possible slope signs are covered. All high-peak, middle
and low-peak cases are exhaustive; m=1 and the c=0 limit are separate.

The limiting curve is continuous at integer endpoints and switches at
a+1-1/(a+1). Upper bounds take k fixed before passing to the limit.
Wilson's fixed-block existence theorem is imported, not reproved.
Its admissible v=1+k(k-1)N sequence has replication kN. The incidence
duals are simple for replication at least two, are linear, and have
explicit feasible primal/dual objectives v/k. Kahn's Corollary 5.4 is
used on these linear families: take the limsup at each fixed a+eta,
then eta down to zero. This yields an integer cover below replication.

Plateau edges use only old vertices and contain that integer cover.
A fixed set of r0-1 old vertices leaves Theta(r0 squared) candidates,
whereas only O(r0) are forbidden or requested. Skipping old edges
preserves simplicity. Old dual weights extended by zero and old primal
weights 1/r0 certify the exact objective on the enlarged family.
Ramp padding is private to each edge, preserves pair intersections,
and has zero primal weight. The prescribed new rank is at least the
original replication. These constructions prove existence at every
fixed real ratio; no algorithm to construct arbitrary Wilson designs
or find Kahn's covers is asserted.

The explicit affine partial-pencil extension uses one old line in
each direction class. Points inside its chosen two-space are covered
by the shifted pencil; points outside are covered by the unchanged
zero-line. Two new edges retain a common zero-line outside their two
spaces. At least two changed directions recover the space, while two
unchanged zero-lines exclude any original pencil. The Gaussian count
provides Theta(v squared) choices. A whole original parallel class is
an exact integer cover. Private ramp padding has one new part for each
padding position. F4 arithmetic is independently replayed with exact
finite operation tables. In the cloned-class ramp each point edge gains
t private copies of its incident class line; pair excess is exactly tv.

In the strict ramp A>0, an optimal vector at equality must have every
weight 1/(k+1), giving the precise degree cap. The near-equality
condition is strict d<A/[k(k+1)], which rules out the high-peak branch.
The proof separates a peak below the lower reciprocal endpoint from
a peak above it; it never sums negative peak deficits. Deleting weights
at or below 1/(k+2) leaves a strict degree threshold. The finite bound
handles d=0, zero-weight edges and empty cores. In the limiting iff,
A/r has a positive limit, so the deletion bound is o(r). A partial-pencil family at a prime-power phase switch attains the
frontier but requires Theta(r) deletions for degree at most k+1: any
k+2 new edges share an unchanged zero-line for sufficiently large rank.
A fixed boundary example checks all 1,820 four-new-edge intersections.
Thus the iff cannot include the switch. No integer rounding follows
from the degree criterion.

Nine Lean exports compile with only propext, Classical.choice and
Quot.sound. They include a genuine finite sum and construct the
bins from actual hypergraph incidence. The main finite dual upper bound
is proved from nonnegative edge weights and the vertex constraints, with
no bin or star premise supplied by the caller. LP duality, degree
extraction, classical inputs and limits are not formalized here.
Exact replay uses RuntimeError checks that remain enabled under -O.
Primal and dual constraints are checked independently for each fixed
construction. The rational diagnostic grids illustrate the proofs;
finite grids are not offered as proofs of universal statements.

The requested GPT-6 Luna High agent compared prior literature, not
mathematical validity. Its limited non-hit does not establish novelty.
This audit is self-review, not independent external mathematician review.
