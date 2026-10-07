# Mathematical and replay audit

The rank bound is an integer r>=2, all edges are nonempty, and s>=1.
Empty families are handled separately. The fractional optimum exists
in a compact finite cube; finite LP duality is explicitly referenced
to the preserved predecessor's separation proof. No solver output,
OpenAI/math theorem or experimental vector is a mathematical input.

An anchored group is not assumed pairwise intersecting. Its maximum
weight anchor meets every other edge. That is precisely enough for
the signed assignment, capacity and rank arguments in the frozen Lean
base. The half bound instead uses each anchor pair constraint plus
the maximum-weight inequality. A nonmaximum anchor would be invalid;
the checker includes three disjoint leaves of unit weights against a
zero-weight common anchor as a negative control.

Greedy groups genuinely partition the original edges. Feasibility
persists under restriction because all weights are nonnegative.
Every later anchor is disjoint from every earlier one, so group count
is bounded by the actual matching number. Single-edge groups have
error 1/2; other groups have error at most 1/2, including their
reciprocal endpoints. The total error is thus at most s/2 and is
universally attained on disjoint single-edge components.

The spectrum's maximum is compact. Its continuity follows from the
explicit trimming Lipschitz argument. Convexity is used only within
integer unit boxes, not asserted globally for psi. Moving two noninteger coordinates in opposite directions preserves
their sum. One endpoint of their allowed segment has at least the same
objective and an additional integral coordinate. Repetition leaves at
most one noninteger coordinate. The remaining integer
allocation is balanced by a strict unit-transfer argument. Zero
coordinates and theta=0 are included. Rational grid diagnostics are
not offered as a proof of the continuous reduction.

Common-rank sharpness is not deduced by intersecting arbitrary existing
subsequences. Wilson's admissible replication progression is within
O(1) of any large prescribed rank. For plateaus a smaller original
rank is padded privately, with zero primal weights on new vertices.
For ramps the design point count is the largest admissible value below
xR. At integer endpoints no plateau extension or Kahn theorem is
needed. A zero-density component is one full-rank edge. Disjoint unions
have exactly s matching edges and additive fractional optima. The
prime-power subsequences are not used to assert all-rank construction.

The concave interpolation h has decreasing slopes. Jensen gives the
relaxation; at integer total edge/rank ratios balanced allocations
attain it. At noninteger totals greater than s, equality would force
integral coordinates, which is impossible. The uniform error bound
between the spectrum and the concave relaxation is less than 1/2.
Diverging-matching sharpness uses only two fixed integer endpoint
families, so their per-component O(1) errors remain O(1/R) after
normalization, regardless of the number of components.

Three additional Lean exports compile with only propext,
Classical.choice and Quot.sound. The copied base is byte-identical to
the frozen nine-export predecessor. This formalizes the actual finite
anchor incidence argument and half bound, not the entire greedy or
asymptotic theorem. A whole-paper formalization is not claimed.

Exact replay uses explicit RuntimeError checks surviving Python -O.
Feasible vectors are exact fractions; matching numbers in small random
families are exhaustively computed by a separate recurrence. Fixed
union certificates verify all primal and dual constraints. The
independent grid convolution does not use the closed balancing formula.
The requested Luna agent performed source comparison, not proof review.
This is self-review without an external mathematician; no historical
priority or prize classification is asserted.
