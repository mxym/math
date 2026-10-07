# Scope of the Lean verification

Lean 4.34.1 and transitive dependencies are pinned. Mathlib revision:
d13f23b723b8a846827a245b89c10fc7d3f11612.

Nine kernel-checked exports in FrontierCertificate.lean:

- `signed_bin`: the two integer-count branches of the signed inequality,
  including both reciprocal endpoints under the stated capacity bounds.
- `sum_signed_bins`: an actual finite sum of the bin inequalities.
- `signed_elimination`: the affine expression after summation.
- `affine_endpoint_bound`: both signs of that affine slope.
- `three_peak_branches`: the exhaustive average/star/bin scalar branches.
- `ramp_peak_control`: high-peak exclusion and the quantitative peak
  deficit inequality in the strict near-equality ramp.

- `assignment_sum`: each edge assigned once to a vertex preserves an
  actual finite sum.
- `incidence_bin_data`: constructs the assignment from actual pair
  intersections and proves both the star and signed-count inequalities
  directly from the vertex feasibility constraints and rank bound.
- `incidence_frontier`: chooses a maximum-weight edge and proves the
  finite main bound for every feasible edge-weight vector on the actual
  hypergraph, without a supplied bin or star assumption.

All printed axioms are exactly propext, Classical.choice and Quot.sound.
There is no `sorry`, `native_decide` or custom axiom. The finite dual
upper-bound argument, including the hypergraph-to-bin assignment and
partition identities, is formalized. This is still a partial paper
formalization: LP duality, the degree/deletion extraction, published
design and covering inputs, and limit arguments are not formalized here.
The full written proof makes each additional step explicit.

Run `./bootstrap.sh` from a fresh checkout, followed by
`lake env lean FrontierCertificate.lean`. The existing manifest is
preserved; bootstrap does not run `lake update`. The shared cloud
package cache is git-ignored and not a reproducibility dependency.
The official Lean compiler, kernel and dependency builds are trusted;
no separate kernel implementation or external human review is claimed.
