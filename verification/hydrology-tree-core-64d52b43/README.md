# Independent Lean verification — 64d52b43

Scope: **Complete all-real full-positive-response classification, automatic positivity and exact root-storage/discharge fiber count with recovered leak; overall graph/leak-location/ODE variants remain partial**

Verified source commit: `64d52b4358a7402e7b983f61a508fdf651ce0b61`.
Independent run: https://github.com/mxym/math/actions/runs/38240534162

All 141 owned modules compiled in a new Lake source tree and a
separate fresh object tree. 1155 audited roots and 44,424
used declarations were replayed into an empty kernel at trust level zero.
Only `Classical.choice`, `propext`, and `Quot.sound` occurred as axioms.
All 58 intentionally incorrect source mutations were rejected.
The fixed Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
and transitive dependency source revisions were checked; before/after source
hashes matched. These are the original completed run's logs, not development
compiler diagnostics or a claim about later source revisions.

`original-actions-artifact.zip` is the unmodified GitHub artifact. The other
verification files and deterministic owned-source archive were extracted from
it. `PROVENANCE.json` records API identifiers and exact binding; `SHA256SUMS`
binds all archived files. The original archive contains the complete build,
axiom, empty-kernel and negative-control logs.

The overall research formalization remains PARTIAL for independent graph
presentations, alternate leak placement and actual ODE/system interpretation.
The original root-leak model's positive realization existence, exhaustive
recursive allocation bijection and exact factorial fiber count are proved.
This receipt covers ONLY the exact source commit and scope stated above.
No complete-program Release, DOI, or external human peer review is claimed.

## Mathematical closure in this checkpoint

For every original labelled OrderedTree with N=n+1 vertices and every normalized
full N-mode target G(s)=sum_i w_i/(s+r_i), with distinct r_i>0, all w_i>0 and
sum_i w_i=1, the entire REAL root-response fiber is in explicit equivalence
with the recursive labelled pole-allocation type. Every real realization is
strictly positive, and every actual coefficient Jacobian in the fiber is nonzero.
No sign or regularity restriction is assumed on the competing real parameters.
The finite exact cardinality is (N-1)! / product_(nonroot v) |T_v|, with original
labels retained and no tree-automorphism quotient.

The same exact all-real count holds for the actual root-discharge transfer
H(s)=ell*G(s), with ell=1/(sum_i w_i/r_i). The leak is identified from equality
of discharge transfers, not supplied as a separate observation.

Primary entries: real_stieltjes_realization_is_positive,
realResponseRecursiveEquiv, real_root_response_fiber_exact_card,
real_full_response_forces_positive_regular, stieltjes_discharge_iff_root_response,
and real_discharge_fiber_exact_card. Full source-level hypotheses and the
explicitly excluded variants are recorded in SCOPE_AUDIT.md and GAPS.md.

The complete written proof and conservative primary-literature novelty audit
are under research/hydrology-tree-real-fibers/. No assertion of historical
priority follows from kernel checking. CROSS_RUN_CHECK.json separately compares
the retained object hashes; ROUND_RUNS.json confirms that all four formal
verification runs in this development cycle completed successfully.
