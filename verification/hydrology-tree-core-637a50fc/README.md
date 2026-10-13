# Independent Lean verification — 637a50fc

Scope: **Exact all-real-rate signed characteristic/cofactor resultant–Jacobian identity; overall partial**

Verified source commit: `637a50fc3b724b5394d86f5e88f6ed16ce043565`.
Independent run: https://github.com/mxym/math/actions/runs/38212403838

All 100 owned modules compiled in a new Lake source tree and a
separate fresh object tree. 897 audited roots and 43,475
used declarations were replayed into an empty kernel at trust level zero.
Only `Classical.choice`, `propext`, and `Quot.sound` occurred as axioms.
All 38 intentionally incorrect source mutations were rejected.
The fixed Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
and transitive dependency source revisions were checked; before/after source
hashes matched. These are the original completed run's logs, not development
compiler diagnostics or a claim about later source revisions.

`original-actions-artifact.zip` is the unmodified GitHub artifact. The other
verification files and deterministic owned-source archive were extracted from
it. `PROVENANCE.json` records API identifiers and exact binding; `SHA256SUMS`
binds all archived files. The original archive contains the complete build,
axiom, empty-kernel and negative-control logs.

The overall research formalization is PARTIAL. The positive-realization
existence and exhaustive factorial fiber count, external graph and alternate
leak presentations, and remaining ODE interpretation still require proofs.
No complete-program Release, DOI, or external human peer review is claimed.
