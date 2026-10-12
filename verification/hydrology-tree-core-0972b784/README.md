# Independent Lean verification — 0972b784

Scope: **Exact multivariate coordinate multiplicities and full real-rate singular/cancellation boundary classification; overall partial**

Verified source commit: `0972b78488aa278253939110dbf36dffde6b18cd`.
Independent run: https://github.com/mxym/math/actions/runs/38214070949

All 110 owned modules compiled in a new Lake source tree and a
separate fresh object tree. 962 audited roots and 43,839
used declarations were replayed into an empty kernel at trust level zero.
Only `Classical.choice`, `propext`, and `Quot.sound` occurred as axioms.
All 41 intentionally incorrect source mutations were rejected.
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
