# Independent Lean verification — 4ae77baf

Scope: **All-real arbitrary-leak formal Jacobian polynomial and actual Frechet evaluation, including zero boundaries; exact alternate-leak multiplicity extension is certified separately**

Verified source commit: `4ae77baf1e80f53f034ac66302d677e0a5b581ae`.
Independent run: https://github.com/mxym/math/actions/runs/38379758652

All 214 owned modules compiled in a new Lake source tree and a
separate fresh object tree. 1639 audited roots and 53,324
used declarations were replayed into an empty kernel at trust level zero.
Only `Classical.choice`, `propext`, and `Quot.sound` occurred as axioms.
All 88 intentionally incorrect source mutations were rejected.
The fixed Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
and transitive dependency source revisions were checked; before/after source
hashes matched. These are the original completed run's logs, not development
compiler diagnostics or a claim about later source revisions.

`original-actions-artifact.zip` is the unmodified GitHub artifact. The other
verification files and deterministic owned-source archive were extracted from
it. `PROVENANCE.json` records API identifiers and exact binding; `SHA256SUMS`
binds all archived files. The original archive contains the complete build,
axiom, empty-kernel and negative-control logs.

This receipt certifies only the exact source commit and stated scope above.
Read the source-bound GAPS.md and FORMAL_THEOREMS.md for the mathematical
hypotheses and exclusions. Later extensions require their own verification;
a successful earlier receipt does not certify any later source bytes.
No complete-program Release, DOI, or external human peer review is claimed.
