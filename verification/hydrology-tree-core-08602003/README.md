# Independent Lean verification — 08602003

Scope: **Closed finite-tree theorem core with all-real arbitrary-leak Jacobian, exact multiplicities, real-fiber and continuous-ODE theory; scope documents and dependency graph cryptographically bound**

Verified source commit: `08602003af46b2a16aa33d7c7c429a197ab607d6`.
Independent run: https://github.com/mxym/math/actions/runs/38381821927

All 220 owned modules compiled in a new Lake source tree and a
separate fresh object tree. 1677 audited roots and 53,370
used declarations were replayed into an empty kernel at trust level zero.
Only `Classical.choice`, `propext`, and `Quot.sound` occurred as axioms.
All 91 intentionally incorrect source mutations were rejected.
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

## Exact scope and main-source binding

All 235 proof, reproduction and public-scope inputs are checked. The current
README.md, GAPS.md, FORMAL_THEOREMS.md, DEPENDENCY_MAP.md and actual owned import
DAG are bound into the manifest and verified source archive. All 220 compiled
module objects, including the aggregate entry, match the preceding mathematical
proof checkpoint byte for byte.

The source inputs at main integration commit c2a2ce36 are identical to this
independently verified source. Its main-triggered full build has a separate
run and must be reported under its own status; MAIN_SOURCE_BINDING.json does
not pretend a pending run has passed.

The declared finite-tree proof chain is closed within its explicit assumptions.
The remaining exclusions are different target classes and solution notions,
not axioms or missing lemmas smuggled into the main result. SCOPE_AUDIT.md records
those distinctions and the deliberate SOURCE-mutation interpretation of the
negative controls. No novelty, DOI, completion Release or human review is claimed.
