# Independent Lean verification — ad92bfe7

Scope: **Finite-tree theorem core with all-real arbitrary-leak formal Jacobian, exact original-coordinate multiplicities and full zero-boundary singular set; precise model exclusions retained**

Verified source commit: `ad92bfe7eb26e77fb3fb8ee80af6a6cbca36caea`.
Independent run: https://github.com/mxym/math/actions/runs/38380948444

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

## Final mathematical boundary closure

`finite_graph_complete_all_leak_algebra` constructs graph presentations and
proves the actual formal determinant factorization for every leak site and all
real rates. `formalLocatedJacobian_exact_power` excludes every next coordinate
power; `symbolicLocatedResidual_no_coordinate_factor` supplies universal
coordinate-hyperplane witnesses. `locatedJacobian_zero_iff_all_rates` includes
all signed and zero-rate boundaries. The leak-variable exponent is zero.

The old report's short scope string was inherited from an earlier root-only
checkpoint and is conservative but outdated. The actual 220-module source,
1677 audited roots and literal logs establish the scope recorded above. A
separate metadata-only revision binds current scope documents into its own
source manifest and receives its own independent verification. The distinction
is not hidden by editing this original artifact.

See SCOPE_AUDIT.md for semantic exclusions and the distinction between deliberate
source-mutation rejection and logical falsity of every mutated statement. The
213 retained module objects match the preceding independent run byte for byte.
