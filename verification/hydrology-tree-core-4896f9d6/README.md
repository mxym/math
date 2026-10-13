# Independent Lean verification — 4896f9d6

Scope: **Exact attained minimum-energy actual state steering with closed-interval equality classification and complete root-leak dynamics; independent graph and alternate-leak variants remain partial**

Verified source commit: `4896f9d6d2da881ee5440346177a0a2ced1061aa`.
Independent run: https://github.com/mxym/math/actions/runs/38335338754

All 168 owned modules compiled in a new Lake source tree and a
separate fresh object tree. 1276 audited roots and 52,031
used declarations were replayed into an empty kernel at trust level zero.
Only `Classical.choice`, `propext`, and `Quot.sound` occurred as axioms.
All 70 intentionally incorrect source mutations were rejected.
The fixed Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
and transitive dependency source revisions were checked; before/after source
hashes matched. These are the original completed run's logs, not development
compiler diagnostics or a claim about later source revisions.

`original-actions-artifact.zip` is the unmodified GitHub artifact. The other
verification files and deterministic owned-source archive were extracted from
it. `PROVENANCE.json` records API identifiers and exact binding; `SHA256SUMS`
binds all archived files. The original archive contains the complete build,
axiom, empty-kernel and negative-control logs.

The original root-leak model's actual continuous-input ODE, finite-horizon
signed controllability and finite-window observability are proved. The energy
checkpoint also proves the attained exact minimum control energy and complete
equality classification on the closed control interval. Independent graph
presentations and alternate leak placement are not certified by these source
checkpoints. This receipt covers ONLY its exact commit and stated scope.
No complete-program Release, DOI, or external human peer review is claimed.
