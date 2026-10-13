# Independent Lean verification — c423e6fc

Scope: **Complete root-leak continuous-time dynamical classification and actual finite-horizon signed controllability; independent graph and alternate-leak variants remain partial**

Verified source commit: `c423e6fc1739f3e3ca67e83797cb76bd3a324fca`.
Independent run: https://github.com/mxym/math/actions/runs/38334828785

All 164 owned modules compiled in a new Lake source tree and a
separate fresh object tree. 1250 audited roots and 51,979
used declarations were replayed into an empty kernel at trust level zero.
Only `Classical.choice`, `propext`, and `Quot.sound` occurred as axioms.
All 67 intentionally incorrect source mutations were rejected.
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
