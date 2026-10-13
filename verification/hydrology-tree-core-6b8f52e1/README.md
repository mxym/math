# Independently verified tree-formalization checkpoint

**Scope: unconditional partial Lean formalization. The full all-tree Jacobian,
its exact multiplicity/conjecture corollaries, positive singular-locus theorem,
and complete positive realization/fiber classification remain unproved in Lean.**

Verified source: `6b8f52e1d5c35dd828d75c42da87c7fbaad0d738`.

Independent GitHub Actions: https://github.com/mxym/math/actions/runs/38153305826

## Checked results and exact evidence

- All 28 owned modules compiled in a fresh Lake tree and a separate fresh object tree.
- 284 roots; 36,481 used declarations replayed into an empty kernel at trust level zero.
- Axioms: Classical.choice, Quot.sound, propext only.
- All 14 deliberately false source mutations were rejected.
- Before/after proof-input source hashes matched; fixed Lean 4.34.1 and Mathlib
  d13f23b723b8a846827a245b89c10fc7d3f11612 and transitive dependency sources were checked.
- All 24 previously verified non-aggregate module objects match the preceding
  independent 25-module run byte for byte. This comparison does not replace the new replay.

`original-actions-artifact.zip` is the unmodified downloaded CI artifact.
`verification.json` and the source archive are extracted from it, not reconstructed
from development diagnostics. `PROVENANCE.json` records the retrieval identifiers
and cross-run comparison. `SHA256SUMS` binds all retained bytes.

## Principal new theorem entry points

`HydrologyTree.familyGlueJacobian_eq_pairwise` proves the all-arity coefficient
gluing Jacobian as the squared pairwise resultant product. Actual numerator
polynomials, Frechet derivatives and second-order regularity are proved; zero
degrees, repeated roots and zero resultants are not excluded.

`HydrologyTree.physical_root_block_decomposition` constructs and proves the exact
root/branch decomposition of the original physical matrix. Root branches,
absence of cross-transfers, and retention of original boundary-exit diagonals
are proved rather than assumed. `physicalCharacteristic_terminal_recursion`
provides the additional all-size physical leaf recurrence.

The package also includes the proved actual edge-attachment and arbitrary-branch
characteristic/cofactor recursions and the physical rate-coordinate Jacobian.
The latter is NOT the full characteristic/cofactor coefficient Jacobian.

## Remaining central task

Renumber the actual child blocks as smaller physical trees, prove the exact
rate-coordinate extraction/permutations and complete the global derivative and
determinant induction. Exact multiplicities, cancellation/spectral equivalences,
and the global Stieltjes inverse/fiber count remain separate obligations. The
complete gap report is `formalizations/hydrology-tree-core/GAPS.md` at the source commit.

No full-formalization Release or DOI is created. This is not external human peer
review. Development compiler sessions are not counted as kernel certificates;
the session used this round was explicitly stopped and completed successfully.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com; ORCID 0009-0000-3864-3536.
No external funding; AI-assisted development. Existing notices remain in force.
