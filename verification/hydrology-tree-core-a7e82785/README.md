# Hydrology tree Lean checkpoint — partial formalization

Verified source commit: `a7e82785beb6a5b2442950ff78bf063d34d72f7d`.

Independent GitHub Actions run: https://github.com/mxym/math/actions/runs/38150289891
Job: 114502150467. Completed successfully on 2026-10-11.

## Exact verification scope

- Lean 4.34.1, source commit 5045d0056413266e57c625dcd7c365b10e377c52.
- Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; transitive dependencies are source-pinned and checked.
- Fresh Lake tree started with zero owned objects.
- All 16 owned modules separately compiled from source.
- 183 roots audited; 28,338 used declarations replayed into an empty trust-level-zero kernel.
- Only Classical.choice, Quot.sound, and propext occurred as axioms.
- All 10 deliberately false source mutations were rejected by Lean.
- Source hashes were checked before and after verification and remained unchanged.

Original 34-file artifact:
https://github.com/mxym/math/actions/runs/38150289891/artifacts/11706233889

Artifact ZIP SHA-256:
`16a10d3981d4ad1c6ca78c35867b27dcc16da0b0ff43d9845928f104c5255233`

Contained verified-source archive SHA-256:
`bda4d3d9b13bc22f0c5aeff9d8873151a5f1df4df576ad756127450a05502dcf`

These are the literal run's receipts, not estimates or a reuse of earlier logs.

## Mathematical progress included

The actual edge-conservative matrix, rate-coordinate Frechet Jacobian, characteristic/cofactor encoding and resolvent semantics are verified. The physical-coordinate Jacobian is the product of the rates toward the designated leak/root, including all zero-rate boundaries in the topologically numbered tree encoding.

`EdgeCharacteristic.charpoly_edgeJoin` (actual namespace: `HydrologyTree.charpoly_edgeJoin`) proves the exact single-edge characteristic identity for arbitrary real matrix blocks, with all original block diagonals retained. `HydrologyTree.diagonalCofactor_edgeJoin_left` proves its root-cofactor companion. There is no positive-rate, simple-spectrum, disjoint-spectrum or nonzero-resultant hypothesis.

`HydrologyTree.assembled_characteristic` and `HydrologyTree.assembled_cofactor` prove the characteristic and root-cofactor formulas for every finite list of actual attached matrix branches, including the empty family. The characteristic is (X+d) times the child denominator product minus the sum of the edge-product/cofactor contributions; the root cofactor is precisely the child denominator product.

The independent check also includes the existing actual polynomial-gluing, monic-scaling and root-update Frechet Jacobians. It does NOT silently promote a matrix-coordinate Jacobian to the full characteristic-coefficient Jacobian.

## Unresolved obligations

The all-tree characteristic/cofactor coefficient-map Jacobian factorization, constructive tree-to-child-block transport, arbitrary-child derivative assembly, full determinant chain-rule induction, exact edge-factor multiplicities, positive singular-locus classification and complete positive realization/fiber enumeration are not yet Lean theorems of this package.

Subsequent development drafts for direct physical leaf recursion and arbitrary-family product differentiation are outside this verified checkpoint. Compiler diagnostics for such drafts are not independent proof certificates and are not counted among the 16 modules above.

The package remains labelled PARTIAL FORMALIZATION. No completion Release, DOI, external peer-review claim, or historical-priority claim is made.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China University of Technology; mxymmxym1@gmail.com; ORCID 0009-0000-3864-3536. No external funding; AI-assisted development. Existing repository and third-party notices remain in force.
