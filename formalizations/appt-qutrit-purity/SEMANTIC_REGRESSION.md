# Physical PPT is not absolute PPT: an all-dimension regression

**Verified in Lean 4.34.1. This result is a semantic regression, not a claim that
the entire maximal-purity formalization is already complete.**

For every integer `n >= 3`, `APPT.Quantum.exists_PPT_density_exceeding_target`
constructs an actual complex matrix on `Fin 3 × Fin n` satisfying all of:

- positive semidefiniteness and trace one;
- a positive semidefinite (indeed unchanged) partial transpose;
- trace-square purity equal to one, strictly above the proposed APPT maximum;
- failure of `AbsolutelyPPT`, with its actual quantification over global unitaries.

The witness is the diagonal projection onto the product-basis coordinate
`(0,0)`. Its idempotence proves purity one; its diagonal form proves that partial
transpose fixes it. Non-APPT is proved independently of the final purity maximum:
the existing physical corner-unitary necessity theorem would make `matA` positive
semidefinite for the selected diagonal entries `[1,0,0,0,0,0,0,0,0]`, but its
principal minor on indices 0 and 1 is exactly `-1`.

Thus neither ordinary density-matrix positivity nor PPT in the original basis
can silently replace the physical APPT hypothesis. The strict purity comparison
is proved for both branches of `targetPurity`, for every `n >= 3`.

## Verification

CI run `37950142930`, source commit
`bdae89b3cf65dd4cf2dac28972879b6d3b7dc3fb`, passed the source build and the
independent replay of **35,589 declarations / six theorem roots**, starting from
an empty kernel at **trust level zero**. Only `Classical.choice`, `Quot.sound`,
and `propext` occur as axioms. Replacing the proof of the same existential theorem
by `True.intro` is rejected by a second fresh kernel for a declaration type mismatch.

Literal build/replay logs, the workflow response, complete source hashes, and
root/closure/axiom inventories are under
`verification/semantic-regression-ci-20261009/`. Every retained source hash was
compared with the publication worktree before commit.

```sh
lake build +APPT.Quantum.SemanticRegression
mkdir -p .lake/build/lib/lean/Verification
lake env lean -j1 -M12288 -o .lake/build/lib/lean/Verification/ReplaySupport.olean Verification/ReplaySupport.lean
lake env lean -j1 -M12288 SemanticRegressionAudit.lean
```

The independent generic sparse-arithmetic coefficient controls are documented in
`SPARSE_ARITHMETIC_AUDIT.md`. Bounded finite certificates and the final all-n
maximum must still complete their combined build and replay before a new full
formalization release is warranted. No immutable interim release is modified.
