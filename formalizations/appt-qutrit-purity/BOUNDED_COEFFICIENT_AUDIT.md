# Dense finite coefficients: bounded kernel-checked continuation

**Verified coefficient foundation, not a claim that the all-n APPT maximum has
already completed its combined build and replay.**

The largest finite dimension is D=24 (qutrit-qudit n=8). Two of its modules had
repeatedly exceeded the explicit 300-second limit: a dense signed cubic product
in the second necessary matrix determinant, and the nonnegativity of certificate
block002. Both now pass without extending that limit or weakening an equality.

## Mathematical and compilation changes

Each internal coefficient merge is given its own literal output and a kernel-
checked equality. Equality composition reconstructs the original nested operation,
with the public theorem type unchanged. Every integer array is then written with
explicit Nat literals and Int constructors, rather than overloaded numeric
notation. The resulting terms are definitionally equal to the original exact
integer coefficients, while avoiding repeated typeclass synthesis during elaboration.

`APPT.SparsePolynomialCubic.eval_decodeCubic` proves the real-evaluation law for
radix-encoded cubic monomials. `APPT.Finite24.eval_det04Term1Coeffs` proves the
corresponding actual real polynomial product, and `APPT.Finite24.block002_nonneg`
proves nonnegativity for all nonnegative gap vectors satisfying the two required
PSD hypotheses. Neither theorem is a numerical sampling assertion.

## Verified evidence

CI run `37955219720` at source `7606e9c35082641e4c8f08e11ebc4e8fa5a9af5d` passed all 16
modules. The two previously timed-out modules compiled in 22.044 seconds and 20.168 seconds.
All three root theorems and their 35,850-declaration dependency closure replayed
in an initially empty Lean kernel at trust level zero, using only the standard
axioms propext, Classical.choice, and Quot.sound.

A second fresh kernel rejects the same coefficient-product theorem after its
proof is replaced by True.intro. The check requires a declaration type mismatch;
True.intro itself is included in the closure, preventing a missing-declaration
failure from masquerading as successful detection.

Literal logs, every module's source/object/dependency hashes, the artifact
manifest, replay roots/closure/axioms, and RUN.json are retained under
`verification/bounded-coefficients-ci-20261009/`. Before publication, all 16
compiled modules and the pinned package configuration were compared byte-for-byte
with their successful CI source hashes.

## Reproduce

From this package directory, with the pinned Lean 4.34.1 and Mathlib cache:

```sh
lake env python3 scripts/build_blocks.py --case MergeBarrierProbe --engine lake --fresh --jobs 2 --timeout 300
mkdir -p .lake/build/lib/lean/Verification
lake env lean -j1 -M12288 -o .lake/build/lib/lean/Verification/ReplaySupport.olean Verification/ReplaySupport.lean
lake env lean -j1 -M12288 MergeBarrierAudit.lean
```

The transformation scripts `scripts/flatten_numeric_merges.py` and
`scripts/explicit_coefficient_literals.py` are retained for the full finite-case
continuation. Their output is always checked by Lean; neither script is a proof
oracle. The full all-n theorem and complete package audit remain separately
tracked; the immutable interim release is unchanged.
