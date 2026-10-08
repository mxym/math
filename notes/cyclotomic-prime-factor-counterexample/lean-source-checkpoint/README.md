# CGF counterexample: Lean source checkpoint

**PENDING INDEPENDENT VERIFICATION. This is a source checkpoint, not a completed independent Lean certification.**

The eight proof modules and three audit modules are published here for reproduction and review. Their bytes match all eleven recorded source hashes. No new Lean compilation or independent empty-kernel replay was performed for this publication.

## Mathematical target

The target is the already published counterexample

F = (Φ₄ Φ₉ Φ₂₅ Φ₃₀)⁶

to the basic, unimodal form of Billey–Swanson Conjecture 48. The separate [written proof and exact certificates](https://github.com/mxym/math/tree/0b9aa237472dfc7cfc252d8708aadd3fd5e897df/notes/cyclotomic-prime-factor-counterexample) passed the mathematical/computational review described there. That result does not depend on completion of this Lean review. This checkpoint does not modify the frozen proof or its Release.

The formalization uses Mathlib's actual integer cyclotomic polynomials. Its principal statement includes degree 216, monicity, constant coefficient 1, nonnegativity at every natural index, positivity on indices 0–216, strict increase/decrease about the unique peak at 108, all-index unimodality, basic-CGF membership, and exclusion of every prime-order cyclotomic factor. It also supplies a centered q-integer expansion and a denominator-cleared quotient identity with nonzero denominator. The coefficient list is connected to the product by a polynomial identity, rather than assumed correct.

Primary audit roots in namespace `CyclotomicCounterexample`:

- `explicit_counterexample`
- `conjecture48_false`
- `F_centered_certificate`
- `F_qInteger_quotient_certificate`

`IsBasicCGF` requires nonnegative integer coefficients and a finite product of cyclotomic polynomials with indices at least 2, without an extra scalar or monomial. `UnimodalCoeffs` quantifies over all natural indices, including the zero tail. Reviewers should compare these definitions and the actual stored theorem types with the published conjecture, not infer semantic fidelity from theorem names.

## Verification status

1. **Historical authoring observation:** the eight core modules compiled into a fresh output directory under Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The corrected 73-declaration signature/axiom audit reported success. Four declarations reported no axioms; the others used only subsets of `propext`, `Classical.choice`, and `Quot.sound`. This is a historical observation, not an attached original compiler log. A subsequent rerun has no observed terminal status and is not counted as successful.
2. **Current source integrity:** all eleven Lean sources match their recorded SHA-256 values and sizes in [RECOVERY_MANIFEST.json](RECOVERY_MANIFEST.json). No original `.olean` files or full historical compiler logs are included. The support scripts and documentation are new publication support, not original proof logs.
3. **Still pending:** a fresh compilation of this public checkpoint, a new axiom/signature audit, and independent trust-level-zero empty-kernel replay with a semantic review and negative controls. Source hash agreement alone establishes none of these.

No `sorry`, `admit`, custom `axiom`, `native_decide`, or `unsafe` declaration occurs in the published proof sources. The supplied source scan is only a guardrail; the independent kernel/semantic review remains required. No claim of minimum degree, historical priority, external human peer review, or complete Lean certification is made.

## Files

The compilation order is `CoefficientList`, `CyclotomicFormulas`, `PrimeExclusion`, `BasicProperties`, `Expansion`, `DataProperties`, `Counterexample`, `CenteredCertificate`. `Audit.lean` prints all 73 declaration signatures and axiom reports, plus central definitions. `BasicPropertiesAudit.lean` and `PrimeExclusionAudit.lean` are smaller additional audits. All eleven files retain their original bytes.

[PACKAGE_MANIFEST.json](PACKAGE_MANIFEST.json) hashes every distributed file except itself. The Git commit binds that manifest. The recovery archive identity is recorded for provenance; the archive is not required to use this directory.

## Reproduce on Linux or macOS

Requirements: Bash, Python 3.8 or later (standard library only), Git, an independently provisioned official Lean **4.34.1** executable, and a prepared Mathlib checkout/cache at **d13f23b723b8a846827a245b89c10fc7d3f11612**. The scripts do not download, install, publish, modify dependencies, or remove files. The Mathlib checkout must have no tracked modifications. Its transitive dependencies and cached artifacts must be provisioned and trusted separately; this compilation workflow does not authenticate dependency binaries or replace empty-kernel replay.

From a writable copy of this directory:

```sh
python3 check_sources.py
export LEAN_BIN=/absolute/path/to/lean
export MATHLIB_ROOT=/absolute/path/to/mathlib4
export MATHLIB_LEAN_PATH="$(cd "$MATHLIB_ROOT" && lake env printenv LEAN_PATH)"
bash verify.sh
```

The `lake` command in the example must belong to the same pinned Lean toolchain. Absolute paths are supplied by the reviewer; no machine-specific path is embedded in the scripts. Relative entries in the Lake-produced dependency path are resolved against `MATHLIB_ROOT`; empty or missing path entries are rejected. The inherited `LEAN_PATH` is replaced. Newly built project modules are loaded from a unique, initially empty output directory, ahead of the supplied dependency paths.

Each invocation writes fresh logs and `.olean` files under `.verification-runs/run.*`. The final `VERIFICATION_REPLAY.json` reports compilation and the 73-declaration axiom audit only. It always labels independent empty-kernel verification as pending. Retain the run directory and exact source commit when reporting results. These support scripts were syntax-checked and exercised with synthetic negative controls at publication; they have not yet completed an end-to-end Lean run on this checkpoint.

For independent replay, rebuild from the exact public source bytes and check the dependency closures of the four audit roots in a newly empty environment at trust level zero. Inspect the stored theorem types and central definitions, verify the axiom whitelist, and include negative controls. Do not describe compilation alone as empty-kernel replay.

Mathematical source: Sara C. Billey and Joshua P. Swanson, *Cyclotomic Generating Functions*, Electronic Journal of Combinatorics 31(4) (2024), P4.4, [DOI](https://doi.org/10.37236/12687), Definitions 3/45 and Conjecture 48. The frozen mathematical certificate SHA-256 is `64b10e5427ecaaaf9076e5d8b592831393db9fcb2b412c5894fd928d5fd4dfad`.
