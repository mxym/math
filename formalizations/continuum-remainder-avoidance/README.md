# Continuum leading power avoidance with power controlled remainders

Source package and verification guide · 7 October 2026

This package contains the Lean proof of an avoidance theorem for a prescribed nonempty countable family of positive-real configurations with bounded logarithmic gaps. A single large closed nowhere-dense periodic set is chosen for that family. It then works simultaneously for all positive real leading exponents, positive real remainder rates, nonzero signed leading coefficients, real translations, and arbitrary functions with the stated eventual power bound.

The conclusion is infinitely many **distinct output values** outside the set in **every positive input tail**. The precise statement, including genuinely tail-defined functions and the compact corollary, is in [THEOREM.md](THEOREM.md).

## What has been checked

The [recorded independent audit](audit/independent/AUDIT_REPORT.md) establishes a closed Lean theorem
`ContinuumRemainder.continuum_power_target : ContinuumPowerTarget`.
The construction premise `RobustCompactBlockerSpec` is itself proved. The compact consequence is `ContinuumRemainder.compact_power_avoidance`.

The recorded independent audit reports:

- Fresh source rebuilds of all 65 owned modules in normal Python and Python `-O`, with identical resulting Lean objects and compiler logs.
- An ownership inventory of 1,454 declarations, including 1,445 safe declarations, and axiom checks for all 568 public theorems.
- Actual replay of all 35,620 declarations in the complete safe-owned dependency closure into a fresh empty trust-level-zero kernel environment.
- A separate source-level semantic review, independently compiled partial-domain and nonvacuity probes, and positive and deliberately false boundary controls.

These are Lean verification and independent AI/model review results. They do not constitute external human peer review, novelty or priority certification. The exact historical scope and the public verifier's scope are separated in [VERIFICATION.md](VERIFICATION.md).

## Important evidence correction

The submitted [KernelReplay.lean](submitted-evidence/KernelReplay.lean) contains only an import. Its successful import under `--trust=0` does **not** establish an explicit empty-environment declaration replay. The submitted Lean file is preserved byte-for-byte. The historical evidence is retained, with any public-copy path redactions identified in the derivative ledger; its earlier description is corrected here.

The independent audit implemented the actual replay programs [ReplayClosure.lean](audit/checks/ReplayClosure.lean) and [ReplayAllSafeOwned.lean](audit/checks/ReplayAllSafeOwned.lean). The latter selected every safe owned declaration by its defining module and replayed the full stored dependency closure. This verification belongs to the independent audit. It is not a retrospective reinterpretation of the submitted import-only test. See [PROVENANCE.md](PROVENANCE.md).

## Read the proof in layers

1. Read [THEOREM.md](THEOREM.md) for the exact hypotheses, quantifier order, and limits.
2. Read [PROOF_ROADMAP.md](PROOF_ROADMAP.md) alongside [Specification.lean](project/ContinuumRemainder/Specification.lean) and [FinalProof.lean](project/ContinuumRemainder/FinalProof.lean). The roadmap identifies which modules prove each mathematical obligation and what to check at the difficult steps.
3. Read [VERIFICATION.md](VERIFICATION.md) for the pinned dependencies, evidence inventory, trust boundary, and reproduction commands.
4. Read [PROVENANCE.md](PROVENANCE.md) for preserved-source identity and the distinction between submission, audit, and release packaging.
5. Read [LICENSE_NOTICE.md](LICENSE_NOTICE.md) before redistributing or assigning license metadata.

This is the source package's reading guide, not a substitute for a traditional mathematical manuscript.

## Package layout

- `project/`: preserved Lean proof sources, aggregate modules, and pinned Lake configuration.
- `submitted-evidence/`: original submitted evidence retained with its historical provenance.
- `audit/`: independent audit programs, reports, and selected evidence.
- `scripts/`: public integrity, verification, and archive-building entry points.
- Root documentation: the current release statement and reading instructions.

Some preserved prose predates completion of the stronger theorem. In particular, the inherited [DEPENDENCIES.md](submitted-evidence/historical/DEPENDENCIES.md) describes an earlier checkpoint. Treat it as historical context; use this README and `THEOREM.md` for the current release's claims.

## Start verification

From the extracted package root:

```sh
python3 scripts/verify_integrity.py
python3 scripts/verify.py --lean-bin PATH --dependency-project PATH --output NEWDIR
```

`PATH` after `--lean-bin` is the pinned toolchain's executable directory. The dependency project must contain the exact pinned packages and usable dependency build artifacts. `NEWDIR` must be a new output directory. An optional `--extra-mathlib PATH` supplies an additional cache for the same pinned mathlib revision. Read [VERIFICATION.md](VERIFICATION.md) before running the full command.

The preserved Lake configuration defaults to the older `ContinuumGeometric` target. A bare `lake build` is therefore not the full verification described here; use the wrapper.

To make an archive of the already sealed package:

```sh
python3 scripts/make_archive.py --output FILE
```

The archive builder verifies the existing integrity record first; it must not silently replace that record to accommodate changed files. Creating an archive does not publish it anywhere.

## Scope in one sentence

This is an existence theorem for each fixed prescribed countable family, with all real leading powers and power-controlled remainders quantified after the common avoiding set; it does not claim a practical numerical construction of the set or a single set valid for every possible family.
