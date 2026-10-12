# Independent rectangular APPT verification

Run **38238377463**, exact source **1a3f6275d7979121f6babd6608567fdecbe304fa**, passed all jobs and all five reproduction stages. The fresh review-package Lake build completed **2886 tasks**, retaining external dependency caches. The empty kernel at trust level zero replayed **42670 transitive declarations and 247 explicit roots**. Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The primary corrupted-proof test targets `APPTReview.appt_rectangular_maximum_formula`. All **13** exact theorem-type corruption controls passed after the positive original proof replay. Additional type-dependency closures and literal rejection diagnostics are retained. These tests preserve theorem types and universe parameters; they replace only the proofs with `True.intro`.

All **99 pinned inputs** match the exact tested commit and the current source. Every uploaded proof, audit, runner and manifest was compared byte-for-byte. Original stage logs match their recorded SHA-256 values. This checkpoint's source binding is not inferred from earlier parent builds.

Scope: Complete exact unrestricted physical APPT purity maximum for every m>=3 and n>=m^3-m-2, including the two-branch outer upper bound and actual attainment. Full maximizing-spectrum classification remains a separate obligation at this checkpoint.

This is independent CI and Lean-kernel verification of the stated endpoints, not external mathematical peer review or a priority claim. Unlisted research claims are not certified. No preprint or immutable Release is changed.
