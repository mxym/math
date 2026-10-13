# Independent rectangular APPT verification

Run **38383302058**, exact source **3bfdc77f695aa799640bdf78b891db40fc5a3f04**, passed all jobs and all five reproduction stages. The fresh review-package Lake build completed **3144 tasks**, retaining external dependency caches. The empty kernel at trust level zero replayed **50684 transitive declarations and 394 explicit roots**. Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The primary corrupted-proof test targets `APPTReview.canonical_lacunary_states_appt`. All **27** exact theorem-type corruption controls passed after the positive original proof replay. Additional type-dependency closures and literal rejection diagnostics are retained. These tests preserve theorem types and universe parameters; they replace only the proofs with `True.intro`.

All **141 pinned inputs** match the exact tested commit and the current source. Every uploaded proof, audit, runner and manifest was compared byte-for-byte. Original stage logs match their recorded SHA-256 values. This checkpoint's source binding is not inferred from earlier parent builds.

Scope: Complete eventual all-global-unitary APPT sufficiency for canonical finite lacunary integer-projection families with a single spike. The purity lower limit and coefficient eight are NOT yet proved by this checkpoint.

This is independent CI and Lean-kernel verification of the stated endpoints, not external mathematical peer review or a priority claim. Unlisted research claims are not certified. No preprint or immutable Release is changed.
