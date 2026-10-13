# Independent APPT sparse-matrix verification

Run **38349046520**, exact source **3ae4c51210c7bf9fecfd726502954cd534929585**, passed all jobs and all five reproduction stages. The fresh review-package Lake build completed **3134 tasks**, retaining external dependency caches. The empty kernel at trust level zero replayed **50610 transitive declarations and 365 explicit roots**. Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The primary corrupted-proof test targets `APPTReview.lacunary_sparse_matrix_bound`. All **24** exact theorem-type corruption controls passed after the positive original proof replay. Additional type-dependency closures and literal rejection diagnostics are retained. These tests preserve theorem types and universe parameters; they replace only the proofs with `True.intro`.

All **131 pinned inputs** match the exact tested commit and the current source. Every uploaded proof, audit, runner and manifest was compared byte-for-byte. Original stage logs match their recorded SHA-256 values. This checkpoint's source binding is not inferred from earlier parent builds.

Scope: Complete uniform canonical-power lacunary fractional sparse-matrix PSD and operator-square bound, including actual finite amplitude measures, clipping, small-coordinate loss, common-probability compactness and homogeneous tests. This checkpoint does not yet verify graph-plus-spike decoupling or the multiscale quantum lower construction.

This is independent CI and Lean-kernel verification of the stated endpoints, not external mathematical peer review or a priority claim. Unlisted research claims are not certified. No preprint or immutable Release is changed.
