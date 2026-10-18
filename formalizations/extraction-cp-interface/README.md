# Abstract CP/TP/PPT to actual finite extraction protocols

This independent continuation package proves the finite-dimensional channel model bridge. It uses Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, with shared dependencies on D storage.

`ExtractionCP.CompletelyPositive` is defined by positivity on **every actual finite auxiliary matrix system**. It is not base positivity, Choi positivity by definition, or the existence of a supplied Kraus certificate. `TracePreserving` quantifies over every complex input matrix.

`CPInterface.Choi` proves:

- `choi_eq_amplification` and `CompletelyPositive.choi_posSemidef`: the actual maximally entangled positive projector's amplification is the Choi matrix.
- `choiKraus`: columns of the positive Choi matrix's functional-calculus square root, reshaped into input/output operators.
- `choiKraus_gram`, `map_eq_choi_sum`, and `choiKraus_apply`: exact Gram and action reconstruction, internally derived from the positive matrix square-root theorem (itself proved in Mathlib through the finite Hermitian spectral calculus).
- `completelyPositive_iff_choi_posSemidef`: both directions of the finite Choi theorem.
- `kraus_complete_of_tracePreserving` and `choiKraus_complete`: the completeness matrix identity follows from trace preservation using nondegeneracy of the matrix trace pairing.
- `CompletelyPositive.exists_kraus` and `.exists_complete_kraus`: actual Kraus representation from abstract CP, and completeness from TP.

`CPInterface.PPT` proves:

- Complex-linearity and exact action of the partial-transpose conjugate, plus its trace preservation derived from the original TP property.
- `completelyPositive_iff_exists_finiteKraus` and `completelyPositive_tracePreserving_iff_exists_complete_finiteKraus`, using natural-index actual Kraus families.
- `PPTChannel.toKrausPPTProtocol`: from abstract CP/TP of the channel and CP of its actual partial-transpose conjugate, construct both complete finite Kraus families of the existing `MinimaxProfile.KrausPPTProtocol`, with any requested preprocessing unitary. Each family has input-dimension times output-dimension branches; no rank or nondegeneracy premise is needed.
- `.toKrausPPTProtocol_apply` and `.toKrausPPTProtocol_fidelity`: exact action and physical Bell overlap equalities on every matrix.
- `ofKrausPPTProtocol`: converse construction, proving the two abstract CP conditions from the existing actual families.
- `abstract_ppt_iff_actual_protocol`: exact equivalence of the abstract channel class and actual extraction protocol model, preserving the unitary and channel action.
- `actual_abstract_actual_fidelity`: the reconstruction roundtrip preserves fidelity on every complex matrix, hence also on every density matrix.

The bridge covers all finite natural input and output dimensions, including zero dimensions. It does not assert that every cPPT map is product local; locality remains a distinct property of particular constructed protocols.

Verification: BUILD_ONLY, not an independent audit. No custom axioms, sorry or admit are used. See `BUILD_ONLY_20261018.txt` for the final aggregate build record. Existing frozen audit scopes are unchanged.
