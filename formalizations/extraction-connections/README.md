# Combined extraction connections: separate Lean scope

Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
`ROOT_GROUPS.json` records every public mathematical theorem in the seven new
component packages. `ROOTS.txt` is the explicit combined root set; existing
39/91/235/444 and 83/11 scopes and evidence remain unchanged.

The principal new endpoints are an actual balanced pure-input target-uniform
minimax theorem; intrinsic rank support and exact fixed-spectrum/rank-promise
integer Bell optima; original-space finite spectral envelopes and multisector
channels; finite iid probability, variational and type/escort theorems; and one
unknown-state-independent unitary plus complete product-local postprocessing
family attaining the subcritical and Gaussian laws. The final existential
statements retain `IsProductLocal` witnesses. Gaussian limits require positive
varentropy, fixed dimensions, fixed input, and targets within both local caps.

This scope does **not** certify the entire manuscript. General-rank sharp Haar
two moments and Weyl constants, the same-family pure/mixed compatibility claim,
finite-block Berry--Esseen and growing-dimension estimates, matching operational
exponents and reliability inverses, gate synthesis/complexity, and equivalence
with abstract completely positive map presentations remain unformalized.
The mixed input uses a fixed coordinate equivalence rather than an asserted
literal copywise regrouping identity. See `REVIEW.md` for the independent
internal review and the theorem/source map in the manuscript supplement.

Run `lake exe cache get` when the pinned dependencies have no compiled cache,
then `python3 reproduce.py --check-only` and `python3 reproduce.py --fresh`.
The fresh option deletes only the eight listed new packages' owned build outputs,
rebuilds them normally, prints types and axioms, and replays every root dependency
in an empty trust-zero kernel. Same-type forged proofs must be rejected.
`verification/LATEST.json` identifies completed evidence; writing a manifest
alone is not a successful audit. Logs and summary bind exact source inputs.

Before the combined run, the four historical nonstandard `Multinomial` build
artifacts were replaced by standard setup artifacts compiled from the identical
clean pinned Mathlib source. `STANDARD_CACHE.json` checks their expected hashes.
The earlier 180-root run retains its original artifact provenance; its logs were
not relabelled as a run on the restored cache.

On this workstation, verify the D-backed research mount before building and use
D-backed `TMPDIR`, `MATHLIB_CACHE_DIR` and `XDG_CACHE_HOME`. Do not run concurrent
large empty-kernel audits, or delete the source-containing ext4 data image.
