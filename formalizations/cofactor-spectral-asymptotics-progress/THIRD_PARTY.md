# Source provenance

Six Bapat/Fischer modules are reused byte-identically from previously public `mxym/math`
formalizations. Exact source commits, paths and SHA-256 values are in
`provenance/reused-sources.json`. Every reused module is fresh compiled and audited in this
78-module final main-theorem package. Prior verification records are not used as proof of the present bytes.

The mathematical source is fixed to `mxym/math` commit
`df6d94763c852c3cf69f29c5fa95c51f88378160`,
`notes/sharp-cofactor-spectral-asymptotics`. Its recorded source hashes are supplied for traceability.
The contraction argument is mathematically related to the classical first-compound refinement
of Lieb's permanent inequality described and attributed in that source. The new Lean proofs
are given here explicitly.

Lean and mathlib are official upstream dependencies at the exact versions specified in the
README and Lake configuration. Their own license terms apply; no upstream source modifications
are part of this package. Missing official cache modules were compiled from the pinned official
source before the frozen verifier run; the verifier itself does not mutate the shared cache.
