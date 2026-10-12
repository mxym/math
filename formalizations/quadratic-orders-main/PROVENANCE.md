# Provenance and public derivative

The received round-five source ZIP is `entry002-v3-lean-round5-20261007.zip`, 16,044,443 bytes, SHA256 `c0fa4d986a4de3700f68deb4d4cead1a6a51713c144bc62d75ae5d4b90592dda`. Private delivery identifiers are omitted.

`project/` retains every one of its 1,256 Lean source files byte-for-byte, as well as original configurations, licenses, compatibility patches, mathematical maps and the written source. `provenance/ORIGINAL_SOURCE_SHA256.json` maps every included original member to its original digest. `PUBLIC_DERIVATIVE_LEDGER.json` identifies privacy/path-only transformations of nonmathematical copies. `OMITTED_AUTHOR_EVIDENCE.json` records original digests and reasons for omitted historical logs, old cache-specific executables and redundant large author inventories. No omitted file is required by the public build entry point.

The class-field source is based on ClassFieldTheory commit `2eb22d6485af45f29c5219de6c49f196a61c4f49`, with the preserved Lean-4.34.1 compatibility patch. OpenAI/math references are pinned to `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; the retained PrimeNumberTheoremAnd reference is pinned to `c39a751132c88b6e8080b74c74023fd95b3d8be0`. Their original provenance metadata, patches and licenses remain under `project/lean/references/upstream/`. Retention does not assert that every reference module occurs in the final Main closure.

Official mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`. The other eight official packages are locked by `project/lean/lake-manifest.json`. Lean is 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`. The strict release runner binds the official Linux x86-64 distribution files and source graph; it is not a claim of cross-platform binary identity.

The independent round-three CFT build is reused only after its terminal completion and exact source/compiler/output-hash reconciliation. It is an independent fresh-source build, not a reuse of author CFT objects. Five round-five bridges are newly compiled. The old offline-v3 verifier binds the author's earlier cache bytes and remains historical evidence validation only; this package neither uses it as its public fresh verifier nor re-labels its cross-environment byte-identity rejection as a mathematical failure.

Public audit records are derived from completed independent checks, with host paths/private IDs normalized. Their original and public digests are recorded separately. Existing licenses and source credits remain intact. No authorship or ownership is assigned by this packaging work.
