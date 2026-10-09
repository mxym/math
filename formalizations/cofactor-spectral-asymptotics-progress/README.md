# Complete Lean proof of sharp cofactor spectral asymptotics

This package proves **Theorem 1**, including the positive-definite correlation extension,
at fixed mathematical source `mxym/math` commit
`df6d94763c852c3cf69f29c5fa95c51f88378160`,
`notes/sharp-cofactor-spectral-asymptotics`.

## Main theorem

`CofactorSpectral.sharp_cofactor_spectral_asymptotics` in
[`src/CofactorFullMain.lean`](src/CofactorFullMain.lean) proves all six limits below.
Each extremum is a supremum of the **actual largest Hermitian eigenvalue divided by the
actual permanent**. Real directions use the entrywise real part of the actual compound;
they continue to permit complex Hermitian input matrices.

| Input matrix class | Complex-direction extremum / log N | Real-direction extremum / log N |
| --- | --- | --- |
| Arbitrary PSD, positive permanent | tends to 1 | tends to 1/2 |
| Correlation, exact rank two | tends to 1 | tends to 1/2 |
| Positive-definite correlation, positive permanent | tends to 1 | tends to 1/2 |

The six spectral/variational equivalences are proved in
[`src/CofactorSpectralExtrema.lean`](src/CofactorSpectralExtrema.lean).
The minor in `compound A i j = A i j * permanent(A(i|j))` is not transposed.
No desired asymptotic bound, construction oracle, or external mathematical theorem is a
hypothesis of the final endpoint. The positive-definite perturbation may increase rank;
there is no exact-rank-two positive-definite assertion in dimensions greater than two.

## Complete proof route

The proof includes the all-rank indicator inequality via actual coordinate contractions,
the sorted-vector and harmonic upper bounds, finite entropy estimates, actual signed root
rings and all their moments, exact rank-two correlation normalization, permanent coefficient
identities, sign orthogonality with degree collisions, factorial/binomial and weighted subset
tail estimates, actual ceiling degree recurrence and floor budget in every sufficiently large
dimension, the sharp parameter limit from the derivative of log, and the actual continuous
positive-definite perturbation. All parameters are fixed before dimension tends to infinity.

See [`SEMANTIC_REVIEW.md`](SEMANTIC_REVIEW.md) for definition correspondence, proof choices
and scope. The later sharp ramp constant and rank-two endpoint statements in the manuscript
are separate results and are not claimed by this package.

## Fresh independent mechanical verification

All **78** frozen owned modules were compiled into a new output directory. The checker audited
all **745** owned declarations, without exclusions, and replayed their full
**55731**-declaration transitive closure into an **empty kernel at trust level 0**.
The requested-root union contains **55515** declarations.
The invalid-proof negative control was rejected. Source hashes remained stable and the shared
official dependency cache was unchanged. No custom axiom, `sorryAx`, unsafe or partial owned
declaration was found. Only Lean's three standard axioms `propext`, `Classical.choice`, and
`Quot.sound` occur; their declarations were separately validated by the checker.

The published verification evidence covers these exact frozen bytes, rather than extending
the earlier 54-module checkpoint certificate. Full inventories and dependency closures are
compressed under `verification`; fresh compiler logs, root types and the checker are included.
Source-to-statement review is by the implementing agent, with no independent human review claim.

## Pinned official environment and reproduction

- Lean **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Sources and provenance hashes: `SHA256SUMS`, `case.json`, and `provenance/`.
- Byte-identical reuse and attribution: [`THIRD_PARTY.md`](THIRD_PARTY.md).

With those official dependencies and their caches already installed, run:

```sh
python3 reproduce.py --output /fresh/output \
  --toolchain /official/lean-4.34.1 \
  --packages-root /official/dependencies \
  --cache-root /official/cache
```

The reproducer creates new owned outputs, verifies dependency pins, compiles all frozen source
modules, audits every owned declaration and performs empty-kernel replay. It does not use old
owned `.olean` files, download packages, install tools or mutate dependency sources.
Ordinary pinned Lake configuration is also included; a Lake build alone is not the replay certificate.
