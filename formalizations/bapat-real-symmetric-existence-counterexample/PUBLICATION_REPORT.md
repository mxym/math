# Publication review and formalization coverage

## Exact result

The unconditional root is `BapatRealExistence.exists_integer_real_symmetric_counterexample`. Its complete elaborated type is archived in `publisher-review/ROOT_TYPE.txt`. It asserts existence of N > 4 and a matrix B with entries in the integers, integer symmetry, positive definiteness after entrywise casting to the reals, non-diagonality, a strictly negative derivative at q = 1 of the q-permanent polynomial, and rational points 0 < q0 < q1 < 1 with a strict decrease of the actual q-permanent.

There is no outer hypothesis or substituted custom positive-definiteness predicate. `BapatDefs.lean` sums over all permutations with the ordinary ordered inversion count. `BapatRealPolynomial.lean` proves equality between evaluation of its polynomial and this sum. The ordering dependence is retained; no invariance of inversion count under arbitrary row reordering is asserted.

## Mathematical chain reviewed

The finite-rank Fischer identity in `BapatFiniteRankEndpoint.lean` uses actual real Gram entries, wedge determinants and two-row cofactors. The analytic construction supplies a finite cloud with a strict energy gap, inserts four selector rows, orders the rows and repeats contiguous blocks to obtain a finite real Gram matrix with a negative endpoint derivative.

The analytic lemmas discharge the equidistribution, logarithmic integrability, balancing, moving-maximizer and strict Gini-gap steps. The archived source review identifies these modules and the exact finite choice order. The publication review read that explanation and the key defining, finite-endpoint, finite-base and final rational/integer source chain. All 67 source files were also independently hash-checked and scanned after removing nested comments and strings. This source reading is not presented as an independent second full Lean execution.

Rational approximation preserves the strict negative derivative. A positive rational diagonal makes the rational Gram matrix positive definite while preserving negativity. Multiplication by a positive common denominator produces the integer matrix and preserves positive definiteness and derivative sign. The final proof derives integer symmetry from real positive definiteness, excludes a diagonal matrix using the negative endpoint derivative, and obtains rational interior decrease points for this same integer matrix.

Two implementation routes differ from the exposition of the written proof: the formalization evaluates the needed Gaussian Gini integral directly, rather than separately proving the full Cauchy density and CDF; non-diagonality follows from the negative derivative, rather than from an intermediate rank argument. Neither changes the final theorem. No explicit dimension bound, numerical real witness, or extractable computational witness is claimed.

## Original execution evidence and independent publication checks

The original run `20261008T173353Z-6a75cf6e` records 67 fresh Lean compilations, 67 dependency commands, the owned-declaration audit and the invalid-proof control, with all 136 command exit codes zero. It records all 776 owned declarations and all 54,739 dependency-closure declarations replayed into a fresh empty kernel at trust level 0. The requested root union contains 54,476 declarations. No owned declaration is excluded. The shared-cache before/after hashes match.

The original verifier checks that the only axioms are `propext`, `Classical.choice` and `Quot.sound`, using full expected signatures with only binder and universe-parameter names normalized. It also checks declaration kind, safety, universe parameters and kernel type equality. The negative control attempts to install a proof of False with value True and records the kernel's rejection.

`publisher-review/INDEPENDENT_RECORD_AUDIT.json` records the separate publication checks: all 234 archive members match actual extracted bytes, all 232 original manifest entries and all 67 source hashes match, the closure graph is dependency-closed, owned declaration records agree with closure entries, no unsafe/partial declarations or extra axioms occur, and all three complete normalized signature records match the expected records. It also records the source files read for the semantic chain and the limitations of that review. The publication owner did not install or rerun Lean.

Pinned dependencies: official Lean 4.34.1 commit `5045d0056413266e57c625dcd7c365b10e377c52`; mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. Further pinned dependencies and reproduction controls are included in the unchanged package.

## Provenance and manifests

The mathematical reference is frozen at public commit `2509263c1028d6814658174b2830a3d658e76c1c`; its paper.tex SHA256 is `ac6983f69f78175ce119b253f22ae11336ba1e23af9e4c8b13b51d9b30e86411`. The private delivery archive was retrieved at exact commit `b1d7d379a42f8be208b1f3ff9d2ccbecc57c3048`, with 5,176,502 bytes and SHA256 `95cc1d7c0b24a07b4a12b61ea20ce14b0dd3f614fa8895d1e4b3b868f8db9cd2`. All 234 original files are represented in the public package. Every Lean source and all declaration, closure, full axiom-signature and replay-result data retain their original bytes. Private machine paths in execution logs/configurations and thread identifiers are replaced with role placeholders; the reading description and affected hash manifests are updated. PUBLICATION_PROJECTION.json records all 115 affected files and their original/projected hashes. The raw private delivery archive is not a public attachment. The publication also adds this report, a reading guide, the independent record audit and the elaborated root type.

The original manifests are preserved unchanged as `ORIGINAL_FILES.json` and `ORIGINAL_SHA256SUMS`; their hashes refer to the raw private delivery. The projected `FILES.json` and `SHA256SUMS` each cover the 232 projected core payload files and exclude both themselves. `PUBLICATION_MANIFEST.json` covers all publication payload files except itself and `PUBLICATION_SHA256SUMS`. `PUBLICATION_SHA256SUMS` covers those files and the publication manifest, excluding itself. Release manifests subsequently bind the public commit and attachment hashes without changing any older immutable Release. The complete public-source archive and projected Lean archive omit private paths and thread identifiers.

This work claims complete formalization of the stated finite existence theorem, with the scope and evidence above. It makes no external human peer-review or exhaustive historical-priority claim.
