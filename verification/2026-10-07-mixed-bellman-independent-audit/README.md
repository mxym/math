# Independent mixed Bellman audit and replay

This directory contains the actual separately written finite/tail checker and full written adversarial audit behind the [publication summary](../../notes/mixed-bellman-product-join/PUBLIC_AUDIT.md). It is separate from the candidate-supplied `combined_audit.md`; running the submitted checker again is not represented as an independent reimplementation.

The [full report](AUDIT.md), [independent checker](independent_replay.py), and all copied evidence JSON files retain their exact original audit bytes. [PROVENANCE.json](PROVENANCE.json) identifies them by SHA-256. The report is a historical record of the original candidate audit: its `candidate_source/`, `pinned_v2/`, script names, and “present bundle” references describe that original audit archive, not this selected public layout. The original private working archive and research log are not needed for this replay. The publication's [source map](../../notes/mixed-bellman-product-join/SOURCE_MAP.json) records the continuity from the immutable candidate.

## Result and scope

For the dimension-preserving class generated from a point by products, joins and affine isomorphisms on affine hulls, the upper theorem is Gamma_C <= exp(1049/1000) < 2.855. The lower endpoint 2.8534 is inherited. The audit found no substantive gap for that intended class and requested the now-applied affine-isomorphism clarification. Arbitrary rank-dropping affine maps, all convex bodies, attainment of the optimal constant, and an improved lower construction are not covered.

## Portable fresh replay

From any working directory, invoke this directory's `replay.py` with Python 3.10 or newer. It requires only the standard library and the two certificate files already shipped in [the supplement](../../notes/mixed-bellman-product-join/README.md); it makes no network request and uses temporary output files.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 replay.py
```

The runner checks the copied evidence hashes, replays the unchanged independent arithmetic in normal and optimized Python, and compares both fresh reports byte-for-byte with the original evidence. It covers all 19,900 finite rectangles, all 15,568 tail intervals, and the independent elementary constant checks. The implementation imports none of the submitted checker code, uses its own 24-term logarithm enclosures and 2^110 outward denominator, forms factorial integers directly, enumerates every finite support corner, and uses its own endpoint-gradient maximization.

The JSON records for 24 corruption rejections, 29 symbolic checks, interval implementation controls, and the inherited lower checker are preserved historical evidence. This minimal runner does not freshly rerun those separate historical controls or claim to do so. The [publication verifier](../../notes/mixed-bellman-product-join/verify.py) independently replays the supplied upper checkers and checks its own package manifest.

This is model-assisted mathematical review and exact arithmetic replay. It is not external human peer review, proof-assistant formalization, or a priority determination. The all-dimensional theorem also uses the written induction, concavity, analytic large-dimension proof and pinned spectral reduction.
