# Exact checks accompanying the additional model review

These standard-library Python programs accompany the [2026-10-07 review](../../reviews/2026-10-07-independent-model-review.md) and the [non-simplex comparison](../../comparisons/2026-10-07-simplex-product-rate-gap.md). They use integers and rational arithmetic for all verification decisions. Their explicit checks remain enabled under `python -O`.

## Reviewed inputs

The reviewed repository snapshot is `65a1baa1307ec91bc53a96087641cc575690f285`. [source_manifest.json](source_manifest.json) records the complete identities of the inputs and the pinned upstream sources. The two differential checkers reject historical input files whose hashes do not match the audited versions. They do not modify those inputs.

## Replay

From the repository root:

```sh
python3 -O verification/2026-10-07-independent-review/check_similarity.py
python3 -O verification/2026-10-07-independent-review/check_simplex.py
python3 -O verification/2026-10-07-independent-review/check_nonsimplex_gap.py
```

The first two programs also accept `--repo-root /path/to/repository`. All three accept `--output /path/to/result.json`, allowing results to be written outside the repository. The defaults write into this directory's `results/` folder.

The original historical verifiers can be replayed without changing their saved certificates:

```sh
python3 -O preprints/004-log-density-similarity/v1.1/verification/check_cover.py --self-test
python3 -O preprints/005-simplex-product-optimum/v1.1/verification/verify_exact.py \
  --limit 300 --output /tmp/simplex-certificate-300.json
cmp /tmp/simplex-certificate-300.json \
  preprints/005-simplex-product-optimum/v1.1/verification/exact_certificate.json
python3 -O preprints/005-simplex-product-optimum/v1.1/verification/verify_exact.py \
  --limit 1000 --output /tmp/simplex-certificate-1000.json
```

## Recorded results and limits

- [similarity.json](results/similarity.json): 1,000 deterministic seeded rational instances agree with an independent boundary-intersection oracle. It finds 564 covers and 436 failures. Original failure witnesses are independently checked. This tests finite normalized certificates; it does not prove the infinite similarity theorem or certify the provenance of a supplied infinite configuration.
- [similarity_regressions.json](results/similarity_regressions.json): replay of the six historical regressions, including endpoint-only obstructions and measure-budget rejection.
- [simplex.json](results/simplex.json): an ascending-dimension dynamic program counts unordered optimal partitions in every dimension 1–300. It also validates the seven strict rational records and all 80 finite no-tie records in the historical certificate. The analytic proof is still required beyond the checked range.
- [nonsimplex_gap.json](results/nonsimplex_gap.json): self-contained rational arithmetic for ε=1/1000, the absolute moment 1487/2268, the gain 11774111/11760000, and the isolating interval for the thirteenth root of the lower bound. Its geometric prerequisites are proved and attributed in the comparison note. The root interval does not upper-bound the unknown exact value of the constructed body.

The original simplex verifier was additionally run through dimension 1000 under `python -O`. That larger finite cross-check is not a proof of an infinite assertion. No floating-point output is used as a certificate.
