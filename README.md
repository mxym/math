# math

Mathematical research manuscripts and supporting verification material maintained at **mxym/math**.

中文：本仓库收录数学研究稿、完整证明和可编辑源码。当前五份稿件涉及最优传输、二次整数阶中的有限步长图、精确维数的不可嵌入紧集、Erdős 相似性问题的对数密度判据，以及单纯形直积的精确投影体体积极值。请从 [CONTENTS.md](CONTENTS.md) 进入各稿件。

## Collection

| ID | Manuscript | Latest | Status |
| --- | --- | --- | --- |
| 001 | [Sharp one-third stability of Brenier maps for strongly log-concave sources](preprints/001-strongly-log-concave-brenier/README.md) | v2 | Research draft |
| 002 | [Bounded step walks on irreducibles in quadratic orders](preprints/002-quadratic-order-moats/README.md) | v2 | Research draft |
| 003 | [Compact Banach space obstructions with Assouad dimension two](preprints/003-assouad-two-zero-box/README.md) | v1 | Research draft |
| 004 | [A logarithmic upper Banach density criterion for the Erdos similarity problem](preprints/004-log-density-similarity/README.md) | v1.1 | Complete written proof draft; finite-cover verifier |
| 005 | [Exact projection-volume optimization over Cartesian products of simplices](preprints/005-simplex-product-optimum/README.md) | v1.1 | Complete written proof draft; exact finite certificates |

A separate [nine-piece balanced-projector cover](notes/balanced_borsuk_slice.md) excludes one proposed Borsuk construction; it is not a solution of the eight-dimensional problem.

## Reading and verification

Each manuscript directory contains LaTeX source, build instructions and upstream attribution. The arguments were developed with AI assistance and checked against explicit hypotheses and proof dependencies. **These are research manuscripts, not externally peer-reviewed or fully machine-formalized results.** See [verification/STATUS.md](verification/STATUS.md) for entries 001--003 and the [additional audit record](verification/density-simplex-2026-10-07.md) for 004--005. The exact finite checks do not replace the infinite analytic arguments. The similarity toy certificate is not a computed small-measure witness for the full theorem.

Several methods build on the public [OpenAI/math collection](https://github.com/openai/math), pinned at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The manuscripts distinguish inherited arguments from the extensions developed here. No affiliation with or endorsement by OpenAI is implied.

## Versions and disclosure

Versions are kept in separate `v1`, `v2`, ... directories. Corrections and extensions are recorded in [CHANGELOG.md](CHANGELOG.md); earlier versions remain accessible. The [v1 manifest](releases/2026-10-07-v1.json) and [v2 manifest](releases/2026-10-07-v2.json) record exact file hashes. Historical manifests must be checked at their corresponding publication commit, because the root catalogue evolves. The first research publication commit is [`4d718fe55d8b53eb8dd8634508c3297f0a978149`](https://github.com/mxym/math/commit/4d718fe55d8b53eb8dd8634508c3297f0a978149). The first complete source publication of entries 004 and 005 is [`e6c776cae39477baa4e1a03d59a1547417f1a68e`](https://github.com/mxym/math/commit/e6c776cae39477baa4e1a03d59a1547417f1a68e); their v1.1 number refers to private-draft revisions, not an earlier public version. Their [build workflow](.github/workflows/density-simplex-publication.yml) replays finite checks, compiles PDFs, records hashes, and preserves a versioned research release.

GitHub commit timestamps document this repository's disclosure history; they do **not** certify mathematical correctness or first discovery. Literature comparison continues separately, and no priority assertion is made.

## Rights and provenance

The upstream OpenAI material retains its Apache-2.0 license, reproduced in [third_party_licenses/openai_math_LICENSE.txt](third_party_licenses/openai_math_LICENSE.txt). See [NOTICE.md](NOTICE.md) and the [additional provenance notice for 004--005](verification/density-simplex-2026-10-07.md). No additional license for newly authored material has been selected; do not infer one merely from the repository being public.

## Post-publication comparison

A [primary-literature comparison](comparisons/2026-10-07-primary-literature.md) records exact and partial overlaps found after the initial release. In particular, a nondegenerate semi-discrete W2 one-third estimate predates this collection, and W1 quarter-power estimates are not interchangeable with W2 one-third estimates. The note distinguishes these results from the current source and target scope; it does not certify priority.
