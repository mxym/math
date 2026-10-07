# math

Mathematical research manuscripts and supporting verification material maintained at **mxym/math**.

中文：本仓库收录数学研究稿、完整证明和可编辑源码。当前七份稿件涉及最优传输、二次整数阶中的有限步长图、精确维数的不可嵌入紧集、Erdős 相似性问题、单纯形直积的精确极值，以及非线性避让与光滑源的稳定性反例。请从 [CONTENTS.md](CONTENTS.md) 进入各稿件。

## Collection

| ID | Manuscript | Latest | Status |
| --- | --- | --- | --- |
| 001 | [Sharp Gaussian Brenier stability under logarithmic second moments](preprints/001-strongly-log-concave-brenier/README.md) | v4 | Research draft |
| 002 | [Bounded step walks on irreducibles in quadratic orders](preprints/002-quadratic-order-moats/README.md) | v3 | Research draft |
| 003 | [Compact Banach space obstructions with Assouad dimension two](preprints/003-assouad-two-zero-box/README.md) | v1 | Research draft |
| 004 | [A logarithmic upper Banach density criterion for the Erdos similarity problem](preprints/004-log-density-similarity/README.md) | v1.1 | Complete written proof draft; finite-cover verifier |
| 005 | [Exact projection-volume optimization over Cartesian products of simplices](preprints/005-simplex-product-optimum/README.md) | v1.1 | Complete written proof draft; exact finite certificates |
| 006 | [Modulus-controlled nonlinear avoidance and a differentiability boundary for null patterns](preprints/006-modulus-nonlinear-similarity/README.md) | v1 | Complete written proof draft; robust finite-cover checker |
| 007 | [Tail-sensitive convex-gradient interpolation and Brenier stability beyond bounded targets](preprints/007-tail-brenier-stability/README.md) | v2 | Complete written proof draft; smooth full-support counterexample |

A separate [nine-piece balanced-projector cover](notes/balanced_borsuk_slice.md) excludes one proposed Borsuk construction; it is not a solution of the eight-dimensional problem.

## Reading and verification

Each manuscript directory contains LaTeX source, build instructions and upstream attribution. The arguments were developed with AI assistance and checked against explicit hypotheses and proof dependencies. **These are research manuscripts, not externally peer-reviewed or fully machine-formalized results.** See [verification/STATUS.md](verification/STATUS.md) for entries 001--003, the [additional audit record](verification/density-simplex-2026-10-07.md) for 004--005, and the [cross-audit and extensions record](verification/2026-10-07-cross-audit-and-extensions.md) with the [007 v2 audit](preprints/007-tail-brenier-stability/v2/PROOF_AUDIT.md) for the new additions. The exact finite checks do not replace the infinite analytic arguments. The similarity toy certificate is not a computed small-measure witness for the full theorem.

Several methods build on the public [OpenAI/math collection](https://github.com/openai/math), pinned at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The manuscripts distinguish inherited arguments from the extensions developed here. No affiliation with or endorsement by OpenAI is implied.

## Versions and disclosure

Versions are kept in separate `v1`, `v2`, ... directories. Corrections and extensions are recorded in [CHANGELOG.md](CHANGELOG.md); earlier versions remain accessible. The [v1 manifest](releases/2026-10-07-v1.json) and [v2 manifest](releases/2026-10-07-v2.json) record exact file hashes. Historical manifests must be checked at their corresponding publication commit, because the root catalogue evolves. The first research publication commit is [`4d718fe55d8b53eb8dd8634508c3297f0a978149`](https://github.com/mxym/math/commit/4d718fe55d8b53eb8dd8634508c3297f0a978149). The first complete source publication of entries 004 and 005 is [`e6c776cae39477baa4e1a03d59a1547417f1a68e`](https://github.com/mxym/math/commit/e6c776cae39477baa4e1a03d59a1547417f1a68e); their v1.1 number refers to private-draft revisions, not an earlier public version. Their [build workflow](.github/workflows/density-simplex-publication.yml) replays finite checks, compiles PDFs, records hashes, and preserves a versioned research release.

Entries 006 and 007 v1 are preserved in [modulus-tail-20261007-v1](https://github.com/mxym/math/releases/tag/modulus-tail-20261007-v1). The stronger 007 v2 is published separately as [tail-stability-20261007-v2](https://github.com/mxym/math/releases/tag/tail-stability-20261007-v2), with the first new extension source in `c8d4fa9d7afc28d10123e666af0dfcdfc3f2681d`. The older sources are not overwritten.

GitHub commit timestamps document this repository's disclosure history; they do **not** certify mathematical correctness or first discovery. Literature comparison continues separately, and no priority assertion is made.

## Rights and provenance

The upstream OpenAI material retains its Apache-2.0 license, reproduced in [third_party_licenses/openai_math_LICENSE.txt](third_party_licenses/openai_math_LICENSE.txt). See [NOTICE.md](NOTICE.md), the [additional provenance notice for 004--005](verification/density-simplex-2026-10-07.md), and the new manuscripts' explicit dependency notes. No additional license for newly authored material has been selected; do not infer one merely from the repository being public.

## Post-publication comparison

A [primary-literature comparison](comparisons/2026-10-07-primary-literature.md) records exact and partial overlaps found after the initial release. In particular, a nondegenerate semi-discrete W2 one-third estimate predates this collection, and W1 quarter-power estimates are not interchangeable with W2 one-third estimates. The note distinguishes these results from the current source and target scope; it does not certify priority.

The [parallel-work reconciliation](comparisons/2026-10-07-modulus-tail-reconciliation.md) identifies the overlap between 001 v3 and 007 v1 and the actual additional v2 results. An [additional model review of 004--005](reviews/2026-10-07-independent-model-review.md) reports exact replays and the known non-simplex rate comparison. It is not human peer review.

## Quadratic version 3

The [quadratic v3 manuscript and complete certificate data](preprints/002-quadratic-order-moats/v3/README.md) extend the finite certificate interface to individual nonzero nonunit principal generators, including ramified norm-prime and composite-norm cases. Exact quotient-component sizes and selected norm values sharpen the integer restoration bounds. Complete two-dimensional four-step and eight-step examples are supplied, together with an explicitly rejected candidate sieve.

The main all-quadratic-order existence theorem and its inherited analytic proof interface are unchanged. The 41 norm-prime tests, 24 general-principal tests, independent finite-lift/direct-multiplication checks, and 184-generator arithmetic checks are finite computational verification only. No unrestricted search implementation, practical-runtime guarantee, formal verification, or optimality claim is made. Exact changed-file hashes are recorded in the [v3 manifest](releases/2026-10-07-v3.json); cite the Git commit actually used.

## Transport version 3 and the smooth-source distinction

The [30-page transport manuscript](preprints/001-strongly-log-concave-brenier/v3/manuscript.pdf) proves sharp one-third map stability on every fixed q>2 moment class for a full Gaussian source in dimension at least two, with the same positive rate for its specified full-support strongly log-concave class with globally bounded Hessian. Its general finite-q rate is (q−2)/(3q−2), sharp for the displayed conditioned-Gaussian and uniform-cube examples. At q=2 no uniform map modulus holds in dimension at least two, even with second moments exactly one. Dimension one remains isometric. See its [precise scope](preprints/001-strongly-log-concave-brenier/README.md) and [focused comparison](comparisons/2026-10-07-gaussian-finite-moments.md).

[007 v2](preprints/007-tail-brenier-stability/v2/README.md) shows that the slower finite-q exponent is not exclusive to support boundaries: one fixed positive C-infinity full-support strongly log-concave source also has that exact optimal power for every q>2. It separately extends the positive one-third result to the stated superquadratic sources with unbounded Hessian. These are compatible results, distinguished by quantitative translation regularity rather than qualitative smoothness alone.

## Nonlinear similarity extension

[006](preprints/006-modulus-nonlinear-similarity/README.md) excludes all finite-order images controlled by prescribed countable families of vanishing remainder moduli. It includes all nonflat smooth and nonconstant analytic germs for configurations satisfying the logarithmic-density hypothesis. It explicitly does not exclude all C1 diffeomorphisms or flat smooth maps, and does not solve the unrestricted Erdos similarity conjecture.

## Transport version 4: focused logarithmic-moment continuation

The [13-page v4 paper](preprints/001-strongly-log-concave-brenier/v4/manuscript.pdf) proves the sharp full-Gaussian logarithmic-moment exponent min(1/3, beta/(beta+1)), including the loss-free beta=1/2 transition, and the exact order (q−2)^(-1/6) of the best finite-q one-third constant as q decreases to two. Sharpness and the beta=0 no-uniform-modulus obstruction are for dimension at least two; dimension one is isometric. Its stated full-support smooth strongly convex source extension does not include arbitrary hard boundaries.

This focused continuation explicitly uses the complete public v3 all-P2 potential theorem; it restates that input rather than re-proving its cell-calculus argument. [Version 3](preprints/001-strongly-log-concave-brenier/v3/manuscript.pdf) remains the full record of the broader earlier potential, compact-source, tail, curve, and conditional-cell results. All historical files and independent entries are preserved. See the [precise dependency and scope](preprints/001-strongly-log-concave-brenier/README.md) and [v4 changed-file manifest](releases/2026-10-07-v4.json).
