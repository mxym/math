# math

Mathematical research manuscripts and supporting verification material maintained at **mxym/math**.

中文：本仓库收录数学研究稿、完整证明和可编辑源码。当前三份稿件分别涉及最优传输、二次整数阶中的有限步长图，以及精确维数的不可嵌入紧集。请从 [CONTENTS.md](CONTENTS.md) 进入各稿件。

## Collection

| ID | Manuscript | Latest | Status |
| --- | --- | --- | --- |
| 001 | [Sharp one-third stability of Brenier maps for strongly log-concave sources](preprints/001-strongly-log-concave-brenier/README.md) | v1 | Research draft |
| 002 | [Bounded step walks on irreducibles in quadratic orders](preprints/002-quadratic-order-moats/README.md) | v1 | Research draft |
| 003 | [Compact Banach space obstructions with Assouad dimension two](preprints/003-assouad-two-zero-box/README.md) | v1 | Research draft |

## Reading and verification

Each manuscript directory contains a complete PDF, LaTeX source, build instructions and upstream attribution. The arguments were developed with AI assistance and checked against explicit hypotheses and proof dependencies. **These are research manuscripts, not externally peer-reviewed or fully machine-formalized results.** See [verification/STATUS.md](verification/STATUS.md) for the precise scope of checks.

Several methods build on the public [OpenAI/math collection](https://github.com/openai/math), pinned at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The manuscripts distinguish inherited arguments from the extensions developed here. No affiliation with or endorsement by OpenAI is implied.

## Versions and disclosure

Versions are kept in separate `v1`, `v2`, ... directories. Corrections and extensions are recorded in [CHANGELOG.md](CHANGELOG.md); earlier versions remain accessible. [releases/2026-10-07-v1.json](releases/2026-10-07-v1.json) records exact file hashes. GitHub commit timestamps document this repository's disclosure history; they do **not** certify mathematical correctness or first discovery. Literature comparison continues separately, and no priority assertion is made.

## Rights and provenance

The upstream OpenAI material retains its Apache-2.0 license, reproduced in [third_party_licenses/openai_math_LICENSE.txt](third_party_licenses/openai_math_LICENSE.txt). See [NOTICE.md](NOTICE.md). No additional license for newly authored material has been selected; do not infer one merely from the repository being public.
