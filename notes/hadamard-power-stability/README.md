# Quantitative stability for power Hadamard matrices

Read the [complete 27-page manuscript](source/main.pdf), with [LaTeX source](source/main.tex), [source map](source/SOURCE_MAP.md), and [build instructions](source/BUILD.md).

## Current review status

The exact final PDF and manuscript copy passed the dated [independent final-copy review](../../verification/2026-10-08-hadamard-power-stability/FINAL_COPY_REVIEW.md). That review includes the corrected compatible-rectangle boundary example and the D. Özteke bibliography correction. The [original analytic report](../../verification/2026-10-08-hadamard-power-stability/REFEREE_REPORT.md) and [revision-one limited review](../../verification/2026-10-08-hadamard-power-stability/REVISION1_LIMITED_REVIEW.md) preserve the review history.

All 30 files in `source/` are the unchanged final source snapshot: 28 manifest entries, the original release manifest and its checksum list. Their preparation-time references to a pending final-copy check are historical and are superseded by the linked final-copy PASS. This outer page only records that current status; no mathematical source or PDF was edited.

## Scope and attribution

For exactly unit-modulus matrices of order 2m, the paper studies the unnormalized operator Gram residual of all entrywise powers 1 through m-1. It proves quantitative global square-root stability, connected rectangle-graph linear estimates, explicit bounds for the stated classical quadratic family, second-order liftability criteria, and pointwise optimal local error exponents under the exact hypotheses in the manuscript. It does not assert that every odd-half-order rectangle graph is connected.

The exact classification and finite-circle geometry are attributed to mio-qwq/math at commit 0f0e59c0bfce75b89998fff413da31e957971f82, including its stated OpenAI order-six antecedent adc7f1241b42e322a6451854ab7e4b4c146bf78a. Classical quadratic MUB seeds and finite examples retain their source attributions. The required exact arguments are reproduced in the attributed appendix; the source map records the predecessor identities.

These are written proofs with AI-assisted analytic and copy checks. They are not Lean verification, professional peer review, journal acceptance or historical-priority certification. Ordinary isolation and zero ordinary defect are distinguished. No new seed-existence result, optimized constants, new license or personal authorship assignment is claimed.

Build within `source/`; the [original checksum manifest](source/SHA256SUMS) checks that frozen snapshot. The [publication identity manifest](../../releases/2026-10-08-hadamard-power-stability.json) separately binds this wrapper, the exact source archive and adjacent reviews.
