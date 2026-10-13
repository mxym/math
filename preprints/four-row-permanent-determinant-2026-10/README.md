# Sharp four-row permanent–determinant inequality and complete equality

Yongxian Zhang, School of Computer Science and Engineering,
South China University of Technology. ORCID 0009-0000-3864-3536.

[PDF](paper.pdf) · [TeX](paper.tex) · [Standalone source ZIP](paper-source.zip) ·
[aiXiv:2610.01489](https://aixiv.online/abs/2610.01489).

For every actual complex 4 × 4 matrix A and every real c ≥ 0,

\[
|\operatorname{per}A|+c|\det A|
\le \max\{3/2,1+c\}\prod_i\|A_{i,*}\|_2.
\]

The constant is attained and optimal. Equality holds exactly for a zero row,
a flat rank-one matrix with c ≤ 1/2, or a monomial matrix with c ≥ 1/2.
For every real t, the normalized norm of per A + t det A is
max(3/2, 1+|t|). All these principal conclusions have complete Lean proofs.

The four-page manuscript is a reading edition of the principal results in
[the existing research note](../../notes/four-row-permanent-tradeoff/PAPER.md).
It includes the full elementary proof, including the transition weight and
both directions of equality. The note's other rectangular, quantitative,
convex-power and tensor extensions are not included in the formalization claim.

The proof projects are
[four-row-complete-equality](../../formalizations/four-row-complete-equality/README.md)
and [four-row-permanent-tradeoff](../../formalizations/four-row-permanent-tradeoff/README.md).
The classification endpoint is `FourRowTradeoff.sharp_four_row_complete`.
Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are pinned.
The archived 2026-10-09 audit freshly built 12 modules and replayed
112 roots / 15,593 dependency declarations into an empty kernel at trust zero,
using only Classical.choice, Quot.sound and propext. This editorial preparation
does not claim a new execution of that audit.

The present PDF was compiled twice with pdfLaTeX, all four pages were rendered
and inspected, and the final log has no overfull or underfull boxes or LaTeX
warnings. aiXiv's source-only dry run also compiled successfully. The published
packet supplies both the exact source ZIP and this checked PDF.
[BUILD_REVIEW.json](BUILD_REVIEW.json) binds the local artifacts.

Research and writing used OpenAI AI assistants. No external funding was received.
This is a public preprint, without a claim of external human peer review or
historical priority. Original material is all rights reserved; existing
third-party licenses and notices remain in force. No agent sessions were uploaded,
following the author's instruction to minimize disclosure.
