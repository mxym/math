# Final submission-preparation audit

**Status: PASS for the scope below; prepared, not submitted.**

Manuscript: *Counterexamples to Bapat's q-permanent monotonicity conjecture*,
Yongxian Zhang, 14 pages. This audit was conducted by the primary Codex
assistant without subagents. It is internal mathematical, editorial and
technical review, not external human peer review or arXiv acceptance.

The reviewed PDF SHA-256 is
`42aac0d142a93c85775f95842e6acd6a778c9bd607248006f771361e1b624cd5`.
The upload ZIP SHA-256 is
`205784e05e80069a7f9cbe59444e9f33467c598dee8e3792107ecb66f6c84707`.
The detailed build and source hashes are in [qa/BUILD_REPORT.json](qa/BUILD_REPORT.json).

## Mathematical statements and proof correspondence

The paper treats the original interval `[-1,1]` and the ordinary inversion
count for the fixed row order. Hermitian real-valuedness is proved by pairing
each permutation with its inverse. Sorting the real construction is an
intentional selection of row order, not an incorrect invariance claim.

The complex theorem specifies `B = VV* + epsilon I` at dimension 200,
including every coefficient row, `epsilon`, `h`, and `q0 = 1-h`. Its
comparison is `P_q0(B) > P_1(B)`; one comparison value is the endpoint 1.
The two-row expansion, binary Fischer norm, exact coefficient recurrence,
integer gap, positive-definite perturbation and derivative bounds were
checked against the archived finite proof. The second derivative argument
explicitly treats inversion counts zero and one separately.

The real theorem proves existence of an integer symmetric positive-definite
matrix and **two rational interior** parameters. It gives no explicit real
matrix or dimension bound. Its entire written proof is included: real-sphere
equidistribution, log truncation and balancing of complex maxima, four real
selector factors, Gaussian ratio/Gini calculation, ordering, concentration
at a conjugate pair, contiguous repetition, rational approximation, diagonal
perturbation, and positive common-denominator multiplication. The cloud is
fixed before the repetition limit; zeros of the product are bounded using
the original numerator rather than an undefined quotient. The rank-four
bound is asserted only for an intermediate Gram matrix. Entrywise positivity
is not asserted for either final matrix.

The combined manuscript preserves the mathematical conclusions and real
proof body of the archived packages. It adds author information, unifies
presentation and updates the verification section. It is not counted as a
third mathematical result. [SOURCE_PROVENANCE.json](SOURCE_PROVENANCE.json)
records the historical source snapshot and hashes.

## Lean evidence and its limits

Both main counterexample conclusions have complete formalizations of the
actual q-permanent, positive definiteness and decrease. Their immutable
records are cited in the paper:

| Conclusion | Exact formal endpoint | Completed recorded verification |
| --- | --- | --- |
| Specified rational complex matrix and specified gap | `BapatExplicit.explicit_rational_counterexample` | 30 roots, 22,812 dependency declarations; full finite-input continuation separately covers all 928 owned declarations |
| Integer real symmetric existence, negative derivative and rational interior decrease | `BapatRealExistence.exists_integer_real_symmetric_counterexample` | 67 freshly compiled modules, all 776 owned declarations, 54,739 union dependency declarations |

The records describe empty-kernel replay at trust level zero with only
`propext`, `Classical.choice`, and `Quot.sound`, full standard-axiom signature
checks, and rejected false-proof controls. The real Lean proof computes the
needed Gini integral directly and derives non-diagonality from the negative
derivative; it does not separately certify every printed density/CDF step.
The formal real theorem is nonconstructive and does not extract a witness.

This preparation inspected the final Lean statements and definition
correspondence, ran the complex frozen-record and standard-signature record
checks, and freshly verified all **242** files in the real publication's
checksum inventory. See [qa/SOURCE_AUDIT.json](qa/SOURCE_AUDIT.json).
It **did not rerun Lean**. The previous successful replays, rather than these
checksum checks, provide the proof-assistant evidence. Historical timed-out
input runs remain distinguished from their successful continuations.

## Fresh source-archive and exact-arithmetic checks

The actual distributed ZIP was extracted into a new directory and compiled
three times using ordinary pdfLaTeX, with shell escape disabled. The final
distributed source, ZIP and PDF bytes match that execution's hashes.
No auxiliary, log or preview PDF file is needed inside the upload ZIP.

Both copied integer checkers were run on the extracted source. The recurrence
checker and independent pair-deletion checker passed, including all 19,900
pair divisions and agreement of the four certificate integers. The PDF table
was checked to specify all 200 rows exactly as in the original byte-preserved
CSV. Both checkers reject optimized Python execution; both also rejected a
deliberately false rank-one replacement input. These are actual executions,
not stored `true` results or numerical tests of the real limiting proof.

All 40 source labels are unique, all 32 references resolve, and all cited
keys are present in the eight-item bibliography. The final log contains:

| Diagnostic | Count |
| --- | ---: |
| Overfull boxes | 0 |
| Underfull boxes | 0 |
| Undefined references or citations | 0 |
| Multiply defined labels | 0 |
| Missing characters | 0 |
| Unresolved table-width or reference rerun warnings | 0 |

Every font is embedded and no Type 3 bitmap font occurs. The harmless
`epstopdf` notice that shell escape is disabled is retained; there are no EPS
figures or shell commands in the manuscript.

## Editorial and visual review

All 14 pages were inspected individually as 110-dpi renderings. In the final
revision, only pages 3, 10 and 11 changed and were reinspected; the remaining
ten rendered pages were pixel-identical to the reviewed preceding version.
See [the contact sheet](qa/contact.png) and [rendering record](qa/VISUAL_RECORD.json).

The review checked title and affiliation, abstract scope, numbered equations,
theorem statements, proof endings, formula widths, paragraph flow, monospaced
Lean identifiers, executable commands, footnotes, table continuation headers,
all witness rows, and the final bibliography. Long identifiers were moved
to separate lines, commands to a verbatim block, and the appendix table font
was enlarged. No visible clipping, overlap, missing glyphs, orphaned section
headings or broken mathematical displays were found.

The author, email and ORCID agree with the confirmed profile. Absence of
external funding and AI assistance are disclosed. The paper does not assert
external referee approval, numerical extraction of the real witness, or
historical first-proof priority. Bibliographic details were checked against
the repository's documented primary-source screen; this preparation is not
a new exhaustive literature search. The additional citations and source-access
limits are recorded in [RELATED_WORK_AUDIT.md](RELATED_WORK_AUDIT.md).
The earlier screen read Mitchell's 2020
article, while the full 1992 and 1994 originals were not obtained.

## Remaining submission steps

The author has registered an arXiv account and is awaiting the requested
math.CO endorsement. Obtain the endorsement, choose the distribution license,
upload the source ZIP, copy the prepared metadata, and inspect arXiv's own
compiled preview. Differences in arXiv's TeX installation can change line or
page breaks, so the platform's preview remains a final operational check.
No arXiv submission has been executed in this task.
