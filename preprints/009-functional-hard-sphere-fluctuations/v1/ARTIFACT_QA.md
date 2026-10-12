# Artifact verification for version 1

Verified 7 October 2026.

## PDF and build

The complete paper is 19 Letter-size pages. The final PDF SHA256 is:

`bd5004c4ad2430cff1baf92f2f31903320263dbe95cb222d5d36c739b33f201f`

A clean source-only rebuild and a separate independent review rebuild in fresh directories both produced the identical PDF. The source archive contains the same complete mathematical source and build entry point; its internal `SOURCE_SHA256SUMS` permits verification independently of the PDF. The release-level `SHA256SUMS` covers the source, documentation, source archive, and matching PDF.

The verification toolchain was pdfTeX 1.40.26 (TeX Live 2025/dev/Debian), latexmk 4.86, and Poppler pdftoppm 26.05.0. The build uses standard TeX packages and needs no network connection. Rebuilding with a different toolchain can change PDF bytes without changing the mathematical source.

## Content and rendering

- All 19 pages were rendered at 110 dpi and checked. The version-1 first page was inspected separately; pages 2–19 have identical rendered PNGs to the fully inspected mathematical-review copy.
- No clipped text, missing glyphs, overlapping content, stray markup, or isolated proposition heading remains.
- The TeX build has no warnings, undefined references, missing-character reports, or overfull/underfull boxes.
- All 47 labels are unique and all 75 internal references resolve.
- All 24 exact upstream labels listed in section 2 exist in the pinned source.
- The public-version change consists solely of three editorial substitutions in the date, manuscript-status sentence, and PDF subject. All eight section files are byte-identical to the mathematically reviewed version.
- The public title remains *Functional hard-sphere fluctuations on regular kinetic intervals*.
- The mathematical paper does not depend on a numeric repository identifier, private notes, build logs, review working files, or planning documents.

## Mathematical scope

The full assembled proof was reviewed under the explicit imported analytic package. The review identified and verified the repeated-pair schedule-refinement repair now stated in section 4. The full review scope and its limitations are recorded in `AUDIT.md`; the imported-versus-new proof boundary is recorded in `DEPENDENCIES.md`.

This verification does not replace external peer review, independently establish every imported kinetic theorem, or claim publication priority. No quantitative CLT rate, fixed-negative-Sobolev tightness theorem, or true-flow high-moment transfer is asserted.
