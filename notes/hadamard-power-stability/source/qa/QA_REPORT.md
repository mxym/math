# Manuscript preparation QA

Date: 8 October 2026 UTC.

## Outcome

The prepared manuscript has 27 US-letter pages. All 27 pages were rendered with Poppler at 100 dpi and inspected for typography, display alignment, legibility, margins, page numbering, matrices, section transitions, and bibliography layout. No clipping, overlap, missing glyphs, or unreadable equations was found in the final render.

Final PDF SHA-256:

```text
53ed15d469ae89d8735778b411431fe5e8c4b4ce774249478585e6c59da4d334
```

## Build checks

- Reused existing system pdfTeX 1.40.26 / TeX Live 2025-dev resources and an existing format/font-map cache.
- No package download, new format generation, large compilation, Lean build, Git operation, or publication occurred.
- The final three-pass compile completed with shell escape disabled.
- Final log: no undefined references or citations, no overfull horizontal/vertical boxes, no missing-character warnings, and no fatal errors.
- The benign epstopdf warning says shell escape is disabled; no EPS input is used or needed.
- PDF metadata records the title, subject, keywords, and fixed 2026-10-08 UTC date. No author identity was invented.
- Text extraction contains no replacement character. Independent page-box inspection found no text span outside a page.

## Visual record

- Pages 1–2: title, abstract, and contents; headings and page references clean.
- Pages 3–7: notation, quantitative scalar lemmas, supports, odd trace obstruction and rounding; displays and fraction baselines clean.
- Pages 8–11: all-half-order theorem, nonroot rate, order-four matrices, integer tangent bounds and certificates; no truncated matrices or displays.
- Pages 12–17: graph/kernel proof, component obstructions, quadratic block and neighbor formulas; long formulas fit within margins.
- Pages 18–22: two-jet theorem, sign/rank-one geometry, all local exponent cases and open questions; no missing proof paragraphs.
- Pages 23–25: attributed exact appendix, corrected explicit order-four rectangle labels, beginning of certificate appendix; clean.
- Pages 26–27: order-ten matrix, exact certificate values, and references; ragged-right bibliography removed undesirable stretched spacing.

The last layout change affected only pages 26–27; image hashes confirmed pages 1–25 were unchanged, and pages 26–27 were re-inspected after the change. PNGs and extracted text are local preparation evidence, not required publication assets.

## Source preservation

All 14 revised source-manifest entries and all three pinned external exact-source snapshots were verified byte-for-byte before/after preparation and remain unchanged. Both copied certificate files match the reviewed source bytes.

A separate read-only editorial source-fidelity pass compared all eight mathematical notes with the manuscript. It found all assumptions, constants, thresholds, proof chains, scope limits, and attribution layers preserved. It identified two material wording/example issues and one first-use notation issue; each was repaired and received a scoped read-only recheck. Details and exact ratio calculations are in `provenance/EDITORIAL_CORRECTIONS.md`.

This QA and source-fidelity pass is not a new independent mathematical validation. In particular the original analytical reviewer still needs to check the final manuscript and the corrected boundary-example label before public release. The prior analytical and limited revision-review status of the frozen research batch is preserved without enlargement.

## Author-initial correction recheck

Following the final-copy reviewer’s bibliographic correction, only `references.tex` changed among TeX files: O. Özteke became D. Özteke. The rebuilt PDF remains 27 pages. Only rendered page 26 differs; it was re-inspected and is clean. The complete previous package and hashes are preserved separately. See `provenance/BIBLIOGRAPHY_AUTHOR_CORRECTION.md`.
