# Typesetting and preservation QA

Completed 8 October 2026. Scope: source identity, faithful notation and proof packaging, build integrity, and visual layout. This is not another mathematical audit or formal verification.

## Source and structure checks

- All three original proof files were checked against their specified SHA-256 values before and after typesetting. The included copies are byte-for-byte identical.
- All 30 source sections are represented: 12 top-N, 9 binary mass, and 9 general moment.
- All 99 original display tags are retained: 37 top-N, 44 binary mass (43 numbered plus SV), and 18 general moment. Every tag is present in the rendered PDF text.
- Complete proof paragraphs were retained, with the typography and limited editorial changes documented in `SOURCE_MAP.md`. No proof is replaced by a computational experiment or by the review verdict.
- The top-N paper displays (P), names 001 v3 Theorem 1.1, gives the permitted source class, and says its proof was not reviewed in this series. The lower constructions remain independent of (P).
- The second and third papers state their independence from (P). The third identifies the exact second-paper geometry and coupling dependencies.
- The general-moment endpoint proofs retain the repaired comparison-only arguments. They do not infer derivative limits from comparability or invoke the extra assumptions in Section 6.
- The source-support qualifier in the selected-scale convex construction is explicit. All support, dimension, mass-range, moment, and small-distance qualifications remain in the papers.

## Visual checks

The final PDFs contain 12, 11, and 9 pages respectively. Every page was rendered as a PNG at 110 dpi and inspected. Checks covered formula glyphs, delimiters, subscripts/superscripts, inequalities, equation tags, line and page breaks, headings, page numbers, margins, and link presentation.

The top-N paper received a shorter long section heading and readable displayed fixed-revision reference labels. The binary paper's long GitHub link display was shortened and its literature list compacted to avoid an orphan final page. In the general-moment paper, the normalization and halfspace displays were split for breathing room, the three main formulas were aligned together, repeated metadata was condensed, and the bibliography was set in a standard smaller font. Every changed PDF was rebuilt and its changed pages re-rendered; the final general-moment PDF was re-inspected in full.

No clipping, text/formula overlap, missing glyphs, equation-tag collision, or unresolved reference remains. All fonts are embedded. The source proofs' scope statements and references are readable.

## Reproduction and limitations

All three PDFs rebuild byte-for-byte in clean output directories under the recorded toolchain. `INTEGRITY_CHECK.json` and `REPRODUCIBILITY.json` provide the machine-readable checks. `verify_bundle.py` checks source hashes, section/tag coverage, rendered tags, and available build diagnostics; it is not a proof checker. Source-hash identity, successful TeX compilation, and visual QA do not imply mathematical formalization or historical novelty.

No Git publication, release creation, user attachment, or external upload was performed by this preparation step.
