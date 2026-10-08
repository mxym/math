# PDF and source quality checks

Preparation date: 2026-10-08 (UTC).

## Rendering

The manuscript was built with two successful pdflatex passes using the supplied existing format and font map. No package or tool was installed. The final second-pass log contains no undefined references, undefined citations, overfull boxes, or underfull boxes. Bibliography alignment was adjusted after the first render to remove excessively stretched spacing; this was purely typographic.

The final PDF has nine US Letter pages, no encryption, no JavaScript, and no form fields. All pages were rendered with `pdftoppm -scale-to 1600 -png`. Every page was visually inspected. The bibliography page was re-inspected after its alignment adjustment. Equations, theorem/proof text, integral signs, exterior-square symbols, Greek letters, accents, page numbers, section headings, and links show no clipping, overlap, replacement boxes, or missing content. The final references occupy part of the last page naturally; there is no blank page.

## Text and cross-references

`pdftotext -layout` extracts nine nonempty pages with sequential page footers 1 through 9. The statement, all proof sections, the rational/integer conclusion, verification disclosure, and both references are present. The final PDF source has 26 resolved numbered equations. The complete Markdown copy has the matching equation tags 1 through 26 and no unresolved reference syntax or citation placeholders.

All extracted word bounding boxes lie within the page boundaries. Poppler represents a few extensible mathematical delimiters as low control characters in its bbox XML; the structural checker removes those XML-invalid text characters solely for parsing, without changing any coordinates. The PDF render, rather than the text extraction, is authoritative for exact mathematical glyph appearance. No replacement characters or unresolved `??` markers appear in the plain extracted text.

The automated structural results are in `verification/check_document_integrity.log`. These document checks do not replace mathematical review.

## Mathematical reproduction

Both independent supplied algebra verifiers were run afresh; their output agrees byte for byte with the original reference logs. A supplementary standard-library exact test passed for all q-permanent coefficients and four rational q-value/derivative checks on each of 30 rational matrices under positive denominator scaling. No test run is described as a finite numerical real counterexample or a proof-assistant certificate.

## Optimized-Python safety checks

All three mathematical verifiers and the assertion-based document integrity checker now fail closed when Python disables assertions. The guards are explicit `if not __debug__` checks, not assertions. Sixteen subprocess negative tests cover `-O`, `-OO`, `PYTHONOPTIMIZE=1`, and `PYTHONOPTIMIZE=2` for all four checkers. Each exits with code 2, prints the expected diagnostic, and emits no success output. Normal-mode mathematics was rerun after the guard insertion; both independent outputs still agree with the original reference logs. The independent source bodies are unchanged apart from the guard.


## Release portability projection

The published build wrapper defaults to ordinary `pdflatex` and accepts `LOCAL_TEX_DIR` only when explicitly set. Its default/custom command selection and missing-format rejection were checked using temporary command stubs; this test did not rerender or modify the frozen PDF. The archived second-pass log is a disclosed publication projection with only the absolute custom TeX directory replaced by `<LOCAL_TEX_DIR>`; its compiler diagnostics are otherwise unchanged.
