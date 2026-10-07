# Verification record

7 October 2026. This record concerns the additive supplement *Effective simplex rigidity for the projection cone invariant*.

## Mathematical audit

The [independent audit](INDEPENDENT_AUDIT.md) finds no substantive mathematical defect in the complete public manuscript, conditional on the explicitly imported affine-invariance and cone-law identities of 005 versions 2--3. It checks the constants, all-body and nonatomic scope, every-maximum-simplex quantifier, both deficit ranges, the planar identity, and the primary-source conversion to the inherited $576e$ Banach--Mazur bound. No mathematical repair is pending.

The finalized manuscript hash is:

`paper.md`: `33651147ae32773add33066c3b60dd099209dcadd6b3b7079e3e08eeaba976d2`.

The independent audit is a model-conducted mathematical review, not external human peer review or proof-assistant formalization.

## Exact replay

Both checkers were run under ordinary Python and `python -O`. Their JSON outputs are byte-identical across those modes and match the previously recorded working-proof results.

1. Explicit constants and all range gates in dimensions 2 through 8: **PASS**.
2. Exact affine-determinant perturbations, 400 cases: **PASS**.
3. Exact stochastic barycentric matrices, 400 cases: **PASS**.
4. Nonatomic box-witness corner signs, 8,320 cases: **PASS**.
5. Planar lifted determinant, projection/difference-body and deficit identities, 200 convex polygons: **PASS**.

The deterministic final JSON digests are:

- `results/exact_gate_results.json`: `a1314c16e83e89ae9dd713d9587e4702843ab6b006a5513785d935f7c757b17d`
- `results/planar_identity_results.json`: `fe5537a32752d0f21cfdf909c59d784772a0dad8f3a69f3ca48d5f72e063bfcb`

These finite tests corroborate the written inequalities. They do not constitute an exhaustive verification of the all-dimensional theorem.

## Source and layout checks

The manuscript is authored in Markdown with displayed mathematics. `build.sh` deterministically produces the supplied standalone LaTeX source and the PDF; the LaTeX file also supports ordinary direct compilation. The final PDF has nine letter-sized pages. Every page was rendered and visually inspected after the final changes. Mathematical symbols, formula tags, margins, paragraph breaks, and the single-page reference list are legible, without clipping or overlap. The final pdfLaTeX run reports no overfull boxes, underfull boxes, undefined references, or warnings.

The complete source archive was unpacked into a fresh directory, both mathematical checkers were rerun in ordinary and optimized modes, and the PDF was rebuilt there. The resulting LaTeX source, PDF, and deterministic evidence remained byte-identical to the packaged files; the complete 20-file manifest passed again after the rebuild.

The PDF and source contain no proposed new entry-005 version number. This is an additive supplement and leaves historical files intact. Its lower-end simplex theorem does not claim to quantify version 4's symmetric upper-end stability problem.

`MANIFEST.json` pins the package's source, evidence, and generated artifacts. The manifest checker verifies byte identity only. A later theorem or typesetting change requires rebuilding the PDF, repeating the affected checks, and refreshing the manifest.
