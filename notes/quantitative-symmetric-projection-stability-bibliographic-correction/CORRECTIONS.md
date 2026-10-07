# Separate bibliographic correction

Date: 7 October 2026. Status: requested attribution corrections applied;
independent model primary-source audit passed; original mathematics preserved.
This is a separate correction bundle. The earlier Library complete and source
ZIP releases remain immutable, and no Library identity is replaced by this
bundle. No upstream repository file has been edited, pushed, or published.
Subsequent research on a stronger exponent is excluded from this correction.

## Source and release identity

The proposal was prepared against public commit
`dd5c29fc50c3e0694591260f60f3030d551d304d`. Read-only retrieval confirms that its
supplement `paper.md`, `LITERATURE.md`, and entry005 v4 `paper.md` match the
original local release sources byte for byte; see
`corrections/public-proposal-source-check.json`.

The immutable original complete ZIP is 471,564 bytes, SHA-256
`c0f384da54e2a6f5b1c7dd4cc3e023ebf831e9796dfe4d22305779b1fe894ee6`.
Its source ZIP is
85,173 bytes, SHA-256
`a8cf2d56804184596a5c92023a266a3aa9f49b52c2b396e5d9a10b2a02af4bbb`.
Original article and packaging-source hashes are recorded in
`corrections/baseline-identifiers.json`.

The mathematical dependency commit remains
`6785c1c830f8e19e2eb07b0bb89f4d475a8b154a`; `DEPENDENCIES.json`, its companion
Markdown file, and `code/dependency-inputs.json` are unchanged. The v4
attribution copy is review material, not a replacement dependency pin.

## Exact requested editorial changes

The complete unified article and literature diffs are
`corrections/paper.md.patch` and `corrections/LITERATURE.md.patch`. Each changed
block, including its exact before/after text, is also stored in
`corrections/editorial-replacements.json`. The changes are:

1. In article Section 7, replace the numerical Wasserstein/containment scaling
   comparison for Böröczky–De's truncated cubes with qualitative geometric
   context, the published p. 302 locator, and the distinction between a fixed
   cube comparison and Theorem B's independent scalar calculation and distance
   bound against the entire affine one-/two-dimensional product class.
2. Make the corresponding replacement in `LITERATURE.md`; retain Example
   1.4's zero cone mass on the specified equator when describing anisotropic
   weak-measure collapse.
3. Insert the requested matroid attribution immediately before entry005 v4
   Lemma 5.1. The standalone insertion is provided in
   `corrections/v4-attribution.patch`, with `v4-paper.before.md` and
   `v4-paper.after.md` for review. No upstream v4 file is changed.
4. Insert the exact rank-two matroid antecedent before article Lemma 4.1,
   separating the established decomposition from quantitative approximation
   by small expected cofactors and a conditioned basis.
5. Insert the Koshevoy–Mosler zonoid/lift-zonoid determinant identities after
   the definitions of A and B in Section 2, with the stated normalization and
   the volume-ratio expression for the inherited cone-law identity.
6. Add the Böröczky–Henk Lemma 3.1(i) attribution adjacent to article Lemma
   5.1's containment bound, noting the constant 2 from central symmetry.
7. Add Saroglou's Weil-body terminology and second projection-body context to
   article Section 7 and the literature comparison. Keep its three-dimensional
   zonoid Theorem 1.2 distinct from the present functional; disclose that Weil's
   original 1971 article was not obtained.

The added primary references and source-extent table entries accompany these
changes. `README.md`, `AUDIT.md`, `BUILD.md`, `PDF_QA.md`, and the packaging
script identify the separate correction and record its rebuilt files. Their
exact textual differences are in `corrections/supporting-documentation.patch`.
New review/provenance files are named in the manifests. The archive prefix and
filenames include `bibliographic-correction` so this bundle is distinguishable
from the immutable earlier release.

No external main theorem is challenged in this correction. The unnecessary
numerical metric/exponent comparison is omitted. No claim of novelty, human
peer review, or formal mathematical certification is made.

## Preservation and verification

`results/editorial-preservation.json` records a passed exact reverse-editorial
check. Reversing only the recorded article edits reconstructs original
`paper.md` SHA-256
`08f6f55c6a694da05d348d3dcbda18be186044fd39570c51bf786507aaef862c`;
reversing the literature edits reconstructs its original bytes. Deleting the
single v4 attribution paragraph reconstructs the pinned original v4 SHA-256
`19eb5aa0c79e34280cc3619cf40c1bea7acda6f6ec1161b05fbb6bf2308fda81`.
Every original mathematical theorem and proof is therefore retained verbatim.
The added zonoid formulas are background identities, not changed theorem
statements. Run the standalone preservation check with:

```sh
python3 code/check_editorial.py
python3 -O code/check_editorial.py
```

`corrections/unchanged-mathematical-files.json` verifies unchanged dependency
records, inherited exact-code inputs, exact programs, and shipped analytic
regression reports. The 5,696-case suite was replayed from this corrected copy;
ordinary and optimized Python outputs matched. Clean Markdown-to-LaTeX/PDF
rebuilding and archive extraction/replay checks are recorded separately in
`BUILD.md` and `results/`. All 11 PDF pages were rendered at 110 dpi and visually
reviewed; see `PDF_QA.md`.

`PRIMARY_LOCATORS.md` records the independent model read of all cited primary
locators, including normalization, page numbers, and retained hypotheses.
Bibliographic review, byte identity, and finite regression tests have distinct
scopes; none alone formally certifies the infinite-dimensional analytic proof.

已完成独立的文献归属修订包；原版保持不变，所有原有定理与证明逐字保留，未推送或发布。
