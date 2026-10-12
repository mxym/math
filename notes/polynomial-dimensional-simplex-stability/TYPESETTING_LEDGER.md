# Typesetting ledger

Date: 7 October 2026.

## Purpose and authoritative inputs

`proof.tex` and `proof.pdf` are English mathematical typesetting derivatives of the frozen written refinement and the square-pyramid lower-bound proof. They are not replacements for the archived source bytes. The governing mathematical statements, hypotheses, constants, case distinctions, and argument order are those of these inputs:

- `POLYNOMIAL_REFINEMENT.md`: SHA-256 `2b398cba3afd73819dbf90d5106e64be64ba06a07f9e42d23f4c2037ff5cd791`.
- The exact byte range beginning with `## 1. ` and ending immediately before `## 9. ` in that file (Sections 1–8): SHA-256 `94c4e777b0000e5e33e024d59c47e258594fbfacc554e4faa91f8b5264c503f5`.
- `SQUARE_PYRAMID_LOWER_BOUND.md`: SHA-256 `dee887e50590cd750d5b211acd9015fa57db5bd70786dcd67ec701674139596e`.
- Original `SOURCE_PINS.json`: SHA-256 `5026125b9ca0a649bfec0c18b23a959621955edf5b0e88bdf1a1d32507e15ba2`.

All four pinned mathematical source manuscripts were read completely for this conversion. Their exact URLs and hashes are retained in the release source pins. No new external-literature verification is claimed by the typesetting process.

## Source-to-output correspondence

- Original title and Result → title, an editorial abstract, and the unnumbered Result and conventions section. All theorem quantifiers and exact definitions of `m`, `R`, `M`, `C`, `J`, `L`, `G_d`, and `e_0` are retained.
- Main Section 1 → typeset Section 1, with the original three unnumbered subheadings. The first absolute determinant moments, all `N` witnesses, `V` as the lifted determinant rather than simplex volume, `V`-weighted selection, the `D=0` case, clipped negative-coefficient cases, Borel tie-breaking, and the separate dispersion implication are retained.
- Main Section 2 → typeset Section 2. The originally prescribed maximum simplex, regular-simplex normalization, exact radius `R=d sqrt(d+2)`, barycentric estimate, and global `d+1` excess bound are retained.
- Main Section 3 → typeset Section 3. The actual cone law, source cone representation, normalized defect, Cauchy factor `1/2`, chord-width argument, dispersion bound, and genuine enclosing simplex are retained. No arbitrary centered law is identified with a convex-body cone law.
- Main Section 4 → typeset Section 4. The facet weights, barycentric correction, normalized projections, mixed-volume scale control, absolute projection deficit, and genuine inclusion are retained.
- Main Section 5 → typeset Section 5. The compact enclosing-body hypothesis, radius of `K`, farthest-point cap, inscribed cube, rearrangement gate, and zero-deficit case are retained.
- Main Section 6 → typeset Section 6. The exact local gate, original maximum simplex, stochastic-matrix/permanent argument, all matched vertices, local coefficient `G_d/2`, and `e=0` case are retained.
- Main Section 7 → typeset Section 7. The global branch and affine pullback about the original centroid are retained, including the statement that affine pullback need not preserve a Euclidean ball.
- Main Section 8 → typeset Section 8. Every inequality in the polynomial estimate, the induction bound on integer dimensions, the factors `256`, `80`, `1280`, `576`, and the final `737280 d^6 < 2^20 d^6` are retained.
- Main Sections 9–10 → typeset Sections 9–10. Scope limitations, exponent obstruction, realized lower bound, asymptotic statements, open linear-growth target, literature distinctions, and non-novelty/non-formalization caveats are retained. Historical model-review and literature-inspection statements are explicitly attributed to the frozen refinement rather than represented as new typesetting findings.
- Square-pyramid introduction and Sections 1–2 → Appendix A and subsections A.1–A.2. The universal excess bound, polytope and simplex, arbitrary-vertex maximality, barycentric excess, optional pyramid calculation, full facet list, volume, both exact maximal-minor sums and their counts, coefficient comparison, and illustrative numerical values are retained.

## Purely editorial changes and source-derived clarifications

1. Plaintext and Unicode mathematical notation is converted into conventional LaTeX, with displayed equations, aligned calculations, italic mathematical symbols, and a standard 11-point article layout. Equations are not truncated or replaced by prose summaries.
2. A short abstract summarizes only statements already in the frozen proofs. The theorem is placed in an unnumbered theorem environment. The author credit follows the original sharp manuscript: “AI-assisted research supplement to entry005”; no individual authorship is invented.
3. The main numbered Sections 1–8 remain in their original order. Some headings are lightly rephrased for readable English; Section 2 receives a deliberate line break. Sections 9–10 remain separate. The complete lower-bound companion is integrated as Appendix A.
4. The meaning of the projection body `ΠK` is stated using its support function, and `𝒫K` is identified as a pyramid over `K`, explicitly referring to pinned entry005 v3, Section 1. The dimension of the projection ratio’s argument is made explicit. These definitions come from the pinned sources; the operator is not redefined.
5. The generic facet identity and definitions of the two maximal-minor sums are recalled from pinned entry005 v3, Section 1, before the square-pyramid certificate. Their local reuse of the letters `H` and `L` is explained so it cannot be confused with the main proof’s witness and cap constant.
6. Standard notation is clarified without changing any assertion: `π_K(u)` is identified with the orthogonal projection volume; `ν_P⊂B_2^d` is typeset as `supp ν_P⊂B_2^d`; “opposite w_i” is expanded to “opposite the facet with polar normal w_i”; the diameter symbol `Δ` in Section 1 is identified as local to that subsection.
7. The sharpness sentence specifies the maximum simplex used in the cited obstruction, so it does not suggest that every maximum simplex of a truncation has identical excess. Its exact `E=(d+1)t` and defect asymptotic are unchanged.
8. The companion’s source equation labels `(1)` and `(6)` become `(1)` and `(2)` in Appendix A, with all references adjusted. All associated formulas are unchanged.
9. Source URLs are presented as clickable bibliography entries. Classical-source attribution to Schneider is inherited from the pinned manuscripts. The three literature-positioning entries retain their original limited roles; none becomes an imported quantitative estimate.
10. Routine second-person wording (“the user’s originally prescribed”) becomes reader-independent mathematical prose (“the originally prescribed”). Operational source filenames are retained only where they identify companion evidence.

## Preservation and scope safeguards

- No theorem, constant, hypothesis, zero/local/global case, or step of the core proof is intentionally weakened, strengthened, omitted, or added.
- No replacement maximum simplex is selected. The final containment is about the centroid of the originally prescribed simplex.
- First absolute determinant moments remain first moments. There is no covariance or second-moment substitution.
- The square-pyramid certificate is an actual polytope calculation. No arbitrary-law realization assumption is introduced.
- Separate anisotropic and simultaneous-truncation material is excluded.
- The written proof, finite arithmetic checks, visual QA, model review, human peer review, and proof-assistant formalization remain distinct. This conversion does not assert novelty, priority, human peer review, or Lean verification.
- Typesetting assigns no new license. Existing source attribution and applicable source notices remain applicable.

## Build and visual verification

Run `./build.sh` from a POSIX shell with TeX Live installed. Required programs are `pdflatex` and `kpsewhich`, plus `pdftex` for the fresh-format fallback. Required LaTeX packages are `fontenc`, `inputenc`, `lmodern`, `geometry`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `microtype`, `xurl`, and `hyperref`, together with their normal dependencies. It fixes `SOURCE_DATE_EPOCH=1791331200` (7 October 2026, 00:00 UTC), `FORCE_SOURCE_DATE=1`, UTC, and the C locale; disables shell escape; runs three LaTeX passes; and writes scratch files only under `build/`. The PDF omits creation/modification timestamps and trailer identifiers. The script never edits the TeX or archival sources, includes no absolute machine paths, and performs no network retrieval.

If the TeX installation lacks usable filename databases or a format, the script discovers its trees through `kpsewhich` and builds a fresh local format from installed sources. It does not copy an existing format cache. The generated PDF was also checked against two clean source-only rebuilds in distinct directories, each using a separately generated format.

`PDF_QA.json` records the final PDF hash, page count, rendering and viewing method, exact pages inspected, independent visual inspection, and compiler-warning status. Visual QA is layout verification, not a substitute for mathematical review.
