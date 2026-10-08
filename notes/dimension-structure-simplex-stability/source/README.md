# Dimension structure in simplex stability

Unpublished English manuscript candidate, 8 October 2026. No upload, repository commit, public release, or user attachment is part of this preparation.

## Read and build

- `main.pdf`: complete readable paper.
- `main.tex`, `sections/*.tex`, `references.tex`: complete editable LaTeX source.
- `./build.sh`: three-pass, no-shell-escape pdfLaTeX build; fails on unresolved references, citations, missing glyphs, and overfull boxes.
- A configured TeX Live installation with `article`, Latin Modern, AMS packages, geometry, microtype, xurl, hyperref, and enumitem is sufficient. `pdfinfo` and `pdftotext` are used for QA.
- In the preparation workspace, the build reuses an already available TeX format/font-map cache. It never copies the cache or downloads packages. To use another existing cache with the same local unconfigured TeX installation, set `TEX_CACHE_DIR` to its directory. A normally configured TeX installation needs no cache override.
- `SOURCE_DATE_EPOCH`, omission of PDF creation dates, and a suppressed variable trailer identifier keep clean builds reproducible.

## Mathematical contents

1. Complete all-maximizer classification for a simplex intersected with any one halfspace, via weighted rooted forests, including zero/tie cases and continuous nonvertex maxima; exact original-centroid excess.
2. Arbitrary one-corner convex bodies containing an entire opposite facet.
3. Exact actual projection-body pyramid defect from signed maximal cofactors of a polytope with exactly d+2 facets, including concentration and clipping specializations.
4. The at-most-d+2-facet class: all-scale upper coefficient (d+1)H_d^(1/(d−1)), sharp defect exponent, a realized square-pyramid lower bound, and optimal coefficient divided by d tending to one.
5. Full-projection concentric cores, finite spectrum, its uniform small-radius branch, exact face-depth hierarchy, and necessary countermodel tests.
6. Two-supported stochastic inverse rigidity, prescribed and all-maximizer edge-supported retention, its explicitly compatible actual-defect corollary, and order-three, positive-definite, and local-basin cases.
7. Full finite determinant assignment and actual-facet enclosure proofs in the appendices.

The comparison core is not asserted to be the original maximum simplex. Edge support relative to an unrelated simplex does not establish the actual-defect corollary. The general linear-versus-quadratic dimension-order gap is open. The exact fixed-dimensional few-facet optimum is not determined.

## Provenance and review

`SOURCE_MAP.md` maps all proof blocks to their sources. `SOURCE_MANIFEST.json` binds the 55 frozen research payload files and the two reused TeX exposition inputs. The original series archive hash is:

631a80b594fb9a597fef15e1c76870956ecb768fbbb14f3b7953e1809970296e

Source snapshots under `sources/` and preparation evidence under `evidence/` are for candidate review. They are excluded from the minimal prospective public whitelist. The source archive has 55 payload files plus its manifest; the original payload files remain unchanged.

The few-facet source series has an independent traditional model review. The full-projection review is a parent proof/integration review, with a parent-authored uniform-branch refinement cross-checked by the originating worker. The inverse-minor record combines parent review and a separate theoretical worker's proof work and focused audit. These are not interchangeable with professional peer review or wholly external review of every contribution.

No new theorem in this manuscript has been formalized in Lean. Earlier formal evidence for the retained quadratic-dimensional theorem does not certify these new results. No novelty or priority certification is claimed. The final-copy manuscript still requires the parent reviewer’s final audit; source review alone does not certify this transcription.

## Package boundaries

`PUBLIC_WHITELIST.json` is the exact minimal prospective public set; it is a packaging definition, not permission to publish. It contains the paper, editable source, build instructions, source mapping, and checksums, with no TeX caches, rendered page images, build logs, research-review archive, or unrelated files. `package_candidate.py` creates a local clean-copy zip from this list only. No command in this package performs a network write or publication.

`QA_REPORT.md` records the completed build, page-by-page visual inspection, proof coverage, clean-copy reproduction, and any outstanding copy-review gate. `SHA256SUMS` binds the public payload except itself. `INTERNAL_SHA256SUMS` additionally binds the selected source snapshots and evidence after final preparation.
