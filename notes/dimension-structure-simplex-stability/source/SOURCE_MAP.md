# Source map and proof coverage

All sources below are mathematical work artifacts. The frozen source package remains untouched. Hashes of all 55 frozen payload files are in `SOURCE_MANIFEST.json`; the same manifest binds the reused TeX exposition sources. This map separates mathematical provenance, review coverage, and manuscript preparation.

## Main paper

| Manuscript location | Complete mathematical source | Coverage and review boundary |
|---|---|---|
| Section 1, invariant and main theorem | `dual_facet_linear_retention_20261008/FEW_FACET_DIMENSION_ASYMPTOTICS.md`; `quadratic_dimension_candidate_cloud_report_20261007.md` | Same actual invariant and original prescribed maximum. Unrestricted bound stated only as retained prior result. |
| Section 2, clipping vertices, forest determinant, all vertex maxima, every continuous nonvertex maximum, exact centroid excess, equality examples | `dual_facet_linear_retention_20261008/CLIPPED_SIMPLEX_EXACT_RETENTION.md`, §§1–6 | All proof steps and zero/tie/single-good cases preserved. Source independent review bound by `dual_facet_linear_retention_independent_review_20261008/REVIEW_BINDING.json`. Corrected “form a basis” wording retained. |
| Section 2, arbitrary one-corner bodies | `dual_facet_linear_retention_20261008/ONE_CORNER_ARBITRARY_BODY.md` | Complete proof, t=1 endpoint, apex-specific estimate, and conditional actual-chain observation. Same independent four-note review. |
| Section 3, signed cofactor theorem and concentration | `dual_facet_linear_retention_20261008/FEW_FACET_COFACTOR_DEFECT.md`, §§1–3 | Rank, both signs, cofactor difference, actual invariant, sorted weighted mass, zeros and nonrealizability warning retained. Same independent review. |
| Section 3, actual clipping, exact truncation, square-pyramid specialization | Same cofactor note, §4; exact truncation rational expression from `vertex_excess_sharp_exponent_20261008/SHARP_VERTEX_EXCESS_EXPONENT.md`, §7 | Irredundancy required before division by facet area. The explicit exact truncation expression is the retained formula, also obtained by the displayed cofactor substitution. |
| Section 4, actual facet selection, cap lemma, all defect scales, sharp exponent, leading coefficient | Few-facet asymptotics note; `vertex_excess_sharp_exponent_20261008/SHARP_VERTEX_EXCESS_EXPONENT.md`, §5; quadratic report §§5,7 | All quantifiers and strict/inclusive gates retained. Finite-facet selection is proved in Appendix B and is not imported from compact-limit Lean. |
| Section 4, square-pyramid direct certificate | `dimension_stability_investigation_20261007/obstructions.md`, §§1–3 | Explicit facets, determinant sums, actual defect, maximum simplex, and barycentric excess reproduced. Its unrelated product/join/anisotropic results are not claimed as new theorems in this manuscript. |
| Section 5, projection structure | `projection_retention_deep_20261008/FULL_PROJECTION_CORE_AND_FACE_HIERARCHY.md`; `FINITE_SPECTRUM_CONCENTRIC_CORE.md` | Both core proofs, complete finite-spectrum proof and uniform branch, face hierarchy, comparison-simplex consequence and necessary countermodel tests. Parent traditional/integration review, not blanket independent authorship. |
| Section 6, inverse rigidity and retention | `inverse_minor_deep_20261008/EDGE_SUPPORTED_RIGIDITY.md`; `LOW_DIMENSION_AND_POSITIVE_DEFINITE.md`; `theory_worker/rigorous_partial_results.md`; `theory_worker/FINAL_FOCUSED_AUDIT.md` | Full cycle/tree and minor-reduction argument, all-maximizer averaging, explicit P-chain compatibility, and all stated additional cases. Parent reading plus separate theory-worker contribution/audit. |
| Appendix A, finite determinant assignment | Reused exact TeX input `vertex_excess_manuscript_20261008/sections/03_assignment.tex` | Complete retained proof, unchanged mathematical body. This is supporting prior material, not a new independent manuscript audit. |
| Appendix B, actual identities and finite enclosure | Reused TeX input `vertex_excess_manuscript_20261008/sections/04_enclosure.tex`; frozen finite bridge §5 and quadratic report §§1–4 | Full raw facet/pyramid identity, finite law, witness assignment, width, actual-facet selection, atom correction, mixed-volume root, projection error. Only a cross-reference and a label adapted from reused TeX. |
| Appendix C, review and open boundary | Three version-bound reviews; frozen total series report | Review dispositions are attributed by role and scope. Not an assertion that source review certifies this transcription. |

Paths in the first two columns are relative to `research_math/` in the retained workspace. The local audit snapshot `sources/frozen_series.zip` preserves the frozen relative paths and all source bytes. The two directly reused TeX originals are separately snapshotted under `sources/reused_*.tex`.

## Explicit standard inputs

Cauchy projection formula, zonotope volume, divergence identities, compact convex separation, finite-dimensional convex hull theorem, determinant multilinearity and Cramer's rule, Jacobi complementary minors, Neumann series, Cauchy–Binet, classical Brunn–Minkowski, the first mixed-volume formula, and Minkowski's first inequality are used in their stated conventional forms. The book citation is bibliographically verified against the publisher on 8 October 2026. This is not a literature novelty search.

## Review distinctions

- Few-facet: independent traditional review of all four notes, with exact replay plus independently implemented forest/cofactor checks. It inspected the upstream interface rather than re-proving the entire older actual-body theorem.
- Projection: parent traditional and integration review. The parent supplied the uniform rho≤1/3 refinement; the originating projection worker cross-checked it. That contribution is not labeled independently authored or independently parent-reviewed.
- Inverse-minor: parent traditional reading plus theoretical worker proof material and final focused audit. The latter review’s scope is explicitly stated in its final uppercase `FINAL_FOCUSED_AUDIT.md`; earlier lowercase preliminary material is not substituted for that final review. The reviewer was also a proof contributor, so the entire core is not described as wholly external independent review.
- The theory note’s occupancy, regularization, and dominant-matching reductions are reproduced with complete proofs, but their presence in the bound source list is not represented as a separate independent proof audit of each auxiliary result.
- Manuscript: source-to-TeX preparation, internal proof-coverage check, strict build, and visual QA. Final parent copy audit is pending. No source review is promoted into a completed independent review of this final PDF.

## Excluded claims

No new Lean formalization or kernel replay. No professional peer review, novelty, or first-discovery certification. No exact fixed-d optimum. No unrestricted O(d) theorem or superlinear actual-body counterfamily. No replacement of a prescribed maximum by the concentric core. No actual-defect inference from arbitrary signed cofactors or finite matrix data. No unconditional edge-supported actual-e result from an unrelated enclosing simplex. No new result from the separate d+2-vertex circuit programme.
