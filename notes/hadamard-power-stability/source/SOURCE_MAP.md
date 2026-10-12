# Source map and preservation record

Base input: `research_math/hadamard_stability_revision1_20261008/`. The original frozen and revised inputs remain unchanged. Eight mathematical notes become Sections 2–9, with introductory definitions, a consolidated discussion, and two appendices. The two exact certificate files remain byte-identical. INDEX and CHECKPOINT supply inventory/dependency/open-question metadata rather than an additional theorem.

## Mathematical notes

| Reviewed source | Manuscript destination | Content retained |
|---|---|---|
| `odd_hadamard_stability.md`, attribution and §1 | §1 and Theorem 3.1 | Exact unit-modulus hypothesis, full power range, labelled dephasing, raw operator residual, `2^-24 m^-3`, `512 sqrt(epsilon/m)`, genuine seed, strict empty-set gap, normalized and row-correlation conversions |
| Same source, §§2–5 | §§2.1–2.4 | Newton coefficient induction, actual-product identity, Rouché matching with multiplicities, active supports, common-support contradiction, balanced approximate rectangle, restricted half-sum estimate |
| Same source, §§6–7 | §3.1 | Positive approximate projection, half-integer trace, `768m^2 epsilon`, `258 sqrt(m epsilon)`, nearest-root uniqueness, integer Fourier certificate, zero-residual endpoint, undoing dephasing |
| Same source, §§8–9 | §3.4, §10, bibliography | Scalar versus matrix sharpness distinction; all cited comparison boundaries and incomplete-priority warning |
| `all_half_orders_extension.md`, §§1–3 | §3.2 | All-half-order theorem, local compatibility definition, small/large phase split, `17 pi` bound, same-group integer rounding, each-half multiplicity-one certificate, zero-residual and nonexistence conclusions |
| Same source, §4 | Proposition 3.4 and proof | Explicit `G` and `K(t)`, Gram spectrum, exact residual `6(1-cos t)`, distance `2t/pi`, incident/nonincident-circle cases, distinction from odd-half-order sharpness |
| Same source, §5 | §3.3 | `s>256 sqrt(m epsilon)`, improved matching, active strips and top-left argument, `5h0`, `160 pi epsilon/s < 512 epsilon/s`, same certified seed and rectangle |
| `local_exponent_criterion.md`, §§1–3 | §§4 and 9 | Exact integer matrix, Fourier kernel proof, inverse-minor constant, cofactor bound, phase radius and residual entrance threshold, explicit quadratic residual curve and finite-root distance, conditional odd dichotomy |
| Same source, §§4–5 | §4.1, Appendix B, certificates, §10 | Both exact ranks, determinants, inverse norms, local radii/constants, pivot convention, no novel-isolation claim, no rank-deficient odd seed claim |
| `rectangle_graph_criterion.md`, §§1–2 | §§5 and 5.1 | Graph definition and degree, balanced component weights, row-and-column equations, component-constant kernel, dimension `r-1`, explicit rational gauge representative |
| Same source, §§3–4 | §§5.2–5.3 | Taylor/Fourier edge constant, diameter absorption, gauge factor four, geodesic closed-neighborhood proof, component diameter, exact and simplified entrance thresholds, conditional `48H epsilon` theorem |
| Same source, §5 | §§5.3 and 10 | General odd connectedness remains open; classical graph diameters `3,4`, local constants `12,40/3`; no inference from discreteness to zero kernel |
| `component_obstructions.md`, §§1–4 | §6 | Even support intersections, binary identity, `AG*=GA*`, Hermitian spectrum and weights one/two, XOR/Gauss-sum congruence, exactly `{1,2}` or `3 mod 4` exclusion, classification-free `m=3`, surviving partitions and residue restrictions |
| `quadratic_family_linear_stability.md`, §1 | §§7.1–7.2 | All admissible parameters, four exponent blocks, complete-square exact GH counts, normalized MUB block and Gauss dephasing calculation with `-chi(q)=1`, carefully bounded classical attribution |
| Same source, §§2–4 | §§7.3–7.4 | Within-group `K_(p,p)` minus matching, all four cross-label formulas and center case, both nonzero-slope arguments, diameter seven, `2^-34 p^-3` entrance, `56 H_(p-1) epsilon/p` rate and equivalence scope |
| Same source, §5 and comparison | §7 end, §10 | Finite-check scope, ordinary isolation versus zero ordinary defect, Conjecture 4.5 boundary, invalid Galois-on-real-coefficients inference explicitly excluded |
| `second_order_tangent_cone_20261008.md`, §§1–4 | §§8–8.3 | Full admissible two-jet iff statement, acceleration convention and caveat, conjugate-power separation including self-conjugate powers, both Fourier conditions, real distance-geometry lemma, balanced rank-one signs, dephased rectangle and compatibility proof |
| Same source, §§5–6 | §8.4 | Component sign assignment plus rank-one condition, Sperner bound, classical three-branch case, odd parity obstruction, no inference of a zero first-order kernel |
| `local_exponents_all_orders_20261008.md`, §§1–5 | §9 | Full neighborhood/constant quantifiers and supremum definition, entire `r,b` classification, both phase radii and constants, component projection and derivative perturbation bounds, `33x` absorption, finite-circle sharpness, nonroot linearity, algorithm and limits |

## Remaining inherited research files

| File | Treatment |
|---|---|
| `check_tangent_rank.py` | Unchanged copy in `certificates/`; the exact E3/E5 matrices and algorithm convention are included in Appendix B |
| `tangent_rank_results.json` | Unchanged copy in `certificates/`; full pivot lists preserved there and numerical conclusions in §4.1 and Appendix B |
| `INDEX_FROZEN.md` | Inventory, theorem scopes, dependency map, and open questions incorporated into §1, §10, README, and this map. Its preparation-time “awaiting limited review” label is superseded only by the later review receipt |
| `CHECKPOINT.md` | Freeze/scope status and open questions consolidated; transient work-log wording is not treated as mathematical content |

## Revision and review records

`REVISION_NOTES.md`, `revision1.diff`, the revision manifest, `REFEREE_REPORT.md`, and `REVISION1_LIMITED_REVIEW.md` were read or checked as preparation inputs. Their exact identities are recorded in `provenance/source_manifest.json`. The source manifest's 14 entries were all verified before authoring. The later receipt accepts the limited corrections and does not expand the review into formal verification, professional peer review, or novelty certification.

The manuscript retains all required corrections: exact component-weight exclusion, ordinary-isolation/defect distinction, explicit Gauss/MUB bridge, trivial treatment of initial all-ones row/column, local compatibility definition, and full local-exponent quantifiers.

## External exact dependency

Appendix A is an attributed, self-contained presentation of the specific exact inputs used: polynomial/polygon identity, common-support product contradiction, balanced block/projection obstruction, root count inversion, compatible-circle construction and exhaustiveness, finite-circle intersections, and local branch geometry. It is derived from the three pinned external files identified in the input manifest and preserves both `mio-qwq/math` and OpenAI attribution. It also records the source's Hall–Paige product-obstruction attribution and boundary cautions.

No new theorem, constant, parameter family, existence assertion, or generalized ordinary-isolation claim was introduced. The finite-check facts additionally mentioned from the analytical review are labelled as supplementary review evidence and are not promoted to analytical premises.

## Explicit consolidation corrections

See `provenance/EDITORIAL_CORRECTIONS.md` for the optional-rectangle abstract correction, the inherited external four-by-four boundary-example label error with its exact countercalculation and corrected compatibility check, and the first-use definition of `V_G`. Third-party snapshots were not edited. The original reviewer should recheck the final typeset copy and replacement label before release.

## Bibliographic final-copy correction

The original final-copy reviewer requested the author initial D. Özteke in bibliography entry [5]. Only that letter changed in the manuscript sources; all other TeX files are byte-identical. See `provenance/BIBLIOGRAPHY_AUTHOR_CORRECTION.md` and the exact one-letter diff. The preceding complete package remains preserved in the sibling `hadamard_series_manuscript_20261008_before_bibliography_fix/`. Corrected PDF SHA-256: `53ed15d469ae89d8735778b411431fe5e8c4b4ce774249478585e6c59da4d334`.
