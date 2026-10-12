# Independent semantic review: lifted B, entryA, and the same-witness bridge

Review date: 2026-10-07 UTC. Review mode: independent source/statement/mathematical audit, with small exact-rational sanity checks; **not a fresh Lean build or an independent kernel replay**.

Source root: `source/entry005-actual-pyramid-20261007/`. References below are relative to `formal/Entry005/` unless another prefix is stated. No frozen source was edited; no cache was downloaded; no compilation was run. All nine primary reviewed files match their entries in the bundled `SOURCE_FILES_SHA256.json` at review time.

## Verdict

**PASS at the reviewed semantic/interface level.** The finite lifted normalization, actual entryA identity, common compact-limit passage, exact defect conversion, and final preservation of the owner's law and assignment tuple form a coherent proof chain. No circular geometric premise, replacement of the requested invariant by a surrogate, or merging of independently selected existential laws was found.

The final theorem assumes only a compact convex `K : Set (Space d)` containing the closed Euclidean unit ball and `[Nontrivial (Space d)]`. It constructs one compact probability witness `μ`, one strictly increasing subsequence `φ`, and retains the owner's already selected assignment tuple `w`. It does **not** assume the pyramid identity, a moment identity, positivity, the assignment bound, or the law's existence.

This verdict does not close the full maximum-simplex Main theorem, and it does not independently establish the package's compilation/axiom-audit claims. Those are distinct validation layers.

## 1. Literal mathematical objects

The invariant is geometric, not defined from moments:

- `Targets.lean:26–36`: `projectionVolumeSet` is intrinsic Lebesgue volume of the actual orthogonal projection; `projectionBodySet` is the actual intersection of its unit-direction support halfspaces; `projectionRatio K = |ΠK| / |K|^(d−1)`.
- `Targets.lean:38–46`: `pyramidSet K = conv((K,0) ∪ {(0,1)})`, `entryA K = (d/(d+1))^d R(PK)/R(K) − 1`, and `entryDefect K = entryA K − 1/(d+1)`.
- `DeterminantWitness.lean:15–25`: the lifted matrix has literal columns `(1,x)` and uses the varying point in column zero. `horizontalDeterminant` is the actual determinant with sampled points as columns. The paper writes height-last coordinates; absolute determinant removes the coordinate-permutation sign.
- `AnchorCoordinates.lean:11–17`: `anchorMatrix w` is definitionally the same lifted matrix with samples `w 0, w 1, …`; assignment uses its actual inverse and `largestCoordinate`.
- `ConeLawFinite.lean:20–27` and `FiniteHalfspaceConeLaw.lean:14–18`: finite law atoms are exactly `nᵢ/hᵢ`, weights are exactly `Ai hᵢ/(dV)`, and `Ai` is the actual intrinsic facet area, not an externally supplied abstract weight.
- `FamilyWitness.lean:110–114`: `determinantLawDefect (iidLaw ν d) ν id id` is the product-law absolute lifted integral minus the horizontal integral.

In this report, `A` and `B` always mean the first absolute determinant moments of the **same** `ν`; `D=B−A`; `e=entryDefect K`; `V=|K|`; `Q=|ΠK|`. They are explanatory abbreviations, not new formal definitions.

## 2. Finite lifted B normalization

### Genuine coordinate isometry

`PyramidLiftCoordinates.lean:11–42` constructs `Space (d+1) ≃ₗᵢ[ℝ] WithLp 2 (Space d × ℝ)` by sending height-first coordinates `(t,x)` to the literal product `(x,t)`. Both inverse identities, linearity and the L² norm identity are proved. This is not an arbitrary measurable map or an unproved Jacobian assertion.

`PyramidLiftCoordinates.lean:48–63` proves

`U((Ai hi/M) · (1,ni/hi)) = (Ai/M) · (ni,hi)`.

Only `hi ≠ 0` is needed for this algebraic leaf; `M ≠ 0` is deliberately unnecessary because Lean's real division is total. The geometric uses separately establish `M=dV>0`.

### Actual side zonotope and exact factorial

`PyramidLiftedMoment.lean:28–47` identifies the actual side zonotope with `(V/2) • U(lifted law zonotope)`. With `M=dV`, each resulting generator is `Ai/(2d) • (ni,hi)`, exactly the side projection-body generator.

`FiniteLawZonotopeMoment.lean:149–178` gives the literal finite iid identity

`|lifted law zonotope| = 2^(d+1)/(d+1)! · B`.

The tuples are iid ordered tuples; the inherited determinant tuple/injection identity accounts for repeats and the factorial. In `PyramidLiftedMoment.lean:51–89`, actual facet nonnegativity and mass `Σ Ai hi=dV` are supplied by the geometric owner. Euclidean isometry preserves volume and dilation contributes `(V/2)^(d+1)`. Thus the powers of two cancel exactly:

`|sideZ| = V^(d+1)/(d+1)! · B`.

No side-volume or lifted-moment identity is supplied as a hypothesis of this geometric theorem.

## 3. Finite entryA and defect algebra

`PyramidEntryDefect.lean:41–84` combines three independently proved statements:

1. `|Π(PK)| = |sideZ| + V/d^d · Q` (`PyramidProjectionVolume.lean:67–101`).
2. `|PK| = V/(d+1)`.
3. `A = d!/(dV)^d · Q` (actual finite horizontal first moment).

After substituting the actual lifted B formula, it unfolds the geometric `entryA` and `projectionRatio`, uses `finrank (Space d)=d` and `finrank` of the pyramid space `=d+1`, and obtains

`entryA K = B / ((d+1) A)`.

The cancellation is protected by proved `V>0`, `Q>0`, `d>0`, `d+1>0` and nonzero factorial. In particular, `PyramidEntryDefect.lean:9–36` proves projection-body volume positivity by scaling a genuine positive-radius ball into the body. There is no zero-denominator branch being misread as a geometric formula.

`PyramidMomentDefect.lean:9–44` proves `A≤B` by centered iid cancellation. It transports the literal `(d+1)`-sample law to `(iidLaw ν d).prod ν` and establishes integrability from coordinate first moments. It does not assume sampled determinants are nonzero.

For the actual finite law, `PyramidMomentDefect.lean:48–69` proves `A>0`, establishes probability and centeredness from facet geometry, and deduces `B>0`. Lines 71–107 then give

`(d+1) A e = B−A`, and `(B−A)/B = (d+1)e / (1+(d+1)e)`.

The finite proof rules out a zero rational denominator using `B>0`; the general iid proof below proves the stronger positivity of that denominator via `e≥0`.

## 4. Arbitrary normalized body: actual geometry and one common subsequence

### Pyramid approximation is proved

`PyramidContinuity.lean:27–43` proves the nontrivial containment

`L ⊆ aK`, `0∈K`, `a≥1` imply `P(L) ⊆ aP(K)`.

The apex case is explicitly handled using `a⁻¹ • apex ∈ P(K)`. This avoids incorrectly treating the canonical height-one pyramid operation as commuting exactly with dilation of its base.

`PyramidContinuity.lean:75–104` applies a genuine dilation sandwich to actual pyramid projection ratios and then `entryA`. Pyramid volume nonvanishing is deduced from the volume formula. Its use in `ActualPyramidMoment.lean:16–27` discharges every sandwich premise from the supporting-halfspace approximation, unit-ball inclusion, compactness, convexity and actual volume/ratio positivity.

### Both moments pass along the same compact law

`ActualPyramidMoment.lean:30–62` takes one supplied `μ`, one `φ`, and one convergence proof `hlim`. Both A and B convergence are derived from it.

- The test functions are actual absolute determinants (`CompactIidMomentContinuity.lean:127–155`).
- They are continuous on finite products of the compact Euclidean unit ball; the iid integral continuity theorems therefore apply (`:160–220`).
- Raw law recovery is exact, using the unit-ball support of each approximant and `compactBallLaw_raw_probability_pushforward` (`CompactBallConeLaw.lean:53–70`). The retraction's outside-ball fallback does not change these measures.
- Both limits are moments of `compactBallRawLaw μ`, literally `μ.map compactBallRaw` (`CompactBallConeLaw.lean:97–98`).

This is not an unjustified passage of an unbounded determinant test under weak convergence on all of Euclidean space.

`ActualPyramidMoment.lean:81–116` uses the **same** `φ` to pass the actual geometric `entryA` sequence and the finite identity `(d+1)A_k entryA(K_k)=B_k`. `StrictMono φ` is used to obtain `φ→∞`. Uniqueness of the real limit gives

`B(μ) = (d+1) A(μ) entryA K`.

The theorem at `:119–133` then divides by the **same law's** positive A, whose positivity is supplied at `:64–77` by the owner's actual horizontal formula and geometric volume positivity. It does not invoke a separate existential law theorem to obtain a compatible B.

### Existence wrappers genuinely discharge the limit premises

The conditional leaves explicitly take `μ, φ, StrictMono φ, hlim`. Their existence wrapper `actual_body_cone_law_with_pyramid_first_moment` (`ActualPyramidMoment.lean:138–160`) obtains the compact witness once from `actual_body_compact_cone_law_exists` and applies all horizontal, positivity and entryA leaves to those exact data.

The owner existence proof (`ActualBodyConeLaw.lean:24–57`) constructs the compact subsequence, proves centeredness by coordinate-integral limits, and brightness by actual finite brightness limits. No probability law, limiting identity, or centeredness premise is assumed at the final body interface.

## 5. General-body D, ratio, and same-witness assignment

### Honest conditional iid leaves

`ActualPyramidDefect.lean:9–21` proves the product-law definition is exactly `D=B−A`. This is an iid split/measure-preserving transport identity, not a redefinition of the defect.

The generic theorem `entryDefect_iid_moment_identity` (`:24–37`) **does** assume `hentry : entryA K=B/((d+1)A)` and `A>0`. This is appropriate for an algebra leaf. The nonnegativity and ratio leaves (`:39–75`) additionally assume coordinate integrability and centeredness. They derive `A≤B`, `e≥0`, `B>0` and `1+(d+1)e>0`, then prove

`D=(d+1)A e`, and `D/B=(d+1)e/(1+(d+1)e)`.

The actual wrapper `actual_body_cone_law_with_pyramid_defect` (`:81–108`) obtains one `ν` with its proved geometric `hentry`, and applies both algebra leaves to that same `ν`. Its literal conclusion exports the ratio equality. It does not promote a conditional algebra leaf to an unconditional geometric result without discharging its premise.

### New standalone assignment wrapper

`ActualPyramidAssignment.lean:41–56` obtains one `ν` from the pyramid first-moment wrapper, derives `B>0` for that law, invokes `unit_ball_first_moment_assignment` directly on it, and rewrites its `D/B` coefficient. No second independently selected law is used.

### Final owner-preserving joint wrapper

The decisive source is `ActualPyramidJointCone.lean:58–75`:

1. A single `obtain` from `actual_body_joint_polar_horizontal_assignment` returns `μ,φ,hφ,hlim,hraw,hball,hcenter,hbright,hboundary,hsupport,hhorizontal,hB,w,hdet,hw,ha,hm,hi,he`.
2. `hA` and `hentry` are computed from this same `μ,φ,hφ,hlim` (`:61–62`).
3. The returned existential tuple reuses all those witnesses, including the original `w,hdet,hw,ha,hm,hi` (`:64–66`).
4. Only the RHS of the original estimate `he` is rewritten, using the exact-law ratio lemma (`:67–74`).

The literal final bound is

`∫ ‖x − w(largestCoordinate(anchorCoordinates w x))‖ dν`

`≤ (d+1)(d+2) · ((d+1)e / (1+(d+1)e))`,

where throughout `ν=compactBallRawLaw μ`. The owner theorem itself (`ActualBodyJointConeInterface.lean:51–59`) had selected `w` by applying the assignment theorem to the very law constructed with polar support and horizontal A. Thus the full chain preserves the owner's common witness rather than merely reproducing an existential theorem of similar shape.

The final theorem explicitly exports A, `A>0`, entryA, D, `B>0`, polar support, weak limits, and assignment. It **does not add D/B as a separate conjunction**; that equality is proved and consumed in its proof for the exact same law. Consumers needing the separate equality can apply `entryDefect_iid_defect_ratio` using the exported `hball,hcenter,hA,hentry`. This is an interface observation, not a missing mathematical step.

## 6. Actual hypothesis inventory

These are grouped by identical assumption sets; they cover the 35 public theorem exports in the nine primary reviewed modules. The bundle's literal compiled-signature fields were consulted as secondary evidence, not treated as a fresh compilation.

| Group | Actual assumptions / exclusions |
|---|---|
| `pyramidLiftCoordinates`, its apply theorem | Every natural `d`; literal Euclidean spaces. No positive dimension or geometric assumption. |
| `pyramid_lifted_law_generator` | Arbitrary index type, scalars/coordinates, and each `hi≠0`. No `M≠0`, probability or facet assumption. |
| `pyramid_lifted_law_image` | Additionally finite labels. Still an algebraic image theorem. |
| `pyramid_side_zonotope_eq_scaled_lifted`; finite projection-volume positivity | Finite labels; `Space d` nontrivial; unit normals; strictly positive heights; compact halfspace intersection. Injectivity is not required for these two leaves. |
| Actual finite lifted B, entryA, A/B positivity, finite D and D/B | Same conditions **plus injective normals**. No unit-ball containment, probability, centering, facet mass, positive individual facet areas, or desired identity premise. Those needed facts are proved. Redundant distinct-normal facets may have zero area. |
| `centered_iid_lifted_moment_ge_horizontal` | Any `d`; an actual probability measure on raw coordinates; integrable coordinates; centeredness. No unit-ball or nondegeneracy premise. |
| Pyramid monotonicity/apex/zero/dilation leaves | Real inner-product ambient space. Dilation specifically needs `0∈K`, `a≥1`, `L⊆aK`; no body hypotheses are silently omitted. |
| Projection-negation / actual projection-body compactness | Finite-dimensional real inner-product space with measurable/Borel structures. Compactness of the defined projection body is proved for every K; no identity with an assumed abstract body. |
| Pyramid ratio / entryA continuity | Compact convex K and each Pₘ, `0∈K`, `|K|≠0`, nonnegative δₘ tending to zero, `K⊆Pₘ⊆(1+δₘ)K`. EntryA continuity additionally needs `R(K)≠0`. |
| `compact_normalized_projection_ratio_pos` | `Space d` nontrivial; compact K containing the closed unit ball. Convexity is not needed in this particular positivity leaf. |
| `halfspace_approximation_entryA_tendsto` | Nontrivial `Space d`; compact convex K containing the closed unit ball. No supplied moments/law. |
| `halfspace_approximation_iid_moments_tendsto` | Same K conditions, a supplied compact probability μ, a map φ and the displayed actual compact-law limit. Strict monotonicity is not needed for this test-integral leaf. |
| `actual_body_*_of_compact_limit` in `ActualPyramidMoment` | Same K conditions, supplied μ and φ, **StrictMono φ**, and the specific actual compact-law convergence premise. It is not an arbitrary weak limit of arbitrary measures. |
| `determinantLawDefect_iid_eq` | Any d and a probability measure. A measure-preserving equality of literal integrals; no integrability premise is concealed. Actual downstream applications also prove integrability. |
| Generic `entryDefect_iid_moment_identity` | K and a probability law; `A>0`; **explicit hentry**. It is not claimed as a standalone geometric theorem. |
| Generic iid nonnegativity and ratio | The preceding assumptions plus coordinate integrability and centeredness. No positivity of B or rational denominator is assumed. |
| All actual-body existence/defect/assignment wrappers, including final joint theorem | Only `K : Set (Space d)`, `[Nontrivial (Space d)]`, compactness, convexity, and `closedBall 0 1 ⊆ K`. The positive-dimensional requirement is real; d=0 is excluded. |

These are normalized-body theorems. They do not directly quantify over an arbitrary unnormalized convex body or every prescribed maximum simplex. Separate affine results do not automatically create that final integration.

## 7. Semantic boundaries and minor documentation observations

1. **No Main overclaim.** `Targets.lean:66–79` defines `sharpMainGoal` and `sharpLocalGoal`; they quantify over every maximum-volume inscribed simplex and require a centroid-based excess bound with exponent `1/(d−1)` and exact dimension constants. The final joint theorem proves a mean assignment error for support anchors in the polar law. It does not relate these anchors to an arbitrary prescribed maximum primal simplex, or prove the required geometric excess estimate. `truncationSharpnessGoal` (`:94–103`) also remains outside this increment. README and the technical report state this boundary honestly.

2. **Do not call the threshold gate open.** An inherited stale comment at `Targets.lean:81–82` calls the threshold gate unproved, but `ThresholdGate.lean:69–71` actually provides `thresholdGate : thresholdGateGoal`. `formal/controls/ThresholdChecks.lean:3` consumes it. This is a minor documentation inconsistency, not a blocker to the pyramid bridge. Main/local/sharpness still remain separate.

3. **Literal polar-boundary output.** `actualPolarBoundaryRaw K` is the concrete support-height level set `{x | h_K(toLp x)=1}` (`ActualBodyPolarBoundary.lean:50–55`). At the normalized compact convex inputs this is the usual polar-boundary condition. The wrapper exports that exact level-set carrying/support property; it does not separately export an equality with a `frontier (polar K)` expression. Owner support passage is for the fixed K, not changing approximation boundaries, and uses the same compact limit (`:68–165`).

4. **Constructed cone-law witness, not uniqueness.** The general law is an actual weak limit of actual finite supporting-halfspace cone laws. No uniqueness of this limit or a formal identification with a separately defined general-body surface-area-measure pushforward is asserted by the reviewed final signature. None is needed to preserve this witness or obtain the displayed identities and assignment. Do not strengthen the result to such a uniqueness/identification theorem in downstream descriptions.

5. **No exact equality classification follows merely from this interface.** At `e=0`, its cost bound becomes zero, but the full geometric equality classification and sharpness theorem require additional arguments. Likewise, the paper's `A≤1` and hence `D≤(d+1)e` are not explicit conjuncts of this final theorem; the audited bridge supplies the exact equality and ratio it uses.

6. The inspected primary files contain no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `extern`, `implemented_by`, or local `set_option` escape. Their 35 exports are recorded in bundled coverage as using only `Classical.choice`, `Quot.sound`, and `propext`. The latter is a **bundled claim inspected here**, not an independently replayed recursive axiom check.

## 8. Independent rational sanity checks

A short pure-Python `Fraction` calculation enumerated all ordered iid tuples of the actual cube cone law: the `2d` atoms `±eᵢ`, each with weight `1/(2d)`. It evaluated the literal horizontal and height-first lifted determinants, without using the Lean theorem under review.

| d | A | B | B/((d+1)A) | e | D/B |
|---|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 1/2 | 0 | 0 |
| 2 | 1/2 | 3/4 | 1/2 | 1/6 | 1/3 |
| 3 | 2/9 | 4/9 | 1/2 | 1/4 | 1/2 |

Both defect identities held exactly in every case. This catches simple dimension/factorial/height-coordinate mistakes, but is only a sanity test; it is not an alternative proof of the actual geometric formula or a kernel check.

## 9. Recommended parent conclusion

Accept the reviewed **same-witness pyramid/entryA/defect interface** at source-semantic level, subject to the separate independent compilation, transitive-axiom and provenance audits. Describe the result as the normalized actual-body cone-law bridge with its common assignment witness. Preserve the full Main, exact final stability integration, geometric equality and sharpness boundaries. No mathematical source change is requested by this review; the stale threshold comment and optional explicit joint ratio conjunct can be handled separately without altering the frozen review source.
