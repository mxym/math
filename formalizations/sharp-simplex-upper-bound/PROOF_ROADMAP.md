# Proof roadmap: same-witness radial scale to the prescribed simplex

This source map describes the unconditional upper Main. The [complete written argument](project/proofs/CompleteSharpMainRadialProof.txt) and [traditional mathematical review](audit/mathematical/REVIEW.md) include the full analytic detail. Historical pending-formalization statements in those documents are superseded by the composed-source kernel certificate, not silently edited into new claims.

## 1. Normalize the specified maximum S

[RegularSimplex](project/formal/Entry005/RegularSimplex.lean), [AffineNormalization](project/formal/Entry005/AffineNormalization.lean), [MaximumOuterBall](project/formal/Entry005/MaximumOuterBall.lean), and [EntryAffineInvariance](project/formal/Entry005/EntryAffineInvariance.lean) supply an invertible affine map f for the original S with f(centroid(S))=0 and

    unit ball ⊂ f(S) ⊂ f(K) ⊂ R0 ball.

Maximum-volume inscribed status, actual defect and actual centroid-based excess are transported by proved identities. The proof does not choose a replacement maximizing simplex. Work henceforth in these normalized coordinates.

## 2. Actual probability law, moments and a single assignment

[ActualPyramidJointCone](project/formal/Entry005/ActualPyramidJointCone.lean), [ActualBodyJointConeInterface](project/formal/Entry005/ActualBodyJointConeInterface.lean), [ActualPyramidAssignment](project/formal/Entry005/ActualPyramidAssignment.lean), and the inherited actual finite-halfspace, pyramid and determinant modules construct a joint compact-limit law μ, one strictly increasing subsequence φ, an affinely independent tuple w of d+1 actual support atoms, and the largest-coordinate assignment r for those anchors.

The raw law ν is centered, supported on the unit ball and on the actual polar support boundary. It gives the actual normalized brightness. Every selected atom satisfies h_K(w_i)=1. With e=entryDefect(K), t=(d+1)e and c=(d+1)(d+2), the actual determinant/pyramid identities yield the strong first-moment assignment bound

    ε = integral ||x−w_(r(x))|| dν(x) ≤ c·t/(1+t).

The final proof destructs the joint existence theorem once. All later scale, roundness and brightness consumers use the resulting identical μ, φ, ν, w and r. No independent limit law is identified without a proof.

## 3. Quantitative anchor roundness and the exact missing source

[ActualNormalizedDirectionalRoundness](project/formal/Entry005/ActualNormalizedDirectionalRoundness.lean) derives a directional negative-part lower bound 2b from actual projection and volume bounds. [SameWitnessOriginalQBudget](project/formal/Entry005/SameWitnessOriginalQBudget.lean) and the supplemented [SelectedAnchorHullRoundness](project/formal/Entry005/SelectedAnchorHullRoundness.lean) use ε ≤ h=Qt ≤ b to prove

    b ball ⊂ conv(w_0,…,w_d).

The missing-file repair contains three genuine proofs, not an assumed geometry interface. Its closest-point separation argument contradicts the directional lower bound with the pointwise assignment-error estimate; the unit-ball wrapper proves the needed integrability. This source was absent from the original 203-file patch, detected by recursive source completeness, and then supplied exactly before the successful independent audit.

## 4. Construct a genuine enclosing polar simplex

[PolarSimplexConstruction](project/formal/Entry005/PolarSimplexConstruction.lean) uses the actual affine barycentric coordinates α_i(x)=λ_i+ℓ_i·x of the supplied w. The b-ball inclusion gives λ_i≥b||ℓ_i||>0. Put q_i=−ℓ_i/λ_i. Barycentric identities give

    q_i·w_j=1−δ_ij/λ_i,
    β_i(y)=λ_i(1−w_i·y),
    Σ β_i(y)q_i=y.

Consequently P={y: w_i·y≤1 for all i}=conv(q_i), and β_i(q_j)=δ_ij proves genuine affine independence. Unit-ball containment, K⊂P, P⊂M ball and support equalities h_P(w_i)=1 follow. The normalized normals n_i=w_i/||w_i|| and heights H_i=1/||w_i|| are well-defined, unit/positive/injective and have exact facet atoms n_i/H_i=w_i. These are constructed conclusions, not Main premises.

Actual cone weights γ_i=area(F_i)H_i/(d volume(P)) are centered probabilities. Uniqueness of barycentric coordinates identifies them with λ_i. They are not silently equated with the assignment probabilities p_i. [CenteredAtomCorrection](project/formal/Entry005/CenteredAtomCorrection.lean) and [FiniteHalfspaceCenteredCorrection](project/formal/Entry005/FiniteHalfspaceCenteredCorrection.lean) prove Σ|p_i−λ_i|≤Mε and therefore the normalized brightness difference ≤(M+1)h/2.

## 5. Direct radial scale replaces the conditional Minkowski step

[FiniteRadialSupportScale](project/formal/Entry005/FiniteRadialSupportScale.lean) works with each actual supporting approximant Q_m and its actual radial facet cones C_i. Let s_i=h_P(n_i)/h_K(n_i). Then 1≤s_i≤M. A ray through any point of P exits Q_m on an active facet, proving the cover

    P ⊂ union_i s_i C_i

(up to the harmless origin). This does **not** assert Q_m⊂P. Actual measure subadditivity, homothety scaling and the radial cone mass identity yield

    volume(P)/volume(Q_m) ≤ Σ p_i s_i^d
      ≤ 1+d M^(d−1)(Σ p_i s_i−1).

The bounded continuous test h_P passes to the limit along the **same φ and μ** from step 2. Actual approximation-volume convergence gives, with I=integral h_P dν,

    α=volume(P)/volume(K) ≤ 1+d M^(d−1)(I−1).

Since h_P(w_i)=1 and h_P is M-Lipschitz, the same assignment proves I−1≤Mε. Thus α−1≤d M^d ε. This route needs neither a finite first-variation theorem nor a new surface-area measure identified with the compact law.

[OriginalRadialScale](project/formal/Entry005/OriginalRadialScale.lean) retains the stronger ε≤c t/(1+t) until proving c M^(d−1)≤Q for the **original** Q. It concludes

    α≤1+d MQt≤(1+MQt)^d.

Replacing the strong estimate prematurely by ε≤Qt would leave an unjustified M^(d−1) factor. The obsolete conditional finite-Minkowski modules remain as unchanged mathematical sources, but Main's actual declaration closure does not use `FiniteSupportMinkowskiObligation` or the old conditional cap theorem.

## 6. Actual brightness, original J/L and the cap exponent

[ActualFiniteEnclosingRadialCap](project/formal/Entry005/ActualFiniteEnclosingRadialCap.lean) and [ProjectionScaleAssembly](project/formal/Entry005/ProjectionScaleAssembly.lean) combine the corrected actual brightness law, the half-unit normalized ceiling and step 5's scale. With Mh≤1 they obtain the actual absolute projection deficits ≤Jh, using the unchanged J.

[ProjectionCap](project/formal/Entry005/ProjectionCap.lean) and the strong cap geometry turn those actual (d−1)-dimensional projection deficits into

    ρ=d_H(K,P) ≤ L(Jh)^(1/(d−1)).

The exponent comes from a genuine projected cap containing a (d−1)-dimensional ball/cube. It is not a full-dimensional volume estimate relabeled with a sharper exponent. The original threshold gives ρ≤1/(8Md).

## 7. Retain the original S and its centroid

[PrescribedSimplex](project/formal/Entry005/PrescribedSimplex.lean), [HausdorffRetention](project/formal/Entry005/HausdorffRetention.lean), [Mxym.StochasticRigidity](project/formal/Mxym/StochasticRigidity.lean), and [SharpMainRetentionAssembly](project/formal/Entry005/SharpMainRetentionAssembly.lean) use (1−ρ)P⊂K and maximality of the **given S** to obtain

    volume(S)/volume(P) ≥ (1−ρ)^d ≥ 1−dρ.

The actual barycentric matrix of S in P is column-stochastic with that determinant ratio. The proved near-permutation lemma matches its vertices to those of P within 2Mdρ. Hence

    K⊂P⊂S+2Mdρ ball⊂(1+2Mdρ)S.

This gives excess≤2Mdρ and leaves slack in the unchanged factor 4 of aSharp. The proof justifies the nonempty bounded-below admissible set for the literal sInf. Zero defect has zero error and requires no division by e.

## 8. Restore affine coordinates and close the global target

[SharpUpperMain](project/formal/Entry005/SharpUpperMain.lean) rewrites the normalized result via the actual defect and excess affine identities for the same f and same original S. [SharpConstantGates](project/formal/Entry005/SharpConstantGates.lean) joins the local estimate and coarse R0−1 bound, using proved nonnegativity. The final theorem is the unchanged universally quantified `sharpMainGoal` and `MainTarget`.

The independent literal controls expand maximality, centroid dilation, actual defect and constants, and reject a proposition-as-proof, a missing constant and an existential-simplex substitute. Separate empty-kernel programs replay the literal Main and every owned declaration. Those machine checks certify the Lean statements; the explanatory mathematical review checks the intended actual-body interpretation and warns that normalized brightness alone cannot imply scale.
