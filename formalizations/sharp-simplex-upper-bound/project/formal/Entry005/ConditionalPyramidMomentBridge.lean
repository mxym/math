import Entry005.ActualBodyJointConeInterface
import Entry005.PyramidApproximationLimits

/-! CONDITIONAL assembly only. The two finite actual-pyramid propositions below
are unproved geometry inputs, not axioms. No theorem in this module proves
these inputs, an unconditional B/entryDefect bridge, or MainTarget. -/

noncomputable section
open Metric MeasureTheory Module Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace Entry005

/-- UNPROVED finite geometry proposition: ordinary volume of the literal
pyramid of an actual compact full-dimensional finite halfspace body. -/
def FiniteActualPyramidVolumeFormula (d : ℕ) : Prop :=
  ∀ (_hd : 1 ≤ d) (ι : Type) [Fintype ι] (n : ι → Space d) (h : ι → ℝ),
    (∀ i, ‖n i‖ = 1) → (∀ i, 0 < h i) → Function.Injective n →
    IsCompact (finiteHalfspaceSet n h) →
    (volume (pyramidSet (finiteHalfspaceSet n h))).toReal =
      (volume (finiteHalfspaceSet n h)).toReal / ((d : ℝ) + 1)

/-- UNPROVED finite geometry proposition: actual pyramid projection-body
volume in terms of the actual facet cone law's first lifted determinant moment.
The actual body equality must be proved externally; weighted normals alone
do not discharge this proposition. -/
def FiniteActualPyramidProjectionFormula (d : ℕ) : Prop :=
  ∀ (_hd : 1 ≤ d) (ι : Type) [Fintype ι] (n : ι → Space d) (h : ι → ℝ),
    (∀ i, ‖n i‖ = 1) → (∀ i, 0 < h i) → Function.Injective n →
    IsCompact (finiteHalfspaceSet n h) →
    (volume (projectionBodySet (pyramidSet (finiteHalfspaceSet n h)))).toReal =
      (volume (finiteHalfspaceSet n h)).toReal ^ (d + 1) /
        ((d + 1).factorial : ℝ) *
          (∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det|
            ∂iidLaw (finiteHalfspaceConeLaw n h) (d + 1)) +
      (volume (finiteHalfspaceSet n h)).toReal / (d : ℝ) ^ d *
        (volume (projectionBodySet (finiteHalfspaceSet n h))).toReal

theorem pyramid_product_finrank {d : ℕ} :
    finrank ℝ (WithLp 2 (Space d × ℝ)) = d + 1 := by
  rw [(WithLp.linearEquiv 2 ℝ (Space d × ℝ)).finrank_eq, finrank_prod]
  simp [Space]

section ActualBody

variable {d : ℕ} [Nontrivial (Space d)]

private theorem positive_body_dimension : 1 ≤ d := by
  have hp : 0 < d := by simpa [Space] using (finrank_pos : 0 < finrank ℝ (Space d))
  omega

/-- CONDITIONAL specialization of the first missing finite geometric input
to the root's actual chosen supporting-halfspace approximation. -/
theorem conditional_halfspace_approximation_pyramid_volume_formula
    (hfinite : FiniteActualPyramidVolumeFormula d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    (volume (pyramidSet (halfspaceApproximationBody K hc hconv hb m))).toReal =
      (volume (halfspaceApproximationBody K hc hconv hb m)).toReal / ((d : ℝ) + 1) := by
  classical
  exact hfinite positive_body_dimension _ _ _
    (halfspace_approximation_normals_unit K hc hconv hb m)
    (halfspace_approximation_heights_pos K hc hconv hb m)
    (halfspace_approximation_normals_injective K hc hconv hb m)
    (halfspace_approximation_body_compact K hc hconv hb m)

/-- CONDITIONAL specialization of the second missing finite geometric input.
The law is the literal actual finiteHalfspaceConeLaw of the chosen body. -/
theorem conditional_halfspace_approximation_pyramid_projection_formula
    (hfinite : FiniteActualPyramidProjectionFormula d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) (m : ℕ) :
    (volume (projectionBodySet
      (pyramidSet (halfspaceApproximationBody K hc hconv hb m)))).toReal =
      (volume (halfspaceApproximationBody K hc hconv hb m)).toReal ^ (d + 1) /
        ((d + 1).factorial : ℝ) *
          (∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det|
            ∂iidLaw (halfspaceApproximationLaw K hc hconv hb m) (d + 1)) +
      (volume (halfspaceApproximationBody K hc hconv hb m)).toReal / (d : ℝ) ^ d *
        (volume (projectionBodySet (halfspaceApproximationBody K hc hconv hb m))).toReal := by
  classical
  exact hfinite positive_body_dimension _ _ _
    (halfspace_approximation_normals_unit K hc hconv hb m)
    (halfspace_approximation_heights_pos K hc hconv hb m)
    (halfspace_approximation_normals_injective K hc hconv hb m)
    (halfspace_approximation_body_compact K hc hconv hb m)

/-- CONDITIONAL finite-to-actual-body ordinary pyramid volume passage. -/
theorem conditional_actual_pyramid_volume_formula
    (hfinite : FiniteActualPyramidVolumeFormula d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) :
    (volume (pyramidSet K)).toReal = (volume K).toReal / ((d : ℝ) + 1) := by
  have ht := (halfspace_approximation_volume_tendsto K hc hconv hb).div_const ((d : ℝ) + 1)
  have hid (m : ℕ) := conditional_halfspace_approximation_pyramid_volume_formula
    hfinite K hc hconv hb m
  simp_rw [← hid] at ht
  exact tendsto_nhds_unique (halfspace_approximation_pyramid_volume_tendsto K hc hconv hb) ht

/-- The literal affine first iid moment converges along any retained actual
compact-law weak limit. This continuity step needs no missing geometry input. -/
theorem actual_body_affine_first_moment_tendsto_of_compact_limit
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability K hc hconv hb (φ k))) atTop (𝓝 μ)) :
    Tendsto (fun k => ∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det|
      ∂iidLaw (halfspaceApproximationLaw K hc hconv hb (φ k)) (d + 1)) atTop
      (𝓝 (∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1))) := by
  let ν := halfspaceApproximationProbability K hc hconv hb
  let x : C(CompactConeBall d, Fin d → ℝ) := ⟨compactBallRaw, continuous_compactBallRaw⟩
  have hball : ∀ m, ∀ᵐ z ∂(ν m : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 z‖ ≤ 1 :=
    halfspace_approximation_law_ae_unit_ball K hc hconv hb
  have hmap (k : ℕ) : (compactBallLaw (ν (φ k))).map x = ν (φ k) :=
    compactBallLaw_raw_probability_pushforward _ (hball (φ k))
  have ht := tendsto_lifted_mapped_iid_first_moment hlim x
  change Tendsto (fun k => ∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det|
    ∂iidLaw ((compactBallLaw (ν (φ k))).map x : Measure (Fin d → ℝ)) (d + 1)) atTop
    (𝓝 (∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det|
      ∂iidLaw (μ.map x : Measure (Fin d → ℝ)) (d + 1))) at ht
  simp_rw [hmap] at ht
  exact ht

/-- CONDITIONAL finite-to-actual-body projection-pyramid formula for the
same specified μ and φ, rather than a newly chosen law. -/
theorem conditional_actual_pyramid_projection_formula_of_compact_limit
    (hfinite : FiniteActualPyramidProjectionFormula d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability K hc hconv hb (φ k))) atTop (𝓝 μ)) :
    (volume (projectionBodySet (pyramidSet K))).toReal =
      (volume K).toReal ^ (d + 1) / ((d + 1).factorial : ℝ) *
        (∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det|
          ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) +
      (volume K).toReal / (d : ℝ) ^ d * (volume (projectionBodySet K)).toReal := by
  have hV := (halfspace_approximation_volume_tendsto K hc hconv hb).comp hφ.tendsto_atTop
  have hW := (halfspace_approximation_projection_body_volume_tendsto K hc hconv hb).comp
    hφ.tendsto_atTop
  have hB := actual_body_affine_first_moment_tendsto_of_compact_limit K hc hconv hb μ φ hlim
  have ht := (((hV.pow (d + 1)).div_const ((d + 1).factorial : ℝ)).mul hB).add
    ((hV.div_const ((d : ℝ) ^ d)).mul hW)
  have hid (k : ℕ) := conditional_halfspace_approximation_pyramid_projection_formula
    hfinite K hc hconv hb (φ k)
  simp only [Function.comp_def] at ht
  simp_rw [← hid] at ht
  exact tendsto_nhds_unique
    ((halfspace_approximation_pyramid_projection_body_volume_tendsto K hc hconv hb).comp
      hφ.tendsto_atTop) ht

end ActualBody

private theorem pyramid_ratio_scalar_reduction (d : ℕ) (hd : 1 ≤ d)
    (V W Z : ℝ) (hV : V ≠ 0) (hW : W ≠ 0) :
    ((d : ℝ) / ((d : ℝ) + 1)) ^ d * (Z / (V / ((d : ℝ) + 1)) ^ d) /
      (W / V ^ (d - 1)) = (d : ℝ) ^ d * Z / (V * W) := by
  have hm : (d : ℝ) + 1 ≠ 0 := by positivity
  have hpow : V ^ d = V ^ (d - 1) * V := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  simp only [div_pow]
  rw [hpow]
  field_simp [hV, hW, hm]

/-- Closed scalar algebra for the exact dimension and factorials. This does
not supply either missing actual geometric premise. -/
theorem pyramid_first_moment_entry_scalar_algebra (d : ℕ) (hd : 1 ≤ d)
    (V W B : ℝ) (hV : V ≠ 0) (hW : W ≠ 0) :
    B = ((d : ℝ) + 1) * ((d.factorial : ℝ) / ((d : ℝ) * V) ^ d * W) *
      (((d : ℝ) / ((d : ℝ) + 1)) ^ d *
        ((V ^ (d + 1) / ((d + 1).factorial : ℝ) * B + V / (d : ℝ) ^ d * W) /
          (V / ((d : ℝ) + 1)) ^ d) / (W / V ^ (d - 1)) - 1) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hm : (d : ℝ) + 1 ≠ 0 := by positivity
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [pyramid_ratio_scalar_reduction d hd V W _ hV hW]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, mul_pow]
  field_simp [hV, hW, hd0, hm, hf]
  ring

section ActualBodyAlgebra

variable {d : ℕ} [Nontrivial (Space d)]

/-- The actual horizontal first moment of any displayed actual compact-law
limit is strictly positive, with no finite pyramid premise. -/
theorem actual_body_horizontal_first_moment_pos_of_compact_limit
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability K hc hconv hb (φ k))) atTop (𝓝 μ)) :
    0 < ∫ base, |horizontalDeterminant base|
      ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d := by
  rw [actual_body_horizontal_first_moment_of_compact_limit K hc hconv hb μ φ hφ hlim]
  have hV := compact_body_volume_pos_of_unit_ball K hc hb
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Space d)
  have hW := normalized_projection_body_volume_pos K hc hb R hR.le hbound
  have hd : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by have := positive_body_dimension (d := d); omega)
  have hf : 0 < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  exact mul_pos (div_pos hf (pow_pos (mul_pos hd hV) d)) hW

/-- CONDITIONAL actual B=(d+1)A entryA for any retained actual μ/φ limit.
All volume and dimensional denominators are discharged geometrically. -/
theorem conditional_actual_body_affine_first_moment_entryA_of_compact_limit
    (hvolume : FiniteActualPyramidVolumeFormula d)
    (hprojection : FiniteActualPyramidProjectionFormula d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability K hc hconv hb (φ k))) atTop (𝓝 μ)) :
    (∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det|
      ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) =
      ((d : ℝ) + 1) *
        (∫ base, |horizontalDeterminant base|
          ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) * entryA K := by
  have hV := compact_body_volume_pos_of_unit_ball K hc hb
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Space d)
  have hW := normalized_projection_body_volume_pos K hc hb R hR.le hbound
  have hA := actual_body_horizontal_first_moment_of_compact_limit K hc hconv hb μ φ hφ hlim
  have hH := conditional_actual_pyramid_volume_formula hvolume K hc hconv hb
  have hZ := conditional_actual_pyramid_projection_formula_of_compact_limit
    hprojection K hc hconv hb μ φ hφ hlim
  have he : entryA K =
      (((d : ℝ) / ((d : ℝ) + 1)) ^ d *
        (((volume K).toReal ^ (d + 1) / ((d + 1).factorial : ℝ) *
          (∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det|
            ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) +
          (volume K).toReal / (d : ℝ) ^ d * (volume (projectionBodySet K)).toReal) /
          ((volume K).toReal / ((d : ℝ) + 1)) ^ d) /
        ((volume (projectionBodySet K)).toReal / (volume K).toReal ^ (d - 1)) - 1) := by
    unfold entryA projectionRatio
    simp only [finrank_euclideanSpace_fin, pyramid_product_finrank, Nat.add_sub_cancel]
    rw [hH, hZ]
  have hi := pyramid_first_moment_entry_scalar_algebra d positive_body_dimension
    (volume K).toReal (volume (projectionBodySet K)).toReal
    (∫ w : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix w).det|
      ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) hV.ne' hW.ne'
  rw [← hA, ← he] at hi
  exact hi

/-- CONDITIONAL exact D=(d+1)A entryDefect for that identical actual law.
No B/entryA or D/entryDefect identity is supplied as a premise. -/
theorem conditional_actual_body_determinant_defect_entryDefect_of_compact_limit
    (hvolume : FiniteActualPyramidVolumeFormula d)
    (hprojection : FiniteActualPyramidProjectionFormula d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K)
    (μ : ProbabilityMeasure (CompactConeBall d)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => compactBallLaw
      (halfspaceApproximationProbability K hc hconv hb (φ k))) atTop (𝓝 μ)) :
    determinantLawDefect (iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d)
      (compactBallRawLaw μ : Measure (Fin d → ℝ)) id id =
      ((d : ℝ) + 1) *
        (∫ base, |horizontalDeterminant base|
          ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) * entryDefect K := by
  have hB := conditional_actual_body_affine_first_moment_entryA_of_compact_limit
    hvolume hprojection K hc hconv hb μ φ hφ hlim
  have hm : (d : ℝ) + 1 ≠ 0 := by positivity
  dsimp only [determinantLawDefect, id_eq]
  rw [← iid_anchor_volume_integral_eq, hB]
  simp only [entryDefect, finrank_euclideanSpace_fin]
  field_simp [hm]

/-- CONDITIONAL joint bridge. One μ/φ is chosen once; its already proved
actual support, A, B positivity and assignment are retained while the two
explicit missing finite geometry inputs yield B/entryA and D/entryDefect.
This does not prove either geometry input or MainTarget. -/
theorem conditional_actual_body_joint_polar_horizontal_assignment_defect
    (hvolume : FiniteActualPyramidVolumeFormula d)
    (hprojection : FiniteActualPyramidProjectionFormula d)
    (K : Set (Space d)) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hb : closedBall (0 : Space d) 1 ⊆ K) :
    ∃ μ : ProbabilityMeasure (CompactConeBall d), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun k => compactBallLaw (halfspaceApproximationProbability K hc hconv hb (φ k)))
        atTop (𝓝 μ) ∧
      Tendsto (fun k => halfspaceApproximationProbability K hc hconv hb (φ k))
        atTop (𝓝 (compactBallRawLaw μ)) ∧
      (∀ᵐ x ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)), ‖WithLp.toLp 2 x‖ ≤ 1) ∧
      (∀ i, (∫ x, x i ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) = 0) ∧
      (∀ u : Space d, ‖u‖ = 1 →
        negativeIntegral (compactBallRawLaw μ : Measure (Fin d → ℝ))
          (fun x => dotProduct (fun j => u j) x) =
          projectionVolumeSet K u / ((finrank ℝ (Space d) : ℝ) * (volume K).toReal)) ∧
      (∀ᵐ x ∂(compactBallRawLaw μ : Measure (Fin d → ℝ)), x ∈ actualPolarBoundaryRaw K) ∧
      (compactBallRawLaw μ : Measure (Fin d → ℝ)).support ⊆ actualPolarBoundaryRaw K ∧
      (∫ base, |horizontalDeterminant base|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) =
        (d.factorial : ℝ) / ((d : ℝ) * (volume K).toReal) ^ d *
          (volume (projectionBodySet K)).toReal ∧
      ((∫ v : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix v).det|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) =
        ((d : ℝ) + 1) *
          (∫ base, |horizontalDeterminant base|
            ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) * entryA K) ∧
      (determinantLawDefect (iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d)
        (compactBallRawLaw μ : Measure (Fin d → ℝ)) id id =
        ((d : ℝ) + 1) *
          (∫ base, |horizontalDeterminant base|
            ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) * entryDefect K) ∧
      (0 < ∫ base, |horizontalDeterminant base|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d) ∧
      0 ≤ entryDefect K ∧
      (0 < ∫ v : Fin (d + 1) → Fin d → ℝ, |(anchorMatrix v).det|
        ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) ∧
      ∃ w : Fin (d + 1) → Fin d → ℝ, ∃ _hdet : (anchorMatrix w).det ≠ 0,
        (∀ i, w i ∈ (compactBallRawLaw μ : Measure (Fin d → ℝ)).support ∧ ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
        AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i)) ∧
        Measurable (fun x => largestCoordinate (anchorCoordinates w x)) ∧
        Integrable (fun x => ‖WithLp.toLp 2 x -
          WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖) (compactBallRawLaw μ : Measure (Fin d → ℝ)) ∧
        (∫ x, ‖WithLp.toLp 2 x - WithLp.toLp 2 (w (largestCoordinate (anchorCoordinates w x)))‖
          ∂(compactBallRawLaw μ : Measure (Fin d → ℝ))) ≤
          ((((d : ℝ) + 1) * ((d : ℝ) + 2)) *
            determinantLawDefect (iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) d)
              (compactBallRawLaw μ : Measure (Fin d → ℝ)) id id) /
            (∫ v : Fin (d + 1) → Fin d → ℝ,
              |(anchorMatrix v).det| ∂iidLaw (compactBallRawLaw μ : Measure (Fin d → ℝ)) (d + 1)) := by
  obtain ⟨μ, φ, hφ, hlim, hraw, hball, hcenter, hbrightness,
    hboundary, hsupport, hA, hBpos, hw⟩ :=
      actual_body_joint_polar_horizontal_assignment K hc hconv hb
  have hB := conditional_actual_body_affine_first_moment_entryA_of_compact_limit
    hvolume hprojection K hc hconv hb μ φ hφ hlim
  have hD := conditional_actual_body_determinant_defect_entryDefect_of_compact_limit
    hvolume hprojection K hc hconv hb μ φ hφ hlim
  have hApos := actual_body_horizontal_first_moment_pos_of_compact_limit K hc hconv hb μ φ hφ hlim
  have hDpos := unit_ball_determinant_law_defect_nonneg
    (compactBallRawLaw μ : Measure (Fin d → ℝ)) hball hcenter
  rw [hD] at hDpos
  have he : 0 ≤ entryDefect K :=
    (mul_nonneg_iff_of_pos_left (mul_pos (by positivity) hApos)).mp hDpos
  exact ⟨μ, φ, hφ, hlim, hraw, hball, hcenter, hbrightness,
    hboundary, hsupport, hA, hB, hD, hApos, he, hBpos, hw⟩

end ActualBodyAlgebra

end Entry005
