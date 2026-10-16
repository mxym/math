import RankSupport.ExactEffect

open scoped BigOperators ComplexOrder
open Matrix Module

namespace ExtractionRankSupport

open SymmetricSupport ExtractionSpectrum

noncomputable section

theorem isometry_factor_range {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (C : Matrix ι κ ℂ) (hC : Cᴴ * C = 1) :
    LinearMap.range C.mulVecLin = LinearMap.range (C * Cᴴ).mulVecLin := by
  apply le_antisymm
  · rintro v ⟨x, rfl⟩
    refine ⟨C *ᵥ x, ?_⟩
    change (C * Cᴴ) *ᵥ (C *ᵥ x) = C *ᵥ x
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hC, Matrix.mul_one]
  · rintro v ⟨x, rfl⟩
    exact ⟨Cᴴ *ᵥ x, Matrix.mulVec_mulVec _ _ _⟩

/-- Any actual factor family of dimension at most rank(X) can be placed in
the range of U X by one actual unitary U. Both isometries and their embedding
are constructed internally, including the zero-dimensional case. -/
theorem exists_unitary_matrix_range_factors (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (z : Fin k → Fin D → ℂ)
    (hz : Module.finrank ℂ (Submodule.span ℂ (Set.range z)) ≤ X.rank) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      ∀ i, z i ∈ LinearMap.range ((U : Matrix (Fin D) (Fin D) ℂ) * X).mulVecLin := by
  classical
  let S := Submodule.span ℂ (Set.range z)
  let R := LinearMap.range X.mulVecLin
  obtain ⟨Q, hQ, hQQ, hQR, hQRank, _⟩ := MatrixSubspace.exists_subspace_projection S
  obtain ⟨P, hP, hPP, hPR, hPRank, _⟩ := MatrixSubspace.exists_subspace_projection R
  obtain ⟨η, iη, eη, C, hC, hCQ, hCardC⟩ := Extraction.exists_projection_factor Q hQ hQQ
  letI : Fintype η := iη
  letI : DecidableEq η := eη
  obtain ⟨κ, iκ, eκ, F, hF, hFP, hCardF⟩ := Extraction.exists_projection_factor P hP hPP
  letI : Fintype κ := iκ
  letI : DecidableEq κ := eκ
  have hRangeC : LinearMap.range C.mulVecLin = S := by
    rw [isometry_factor_range C hC, hCQ, hQR]
  have hRangeF : LinearMap.range F.mulVecLin = R := by
    rw [isometry_factor_range F hF, hFP, hPR]
  have hcard : Fintype.card η ≤ Fintype.card κ := by
    rw [hCardC, hQRank, hCardF, hPRank]
    exact hz
  let G := Extraction.coordinateIsometry (Extraction.cardEmbedding hcard)
  have hG : Gᴴ * G = 1 := Extraction.coordinateIsometry_isometry _
  let T := F * G
  have hT : Tᴴ * T = 1 := Extraction.isometry_mul F G hF hG
  obtain ⟨U, hU⟩ := Extraction.exists_unitary_between_isometries T C hT hC
  refine ⟨U, ?_⟩
  intro i
  have hzi : z i ∈ LinearMap.range C.mulVecLin := by
    rw [hRangeC]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := hzi
  have hsource : T *ᵥ c ∈ R := by
    rw [← hRangeF]
    exact ⟨G *ᵥ c, Matrix.mulVec_mulVec _ _ _⟩
  obtain ⟨w, hw⟩ := hsource
  change X *ᵥ w = T *ᵥ c at hw
  refine ⟨w, ?_⟩
  change ((U : Matrix (Fin D) (Fin D) ℂ) * X) *ᵥ w = z i
  calc
    _ = (U : Matrix (Fin D) (Fin D) ℂ) *ᵥ (X *ᵥ w) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = (U : Matrix (Fin D) (Fin D) ℂ) *ᵥ (T *ᵥ c) := by rw [hw]
    _ = ((U : Matrix (Fin D) (Fin D) ℂ) * T) *ᵥ c := Matrix.mulVec_mulVec _ _ _
    _ = C *ᵥ c := by rw [hU]
    _ = z i := hc

def unitaryTensorOrbitSpace (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    Submodule ℂ (Word D k → ℂ) :=
  Submodule.span ℂ {v | ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
    v ∈ LinearMap.range (tensorMatrix
      ((U : Matrix (Fin D) (Fin D) ℂ) * X * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) k).mulVecLin}

/-- Every actual fixed matrix has exactly the rank-budget tensor-orbit
support. Positivity or flatness of its nonzero eigenvalues is not required. -/
theorem unitaryTensorOrbitSpace_eq_rankBudgetSpace (D k : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    unitaryTensorOrbitSpace D k X = rankBudgetSpace D k X.rank := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨U, hv⟩
    have hr : ((U : Matrix (Fin D) (Fin D) ℂ) * X *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ).rank ≤ X.rank :=
      (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    exact tensorMatrix_range_le_rankBudgetSpace D k X.rank _ hr hv
  · apply Submodule.span_le.mpr
    rintro v ⟨z, hz, rfl⟩
    obtain ⟨U, hU⟩ := exists_unitary_matrix_range_factors D k X z hz
    choose w hw using hU
    have hUU : (U : Matrix (Fin D) (Fin D) ℂ)ᴴ * U = 1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
    have hzi (i : Fin k) :
        ((U : Matrix (Fin D) (Fin D) ℂ) * X * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) *ᵥ
          ((U : Matrix (Fin D) (Fin D) ℂ) *ᵥ w i) = z i := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hUU, Matrix.mul_one]
      exact hw i
    apply Submodule.subset_span
    refine ⟨U, productVector D k (fun i => (U : Matrix (Fin D) (Fin D) ℂ) *ᵥ w i), ?_⟩
    change tensorMatrix _ k *ᵥ productVector D k _ = productVector D k z
    rw [tensorMatrix_mulVec_productVector]
    congr 1
    exact funext hzi

theorem fixed_density_unitary_conjugate_density (D : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (U : Matrix.unitaryGroup (Fin D) ℂ) :
    (((U : Matrix (Fin D) (Fin D) ℂ) * X * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ).PosSemidef ∧
      ((U : Matrix (Fin D) (Fin D) ℂ) * X * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ).trace = 1) := by
  refine ⟨hX.1.mul_mul_conjTranspose_same _, ?_⟩
  have hUU : (U : Matrix (Fin D) (Fin D) ℂ)ᴴ * U = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
  exact hX.2

/-- Perfect performance on the global-unitary orbit of one actual fixed
density forces identity on the same support as the full rank-budget class.
This is only an exact-performance statement, not a fixed-error profile. -/
theorem exact_fixed_density_orbit_effect_mul_rankBudgetProjector (D k : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (M : Matrix (Word D k) (Word D k) ℂ) (hM : (1-M).PosSemidef)
    (hfit : ∀ U : Matrix.unitaryGroup (Fin D) ℂ,
      (M * tensorMatrix ((U : Matrix (Fin D) (Fin D) ℂ) * X *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) k).trace.re = 1) :
    M * rankBudgetProjector D k X.rank = rankBudgetProjector D k X.rank := by
  have hle : rankBudgetSpace D k X.rank ≤ LinearMap.ker (M.mulVecLin - LinearMap.id) := by
    rw [← unitaryTensorOrbitSpace_eq_rankBudgetSpace D k X]
    apply Submodule.span_le.mpr
    rintro v ⟨U, x, rfl⟩
    let Y := (U : Matrix (Fin D) (Fin D) ℂ) * X * (U : Matrix (Fin D) (Fin D) ℂ)ᴴ
    have hY := tensorMatrix_density Y (fixed_density_unitary_conjugate_density D X hX U) k
    have hfix := exact_density_effect_fixes_density M (tensorMatrix Y k) hM hY (hfit U)
    change M *ᵥ (tensorMatrix Y k *ᵥ x) - tensorMatrix Y k *ᵥ x = 0
    rw [Matrix.mulVec_mulVec, hfix, sub_self]
  apply matrix_mul_eq_of_fixes_columns
  intro w
  have hw : (rankBudgetProjector D k X.rank).col w ∈ rankBudgetSpace D k X.rank := by
    rw [← rankBudgetProjector_range, Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨w, rfl⟩
  have h := hle hw
  change M *ᵥ (rankBudgetProjector D k X.rank).col w - (rankBudgetProjector D k X.rank).col w = 0 at h
  exact sub_eq_zero.mp h

end
end ExtractionRankSupport
