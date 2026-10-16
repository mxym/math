import RankSupport.Invariance
import Extraction.ProjectionFactor

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionRankSupport

open SymmetricSupport ExtractionSpectrum

noncomputable section

theorem hermitian_projection_trace_eq_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (hP : P.IsHermitian) (hPP : P * P = P) :
    P.trace = (P.rank : ℂ) := by
  obtain ⟨κ, iκ, eκ, C, hC, hCP, hcard⟩ := Extraction.exists_projection_factor P hP hPP
  letI : Fintype κ := iκ
  letI : DecidableEq κ := eκ
  calc
    P.trace = (C * Cᴴ).trace := congrArg Matrix.trace hCP.symm
    _ = (Cᴴ * C).trace := Matrix.trace_mul_comm _ _
    _ = (Fintype.card κ : ℂ) := by rw [hC, Matrix.trace_one]
    _ = (P.rank : ℂ) := by rw [hcard]

def normalizedProjection {ι : Type*} [Fintype ι] (P : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((P.rank : ℝ)⁻¹) • P

theorem normalizedProjection_density {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (hP : P.IsHermitian) (hPP : P * P = P) (hr : 0 < P.rank) :
    (normalizedProjection P).PosSemidef ∧ (normalizedProjection P).trace = 1 := by
  have hpos : 0 < (P.rank : ℝ) := by exact_mod_cast hr
  have hPSD : P.PosSemidef := by
    simpa only [hP.eq, hPP] using Matrix.posSemidef_self_mul_conjTranspose P
  refine ⟨hPSD.smul (inv_nonneg.mpr hpos.le), ?_⟩
  rw [normalizedProjection, Matrix.trace_smul, hermitian_projection_trace_eq_rank P hP hPP]
  apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im, ne_of_gt hpos]

theorem normalizedProjection_rank_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) : (normalizedProjection P).rank ≤ P.rank := by
  apply Submodule.finrank_mono
  rintro v ⟨x, rfl⟩
  refine ⟨((P.rank : ℝ)⁻¹) • x, ?_⟩
  change P *ᵥ (((P.rank : ℝ)⁻¹) • x) = normalizedProjection P *ᵥ x
  simp only [normalizedProjection, Matrix.mulVec_smul, Matrix.smul_mulVec]

theorem tensorMatrix_real_smul (D k : ℕ) (c : ℝ) (M : Matrix (Fin D) (Fin D) ℂ) :
    tensorMatrix (c • M) k = c ^ k • tensorMatrix M k := by
  ext w v
  simp only [tensorMatrix, Matrix.smul_apply, RCLike.real_smul_eq_coe_mul,
    RCLike.ofReal_pow]
  rw [Finset.prod_mul_distrib]
  simp

/-- Span of ranges of actual normalized rank-bounded iid densities. -/
def densityTensorSpace (D k s : ℕ) : Submodule ℂ (Word D k → ℂ) :=
  Submodule.span ℂ {v | ∃ X : Matrix (Fin D) (Fin D) ℂ,
    (X.PosSemidef ∧ X.trace = 1) ∧ X.rank ≤ s ∧
      v ∈ LinearMap.range (tensorMatrix X k).mulVecLin}

theorem tensorMatrix_range_le_rankBudgetSpace (D k s : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.rank ≤ s) :
    LinearMap.range (tensorMatrix X k).mulVecLin ≤ rankBudgetSpace D k s := by
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro v ⟨w, rfl⟩
  exact tensorMatrix_col_mem_rankBudgetSpace D k s X hX w

/-- The intrinsic support is exactly the span of the actual density promise.
The proof constructs normalized finite-dimensional projections internally;
neither a Haar average nor a Schur decomposition is a caller premise. -/
theorem rankBudgetSpace_eq_densityTensorSpace (D k s : ℕ) (hk : 0 < k) :
    rankBudgetSpace D k s = densityTensorSpace D k s := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨z, hz, rfl⟩
    let S := Submodule.span ℂ (Set.range z)
    by_cases hS : Module.finrank ℂ S = 0
    · have hbot : S = ⊥ := Submodule.finrank_eq_zero.mp hS
      have hzi : z ⟨0, hk⟩ = 0 := by
        have hmem : z ⟨0, hk⟩ ∈ S := Submodule.subset_span ⟨⟨0, hk⟩, rfl⟩
        rwa [hbot, Submodule.mem_bot] at hmem
      have hv0 : productVector D k z = 0 := by
        ext w
        apply Finset.prod_eq_zero (Finset.mem_univ ⟨0, hk⟩)
        exact congrFun hzi (w ⟨0, hk⟩)
      rw [hv0]
      exact Submodule.zero_mem _
    · obtain ⟨Q, hQ, hQQ, hRange, hRank, hfix⟩ :=
        MatrixSubspace.exists_subspace_projection S
      have hr : 0 < Q.rank := by rw [hRank]; omega
      let X := normalizedProjection Q
      have hX : X.PosSemidef ∧ X.trace = 1 := normalizedProjection_density Q hQ hQQ hr
      have hXrank : X.rank ≤ s :=
        (normalizedProjection_rank_le Q).trans (hRank.trans_le hz)
      have hQz (i : Fin k) : Q *ᵥ z i = z i :=
        hfix (z i) (Submodule.subset_span ⟨i, rfl⟩)
      have hTQ : tensorMatrix Q k *ᵥ productVector D k z = productVector D k z := by
        rw [tensorMatrix_mulVec_productVector]
        congr 1
        funext i
        exact hQz i
      let c : ℝ := (Q.rank : ℝ)⁻¹
      have hc : c ^ k ≠ 0 := pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hr.ne'))
      apply Submodule.subset_span
      refine ⟨X, hX, hXrank, (c ^ k)⁻¹ • productVector D k z, ?_⟩
      change tensorMatrix X k *ᵥ ((c ^ k)⁻¹ • productVector D k z) = productVector D k z
      dsimp only [X, normalizedProjection]
      rw [tensorMatrix_real_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, hTQ,
        smul_smul]
      change ((c ^ k)⁻¹ * c ^ k) • productVector D k z = productVector D k z
      rw [inv_mul_cancel₀ hc, one_smul]
  · apply Submodule.span_le.mpr
    rintro v ⟨X, _, hRank, hv⟩
    exact tensorMatrix_range_le_rankBudgetSpace D k s X hRank hv

/-- Any actual linear map fixing every promised iid density fixes their whole
common support. This proves minimality of the constructed projector. -/
theorem fixes_densityTensor_mul_rankBudgetProjector (D k s : ℕ) (hk : 0 < k)
    (M : Matrix (Word D k) (Word D k) ℂ)
    (hfix : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      X.PosSemidef ∧ X.trace = 1 → X.rank ≤ s → M * tensorMatrix X k = tensorMatrix X k) :
    M * rankBudgetProjector D k s = rankBudgetProjector D k s := by
  have hle : rankBudgetSpace D k s ≤
      LinearMap.ker ((M.mulVecLin) - LinearMap.id) := by
    rw [rankBudgetSpace_eq_densityTensorSpace D k s hk]
    apply Submodule.span_le.mpr
    rintro v ⟨X, hX, hRank, x, rfl⟩
    change M *ᵥ (tensorMatrix X k *ᵥ x) - tensorMatrix X k *ᵥ x = 0
    rw [Matrix.mulVec_mulVec, hfix X hX hRank, sub_self]
  apply matrix_mul_eq_of_fixes_columns
  intro w
  have hw : (rankBudgetProjector D k s).col w ∈ rankBudgetSpace D k s := by
    rw [← rankBudgetProjector_range, Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨w, rfl⟩
  have h := hle hw
  change M *ᵥ (rankBudgetProjector D k s).col w - (rankBudgetProjector D k s).col w = 0 at h
  exact sub_eq_zero.mp h

end
end ExtractionRankSupport
