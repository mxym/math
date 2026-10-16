import RankSupport.FixedSpectrumOrbit
import RankSupport.ExponentialLower

open scoped BigOperators ComplexOrder
open Matrix Module

namespace ExtractionRankSupport

open SymmetricSupport ExtractionSpectrum

noncomputable section

/-- An actual one-copy projection onto the first s original coordinates. -/
def coordinateRankProjection (D s : ℕ) (hsD : s ≤ D) : Matrix (Fin D) (Fin D) ℂ :=
  let C := Extraction.coordinateIsometry (coordinateLetterEmbedding hsD)
  C * Cᴴ

theorem coordinateRankProjection_isHermitian (D s : ℕ) (hsD : s ≤ D) :
    (coordinateRankProjection D s hsD).IsHermitian := by
  change (_ * _)ᴴ = _
  simp only [coordinateRankProjection, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

theorem coordinateRankProjection_idempotent (D s : ℕ) (hsD : s ≤ D) :
    coordinateRankProjection D s hsD * coordinateRankProjection D s hsD =
      coordinateRankProjection D s hsD := by
  let C := Extraction.coordinateIsometry (coordinateLetterEmbedding hsD)
  have hC : Cᴴ * C = 1 := Extraction.coordinateIsometry_isometry _
  change (C * Cᴴ) * (C * Cᴴ) = C * Cᴴ
  calc
    _ = C * (Cᴴ * C) * Cᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hC, Matrix.mul_one]

theorem coordinateRankProjection_rank (D s : ℕ) (hsD : s ≤ D) :
    (coordinateRankProjection D s hsD).rank = s := by
  let C := Extraction.coordinateIsometry (coordinateLetterEmbedding hsD)
  let P := coordinateRankProjection D s hsD
  have hC : Cᴴ * C = 1 := Extraction.coordinateIsometry_isometry _
  have hCPC : Cᴴ * P * C = 1 := by
    calc
      _ = (Cᴴ * C) * (Cᴴ * C) := by
        dsimp only [P, coordinateRankProjection, C]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hC, Matrix.one_mul]
  apply le_antisymm
  · calc
      _ ≤ C.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin s) := Matrix.rank_le_card_width _
      _ = s := Fintype.card_fin s
  · have h := (Matrix.rank_mul_le_left (Cᴴ * P) C).trans (Matrix.rank_mul_le_right Cᴴ P)
    rw [hCPC, Matrix.rank_one, Fintype.card_fin] at h
    exact h

theorem matrix_rank_real_smul_le {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix ι κ ℂ) (c : ℝ) : (c • M).rank ≤ M.rank := by
  apply Submodule.finrank_mono
  rintro v ⟨x, rfl⟩
  refine ⟨c • x, ?_⟩
  change M *ᵥ (c • x) = (c • M) *ᵥ x
  simp only [Matrix.mulVec_smul, Matrix.smul_mulVec]

/-- A concrete original-coordinate density, with no spectrum or rank
certificate supplied by the caller. -/
def flatCoordinateDensity (D s : ℕ) (hsD : s ≤ D) : Matrix (Fin D) (Fin D) ℂ :=
  normalizedProjection (coordinateRankProjection D s hsD)

theorem flatCoordinateDensity_density (D s : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    (flatCoordinateDensity D s hsD).PosSemidef ∧ (flatCoordinateDensity D s hsD).trace = 1 := by
  apply normalizedProjection_density _
    (coordinateRankProjection_isHermitian D s hsD) (coordinateRankProjection_idempotent D s hsD)
  rwa [coordinateRankProjection_rank]

theorem flatCoordinateDensity_rank (D s : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    (flatCoordinateDensity D s hsD).rank = s := by
  let P := coordinateRankProjection D s hsD
  let X := flatCoordinateDensity D s hsD
  have hP : P.rank = s := coordinateRankProjection_rank D s hsD
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hscale : (s : ℝ) • X = P := by
    dsimp only [X, flatCoordinateDensity, normalizedProjection]
    rw [hP, smul_smul, mul_inv_cancel₀ hsR, one_smul]
  apply le_antisymm
  · exact (normalizedProjection_rank_le P).trans_eq hP
  · calc
      s = P.rank := hP.symm
      _ = ((s : ℝ) • X).rank := congrArg Matrix.rank hscale.symm
      _ ≤ X.rank := matrix_rank_real_smul_le X _

theorem normalizedProjection_trace_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (hP : P.IsHermitian) (hPP : P * P = P) :
    (normalizedProjection P * normalizedProjection P).trace = (P.rank : ℂ)⁻¹ := by
  simp only [normalizedProjection, Matrix.smul_mul, Matrix.mul_smul, hPP,
    Matrix.trace_smul, hermitian_projection_trace_eq_rank P hP hPP]
  simp only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv, RCLike.ofReal_natCast]
  by_cases hr : P.rank = 0
  · simp [hr]
  · have hrC : (P.rank : ℂ) ≠ 0 := by exact_mod_cast hr
    field_simp

theorem actual_tensorMatrix_trace (D k : ℕ) (M : Matrix (Fin D) (Fin D) ℂ) :
    (tensorMatrix M k).trace = M.trace ^ k := by
  simp only [Matrix.trace, Matrix.diag, tensorMatrix]
  exact (Fintype.sum_pow (fun i : Fin D => M i i) k).symm

theorem flatCoordinateDensity_tensor_density (D s : ℕ) (hs : 0 < s) (hsD : s ≤ D) (k : ℕ) :
    (tensorMatrix (flatCoordinateDensity D s hsD) k).PosSemidef ∧
      (tensorMatrix (flatCoordinateDensity D s hsD) k).trace = 1 :=
  tensorMatrix_density _ (flatCoordinateDensity_density D s hs hsD) k

/-- Exact actual tensor purity s^(-k), including blocklength zero. -/
theorem flatCoordinateDensity_tensor_purity (D s : ℕ) (hsD : s ≤ D) (k : ℕ) :
    (tensorMatrix (flatCoordinateDensity D s hsD) k *
      tensorMatrix (flatCoordinateDensity D s hsD) k).trace.re = ((s : ℝ)^k)⁻¹ := by
  rw [← tensorMatrix_mul, actual_tensorMatrix_trace]
  rw [flatCoordinateDensity, normalizedProjection_trace_square _
    (coordinateRankProjection_isHermitian D s hsD) (coordinateRankProjection_idempotent D s hsD),
    coordinateRankProjection_rank, inv_pow]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    Complex.ofReal_re]

/-- The actual flat rank-s witness and all its tensor purities are constructed
on the original coordinate space, without a Haar averaging premise. -/
theorem exists_flat_rank_density (D s : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ, (X.PosSemidef ∧ X.trace = 1) ∧ X.rank = s ∧
      ∀ k, (tensorMatrix X k * tensorMatrix X k).trace.re = ((s : ℝ)^k)⁻¹ :=
  ⟨flatCoordinateDensity D s hsD, flatCoordinateDensity_density D s hs hsD,
    flatCoordinateDensity_rank D s hs hsD, flatCoordinateDensity_tensor_purity D s hsD⟩

end
end ExtractionRankSupport
