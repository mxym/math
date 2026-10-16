import RankSupport.MinimalSupport
import Mathlib.Analysis.Matrix.Order

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ExtractionRankSupport

open SymmetricSupport ExtractionSpectrum

noncomputable section

/-- Vanishing trace pairing of two actual PSD matrices forces their product
to vanish. The factorization and square-norm argument are internal. -/
theorem psd_mul_eq_zero_of_trace_re_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A X : Matrix ι ι ℂ) (hA : A.PosSemidef) (hX : X.PosSemidef)
    (ht : (A * X).trace.re = 0) : A * X = 0 := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  simp only [Matrix.star_eq_conjTranspose] at hC hB
  let Z := C * Bᴴ
  have he : (A * X).trace = (Zᴴ * Z).trace := by
    rw [hC, hB]
    dsimp only [Z]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = (B * (Cᴴ * C) * Bᴴ).trace := by
        rw [Matrix.trace_mul_cycle']
        simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self Z
  have him : (Zᴴ * Z).trace.im = 0 := (RCLike.nonneg_iff.mp hPSD.trace_nonneg).2
  have hzero : (Zᴴ * Z).trace = 0 := by
    apply Complex.ext
    · rw [← he]
      exact ht
    · exact him
  have hZ : Z = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hzero
  rw [hC, hB]
  calc
    _ = Cᴴ * Z * B := by dsimp only [Z]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]

theorem exact_density_effect_fixes_density {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M X : Matrix ι ι ℂ) (hM : (1 - M).PosSemidef)
    (hX : X.PosSemidef ∧ X.trace = 1) (hfit : (M * X).trace.re = 1) :
    M * X = X := by
  have ht : ((1 - M) * X).trace.re = 0 := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
      hX.2, Complex.one_re, hfit, sub_self]
  have h := psd_mul_eq_zero_of_trace_re_eq_zero (1 - M) X hM hX.1 ht
  rw [Matrix.sub_mul, Matrix.one_mul] at h
  exact (sub_eq_zero.mp h).symm

/-- Perfect expectation on the actual normalized rank-s iid promise forces
identity on the internally constructed minimal common support. -/
theorem exact_rankBounded_iid_effect_mul_rankBudgetProjector (D k s : ℕ) (hk : 0 < k)
    (M : Matrix (Word D k) (Word D k) ℂ) (hM : (1 - M).PosSemidef)
    (hfit : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      X.PosSemidef ∧ X.trace = 1 → X.rank ≤ s → (M * tensorMatrix X k).trace.re = 1) :
    M * rankBudgetProjector D k s = rankBudgetProjector D k s := by
  apply fixes_densityTensor_mul_rankBudgetProjector D k s hk M
  intro X hX hRank
  exact exact_density_effect_fixes_density M (tensorMatrix X k) hM
    (tensorMatrix_density X hX k) (hfit X hX hRank)

end
end ExtractionRankSupport
