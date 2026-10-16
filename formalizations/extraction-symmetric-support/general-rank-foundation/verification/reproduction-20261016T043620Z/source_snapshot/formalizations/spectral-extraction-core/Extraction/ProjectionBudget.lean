import Extraction.RainsBudget
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp

open scoped BigOperators ComplexOrder
open Matrix
namespace Extraction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real trace of a nonzero actual positive matrix is strictly positive. -/
theorem positive_trace_re (P : Matrix ι ι ℂ)
    (hP : P.PosSemidef) (hne : P ≠ 0) : 0 < P.trace.re := by
  obtain ⟨hre, him⟩ := RCLike.nonneg_iff.mp hP.trace_nonneg
  change 0 ≤ P.trace.re at hre
  change P.trace.im = 0 at him
  by_contra h
  have heq : P.trace = 0 := by
    apply Complex.ext
    · simpa only [Complex.zero_re] using le_antisymm (le_of_not_gt h) hre
    · simpa only [Complex.zero_im] using him
  exact hne (hP.trace_eq_zero_iff.mp heq)

/-- Matrix Cauchy--Schwarz against an actual orthogonal projection.
The quadratic polynomial comes from the positive square of M-tP. -/
theorem projection_trace_pairing_sq_le (P M : Matrix ι ι ℂ)
    (hP : P.PosSemidef) (hPP : P * P = P) (hne : P ≠ 0)
    (hM : M.IsHermitian) :
    (P * M).trace.re ^ 2 ≤ P.trace.re * (M * M).trace.re := by
  have hr := positive_trace_re P hP hne
  have hpoly (t : ℝ) :
      0 ≤ (M * M).trace.re - 2 * t * (P * M).trace.re + t ^ 2 * P.trace.re := by
    have hh : (M - t • P).IsHermitian := by
      change (M - t • P)ᴴ = M - t • P
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hM.eq,
        hP.isHermitian.eq, star_trivial]
    have hs : ((M - t • P) * (M - t • P)).PosSemidef := by
      simpa only [hh.eq] using Matrix.posSemidef_self_mul_conjTranspose (M - t • P)
    have ht : 0 ≤ ((M - t • P) * (M - t • P)).trace.re :=
      (RCLike.nonneg_iff.mp hs.trace_nonneg).1
    have he : ((M - t • P) * (M - t • P)).trace.re =
        (M * M).trace.re - 2 * t * (P * M).trace.re + t ^ 2 * P.trace.re := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.smul_re,
        smul_smul, smul_eq_mul, hPP, Matrix.trace_mul_comm M P]
      ring
    rwa [he] at ht
  have hh := mul_nonneg hr.le (hpoly ((P * M).trace.re / P.trace.re))
  have he : P.trace.re *
      ((M * M).trace.re - 2 * ((P * M).trace.re / P.trace.re) * (P * M).trace.re +
       ((P * M).trace.re / P.trace.re) ^ 2 * P.trace.re) =
      P.trace.re * (M * M).trace.re - (P * M).trace.re ^ 2 := by
    field_simp
    <;> ring
  rw [he] at hh
  linarith

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- The average overlap on a genuine subspace obeys the squared-dimension
Rains budget. This is uniform over the orientation of the projection. -/
theorem rainsEffect_projection_average_sq_le (K : ℕ)
    (P M : Matrix (a × b) (a × b) ℂ)
    (hP : P.PosSemidef) (hPP : P * P = P) (hne : P ≠ 0)
    (hM : RainsEffect K M) :
    ((P * M).trace.re / P.trace.re) ^ 2 ≤
      ((Fintype.card a * Fintype.card b : ℝ) / (K : ℝ)^2) / P.trace.re := by
  have hr := positive_trace_re P hP hne
  calc
    ((P * M).trace.re / P.trace.re) ^ 2 =
        (P * M).trace.re ^ 2 / P.trace.re ^ 2 := div_pow _ _ _
    _ ≤ (P.trace.re * (M * M).trace.re) / P.trace.re ^ 2 :=
      div_le_div_of_nonneg_right
        (projection_trace_pairing_sq_le P M hP hPP hne hM.1.isHermitian) (sq_nonneg _)
    _ = (M * M).trace.re / P.trace.re := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (rainsEffect_trace_square_le K M hM) hr.le

/-- A finite-dimensional one-shot subspace converse from actual PSD matrices. -/
theorem rainsEffect_projection_average_le (K : ℕ)
    (P M : Matrix (a × b) (a × b) ℂ)
    (hP : P.PosSemidef) (hPP : P * P = P) (hne : P ≠ 0)
    (hM : RainsEffect K M) :
    (P * M).trace.re / P.trace.re ≤
      Real.sqrt (((Fintype.card a * Fintype.card b : ℝ) / (K : ℝ)^2) / P.trace.re) :=
  Real.le_sqrt_of_sq_le (rainsEffect_projection_average_sq_le K P M hP hPP hne hM)

/-- The unit-fidelity bound also comes from actual order constraints. -/
theorem rainsEffect_projection_average_le_one (K : ℕ)
    (P M : Matrix (a × b) (a × b) ℂ)
    (hP : P.PosSemidef) (hne : P ≠ 0) (hM : RainsEffect K M) :
    (P * M).trace.re / P.trace.re ≤ 1 := by
  have hr := positive_trace_re P hP hne
  have h := positive_product_trace_re P (1 - M) hP hM.2.1
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at h
  exact (div_le_one hr).mpr (by linarith)

end Extraction
