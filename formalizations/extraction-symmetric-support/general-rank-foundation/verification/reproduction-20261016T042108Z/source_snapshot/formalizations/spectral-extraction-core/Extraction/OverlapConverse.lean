import Extraction.KrausCompletion

open scoped BigOperators ComplexOrder
open Matrix
namespace Extraction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace square of every actual Hermitian matrix is nonnegative. -/
theorem hermitian_trace_square_nonneg (X : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    0 ≤ (X * X).trace.re := by
  have h : 0 ≤ (X * Xᴴ).trace.re :=
    (RCLike.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose X).trace_nonneg).1
  simpa only [hX.eq] using h

/-- The trace square is strictly positive for every nonzero Hermitian matrix. -/
theorem hermitian_trace_square_pos (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hne : X ≠ 0) : 0 < (X * X).trace.re := by
  have hs : (X * X).PosSemidef := by
    simpa only [hX.eq] using Matrix.posSemidef_self_mul_conjTranspose X
  apply positive_trace_re (X * X) hs
  intro hz
  have ht : (X * Xᴴ).trace = 0 := by rw [hX.eq, hz]; simp
  exact hne (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp ht)

/-- Hilbert--Schmidt Cauchy--Schwarz for actual complex Hermitian matrices. -/
theorem hermitian_trace_pairing_sq_le (X Y : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (X * Y).trace.re ^ 2 ≤ (X * X).trace.re * (Y * Y).trace.re := by
  by_cases hx : X = 0
  · simp [hx]
  have hr := hermitian_trace_square_pos X hX hx
  have hpoly (t : ℝ) :
      0 ≤ (Y * Y).trace.re - 2 * t * (X * Y).trace.re +
        t ^ 2 * (X * X).trace.re := by
    have hh : (Y - t • X).IsHermitian := by
      change (Y - t • X)ᴴ = Y - t • X
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        hY.eq, hX.eq, star_trivial]
    have ht := hermitian_trace_square_nonneg (Y - t • X) hh
    have he : ((Y - t • X) * (Y - t • X)).trace.re =
        (Y * Y).trace.re - 2 * t * (X * Y).trace.re +
          t ^ 2 * (X * X).trace.re := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.smul_re,
        smul_eq_mul, Matrix.trace_mul_comm Y X]
      ring
    rwa [he] at ht
  have hh := mul_nonneg hr.le
    (hpoly ((X * Y).trace.re / (X * X).trace.re))
  have he : (X * X).trace.re *
      ((Y * Y).trace.re -
        2 * ((X * Y).trace.re / (X * X).trace.re) * (X * Y).trace.re +
        ((X * Y).trace.re / (X * X).trace.re) ^ 2 * (X * X).trace.re) =
      (X * X).trace.re * (Y * Y).trace.re - (X * Y).trace.re ^ 2 := by
    field_simp
    ring
  rw [he] at hh
  linarith

variable {a b d κ : Type*} [Fintype a] [Fintype b] [Fintype d] [Fintype κ]
  [DecidableEq a] [DecidableEq b] [DecidableEq d]

/-- Actual Rains effects obey the one-shot purity envelope for every input,
including non-flat ensemble averages. -/
theorem rainsEffect_overlap_sq_le (K : ℕ)
    (X M : Matrix (a × b) (a × b) ℂ) (hX : X.IsHermitian)
    (hM : RainsEffect K M) :
    (M * X).trace.re ^ 2 ≤
      (X * X).trace.re * ((Fintype.card a * Fintype.card b : ℝ) / (K : ℝ)^2) := by
  rw [Matrix.trace_mul_comm M X]
  exact (hermitian_trace_pairing_sq_le X M hX hM.1.isHermitian).trans
    (mul_le_mul_of_nonneg_left (rainsEffect_trace_square_le K M hM)
      (hermitian_trace_square_nonneg X hX))

/-- The one-shot output overlap envelope starts from a physical Kraus channel,
its trace preservation, and its transpose-conjugate positivity. -/
theorem kraus_target_overlap_le [Nonempty d]
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1) (hpt : PTConjugatePositive A)
    (X : Matrix (a × b) (a × b) ℂ) (hX : X.IsHermitian) :
    (bellProjector (d := d) * krausApply A X).trace.re ≤
      Real.sqrt ((X * X).trace.re *
        ((Fintype.card a * Fintype.card b : ℝ) / (Fintype.card d : ℝ)^2)) := by
  rw [target_overlap_eq]
  exact Real.le_sqrt_of_sq_le
    (rainsEffect_overlap_sq_le _ X (targetEffect A) hX
      (targetEffect_rains A hcomplete hpt))

/-- The unit bound also follows from the actual trace-one PSD input semantics. -/
theorem kraus_target_overlap_le_one [Nonempty d]
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1) (hpt : PTConjugatePositive A)
    (X : Matrix (a × b) (a × b) ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1) :
    (bellProjector (d := d) * krausApply A X).trace.re ≤ 1 := by
  let M := targetEffect A
  have hM := targetEffect_rains A hcomplete hpt
  have h := positive_product_trace_re X (1 - M) hX.1 hM.2.1
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re, hX.2,
    Complex.one_re] at h
  rw [target_overlap_eq, Matrix.trace_mul_comm]
  change (X * M).trace.re ≤ 1
  linarith

/-- The relevant purity is invariant under the actual initial global unitary. -/
theorem trace_square_unitary (X : Matrix (a × b) (a × b) ℂ)
    (U : Matrix.unitaryGroup (a × b) ℂ) :
    ((U : Matrix (a × b) (a × b) ℂ) * X * (U : Matrix (a × b) (a × b) ℂ)ᴴ *
      ((U : Matrix (a × b) (a × b) ℂ) * X * (U : Matrix (a × b) (a × b) ℂ)ᴴ)).trace =
      (X * X).trace := by
  have hU : (U : Matrix (a × b) (a × b) ℂ)ᴴ * U = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  calc
    _ = ((U : Matrix (a × b) (a × b) ℂ) * (X * X) *
      (U : Matrix (a × b) (a × b) ℂ)ᴴ).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U : Matrix (a × b) (a × b) ℂ)ᴴ, hU, Matrix.one_mul]
    _ = _ := by rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

end Extraction
