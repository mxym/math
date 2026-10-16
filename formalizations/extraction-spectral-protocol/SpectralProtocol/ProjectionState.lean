import SpectralProtocol.TransposeConvention

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual complex trace of a Hermitian idempotent equals its matrix rank. -/
theorem projection_trace_eq_rank (P : Matrix ι ι ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) : P.trace = (P.rank : ℂ) := by
  obtain ⟨κ, iκ, eκ, C, hC, hCP, hcard⟩ := Extraction.exists_projection_factor P hP hPP
  letI : Fintype κ := iκ
  letI : DecidableEq κ := eκ
  calc
    P.trace = (C * Cᴴ).trace := congrArg Matrix.trace hCP.symm
    _ = (Cᴴ * C).trace := Matrix.trace_mul_comm _ _
    _ = (Fintype.card κ : ℂ) := by rw [hC, Matrix.trace_one]
    _ = (P.rank : ℂ) := by rw [hcard]

/-- Idempotence and Hermiticity give positivity internally. -/
theorem projection_posSemidef (P : Matrix ι ι ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) : P.PosSemidef := by
  simpa only [hP.eq, hPP] using Matrix.posSemidef_self_mul_conjTranspose P

/-- The normalized projector, an actual matrix on the original input space. -/
noncomputable def projectionDensity (P : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((P.rank : ℝ)⁻¹) • P

theorem projectionDensity_density (P : Matrix ι ι ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) (hr : 0 < P.rank) :
    (projectionDensity P).PosSemidef ∧ (projectionDensity P).trace = 1 := by
  have hpos : 0 < (P.rank : ℝ) := by exact_mod_cast hr
  refine ⟨(projection_posSemidef P hP hPP).smul (inv_nonneg.mpr hpos.le), ?_⟩
  rw [projectionDensity, Matrix.trace_smul, projection_trace_eq_rank P hP hPP]
  apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im, ne_of_gt hpos]

theorem projectionDensity_supported (P : Matrix ι ι ℂ)
    (hPP : P * P = P) : P * projectionDensity P * P = projectionDensity P := by
  simp only [projectionDensity, Matrix.mul_smul, Matrix.smul_mul, hPP]

theorem projectionDensity_purity (P : Matrix ι ι ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) (hr : 0 < P.rank) :
    (projectionDensity P * projectionDensity P).trace.re = (P.rank : ℝ)⁻¹ := by
  have hpos : 0 < (P.rank : ℝ) := by exact_mod_cast hr
  rw [projectionDensity, Matrix.smul_mul, Matrix.mul_smul, hPP,
    Matrix.trace_smul, Matrix.trace_smul, projection_trace_eq_rank P hP hPP]
  simp [Complex.smul_re, ne_of_gt hpos]

variable {a b d κ : Type*} [Fintype a] [Fintype b] [Fintype d] [Fintype κ]
  [DecidableEq a] [DecidableEq b] [DecidableEq d] [Nonempty d]

/-- Exact extraction on every state in one actual support subspace forces the
squared-dimension budget, even with arbitrary original-space unitaries and
physical channels whose transpose conjugate is positive. -/
theorem exact_common_support_dimension_budget
    (P : Matrix (a × b) (a × b) ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) (hr : 0 < P.rank)
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1)
    (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (a × b) ℂ)
    (hexact : ∀ X : Matrix (a × b) (a × b) ℂ,
      APPT.Quantum.IsDensity X → P * X * P = X →
      (Extraction.bellProjector (d := d) * Extraction.krausApply A
        ((U : Matrix (a × b) (a × b) ℂ) * X *
          (U : Matrix (a × b) (a × b) ℂ)ᴴ)).trace.re = 1) :
    (P.rank : ℝ) * (Fintype.card d : ℝ)^2 ≤ Fintype.card a * Fintype.card b := by
  let X := projectionDensity P
  have hX := projectionDensity_density P hP hPP hr
  have he := hexact X hX (projectionDensity_supported P hPP)
  let Y := (U : Matrix (a × b) (a × b) ℂ) * X *
    (U : Matrix (a × b) (a × b) ℂ)ᴴ
  have hY : Y.IsHermitian := (hX.1.mul_mul_conjTranspose_same _).isHermitian
  have hb := Extraction.rainsEffect_overlap_sq_le (Fintype.card d) Y
    (Extraction.targetEffect A) hY (Extraction.targetEffect_rains A hcomplete hpt)
  rw [← Extraction.target_overlap_eq] at hb
  change (Extraction.bellProjector * Extraction.krausApply A Y).trace.re = 1 at he
  rw [he, one_pow] at hb
  change 1 ≤ (Y * Y).trace.re *
    ((Fintype.card a * Fintype.card b : ℝ) / (Fintype.card d : ℝ)^2) at hb
  rw [Extraction.trace_square_unitary X U, projectionDensity_purity P hP hPP hr] at hb
  have hrpos : 0 < (P.rank : ℝ) := by exact_mod_cast hr
  have hdpos : 0 < (Fintype.card d : ℝ) := by exact_mod_cast Fintype.card_pos
  have heq : (P.rank : ℝ)⁻¹ *
      ((Fintype.card a * Fintype.card b : ℝ) / (Fintype.card d : ℝ)^2) =
      (Fintype.card a * Fintype.card b : ℝ) /
        ((P.rank : ℝ) * (Fintype.card d : ℝ)^2) := by field_simp
  rw [heq] at hb
  have := (le_div_iff₀ (mul_pos hrpos (sq_pos_of_pos hdpos))).mp hb
  simpa only [one_mul] using this

end SpectralProtocol