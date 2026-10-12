import GaussianFour.TraceSupport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The upper normal cone of the full positive trace-one slice, with its
complementary-slackness condition. Valid for every finite matrix size. -/
open Matrix
open scoped MatrixOrder
namespace GaussianFour
variable {n : Type*} [Fintype n] [DecidableEq n]

def IsTraceOneUpperNormal (Q A : Matrix n n ℝ) : Prop :=
  ∀ Y : Matrix n n ℝ, Y.PosSemidef → Y.trace = 1 → (A * (Y - Q)).trace ≤ 0

/-- Testing all positive trace-one matrices bounds every quadratic form. -/
theorem upperNormal_quadratic_bound {Q A : Matrix n n ℝ}
    (hnormal : IsTraceOneUpperNormal Q A) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ (A * Q).trace * (x ⬝ᵥ x) := by
  by_cases hx : x = 0
  · subst x; simp
  have hs : 0 < x ⬝ᵥ x := by
    simpa only [star_trivial] using (dotProduct_star_self_pos_iff.mpr hx)
  let Y : Matrix n n ℝ := (x ⬝ᵥ x)⁻¹ • vecMulVec x x
  have hY : Y.PosSemidef := by
    have h := posSemidef_vecMulVec_self_star x
    simp only [star_trivial] at h
    exact h.smul (inv_nonneg.mpr hs.le)
  have ht : Y.trace = 1 := by
    simp only [Y, trace_smul, trace_vecMulVec, smul_eq_mul]
    exact inv_mul_cancel₀ hs.ne'
  have h := hnormal Y hY ht
  rw [mul_sub, trace_sub] at h
  have hh : (A * Y).trace = (x ⬝ᵥ (A *ᵥ x)) / (x ⬝ᵥ x) := by
    simp only [Y, Matrix.mul_smul, trace_smul, mul_vecMulVec,
      trace_vecMulVec, smul_eq_mul, div_eq_mul_inv]
    rw [dotProduct_comm (A *ᵥ x) x, mul_comm]
  rw [hh] at h
  exact (div_le_iff₀ hs).mp (by linarith)

/-- A true upper normal has a positive scalar-identity slack matrix. -/
theorem upperNormal_slack_posSemidef {Q A : Matrix n n ℝ}
    (hA : A.IsHermitian) (hnormal : IsTraceOneUpperNormal Q A) :
    ((A * Q).trace • (1 : Matrix n n ℝ) - A).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
    ((isHermitian_one.smul (show IsSelfAdjoint (A * Q).trace from rfl)).sub hA)
  intro x
  simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]
  exact sub_nonneg.mpr (upperNormal_quadratic_bound hnormal x)

/-- Exact upper-normal characterization, including off-diagonal complementarity. -/
theorem upperNormal_iff_slack_and_product {Q A : Matrix n n ℝ}
    (hQ : Q.PosSemidef) (htrace : Q.trace = 1) (hA : A.IsHermitian) :
    IsTraceOneUpperNormal Q A ↔
      ((A * Q).trace • (1 : Matrix n n ℝ) - A).PosSemidef ∧
      A * Q = (A * Q).trace • Q := by
  constructor
  · intro hn
    have hs := upperNormal_slack_posSemidef hA hn
    refine ⟨hs, ?_⟩
    have hz : (((A * Q).trace • (1 : Matrix n n ℝ) - A) * Q).trace = 0 := by
      rw [sub_mul, smul_mul, one_mul, trace_sub, trace_smul, htrace]
      simp
    have hp := (trace_psd_mul_zero_iff hs hQ).mp hz
    rw [sub_mul, smul_mul, one_mul, sub_eq_zero] at hp
    exact hp.symm
  · rintro ⟨hs, hp⟩ Y hY htrY
    have h := trace_psd_mul_nonneg hs hY
    rw [sub_mul, smul_mul, one_mul, trace_sub, trace_smul, htrY] at h
    simp only [smul_eq_mul, mul_one] at h
    rw [mul_sub, trace_sub]
    linarith

/-- The multiplier is uniquely determined by the trace pairing. -/
theorem upperNormal_iff_exists_multiplier {Q A : Matrix n n ℝ}
    (hQ : Q.PosSemidef) (htrace : Q.trace = 1) (hA : A.IsHermitian) :
    IsTraceOneUpperNormal Q A ↔ ∃ μ : ℝ,
      (μ • (1 : Matrix n n ℝ) - A).PosSemidef ∧ A * Q = μ • Q := by
  rw [upperNormal_iff_slack_and_product hQ htrace hA]
  constructor
  · rintro ⟨hs, hp⟩; exact ⟨(A * Q).trace, hs, hp⟩
  · rintro ⟨μ, hs, hp⟩
    have he : (A * Q).trace = μ := by rw [hp, trace_smul, htrace]; simp
    rw [he]
    exact ⟨hs, hp⟩

end GaussianFour
