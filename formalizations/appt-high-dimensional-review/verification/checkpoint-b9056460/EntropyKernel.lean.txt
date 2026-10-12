import APPTReview.SOS
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp

open Set
namespace APPTReview

/-- A direct mean-value argument, used twice below. -/
theorem nonneg_of_nonneg_derivative {f f' : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → HasDerivAt f (f' x) x)
    (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) (h0 : 0 ≤ f 0)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y hy => (hf y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hf y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => hd y (interior_subset hy))
  exact h0.trans (hmono (by simp) hx hx)

/-- The exact nonlinear correction in the entropy proof. -/
noncomputable def entropyCorrection (x : ℝ) : ℝ :=
  x^2/2 + x - (1+x)*Real.log (1+x)

noncomputable def correctionGap (x : ℝ) : ℝ :=
  entropyCorrection x - x^3/(3*(x+2))

noncomputable def correctionSlope (x : ℝ) : ℝ :=
  x - Real.log (1+x) - (2*x^3+6*x^2)/(3*(x+2)^2)

theorem correctionSlope_derivative {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt correctionSlope (x^3*(x+4)/(3*(x+1)*(x+2)^3)) x := by
  have h1 : 1+x ≠ 0 := by linarith
  have h2 : x+2 ≠ 0 := by linarith
  have hi := hasDerivAt_id x
  have hl := (hi.const_add 1).log h1
  have hn := ((hi.pow 3).const_mul 2).add ((hi.pow 2).const_mul 6)
  have hd := ((hi.add_const 2).pow 2).const_mul 3
  have hh := (hi.sub hl).sub (hn.div hd (by change 3*(x+2)^2 ≠ 0; positivity))
  convert hh using 1
  · rfl
  · dsimp
    field_simp [h1, h2, show x+1 ≠ 0 by linarith]
    ring

theorem correctionSlope_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ correctionSlope x := by
  apply nonneg_of_nonneg_derivative
    (fun y hy => correctionSlope_derivative hy) _ _ hx
  · intro y hy
    positivity
  · norm_num [correctionSlope]

theorem correctionGap_derivative {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt correctionGap (correctionSlope x) x := by
  have h1 : 1+x ≠ 0 := by linarith
  have h2 : x+2 ≠ 0 := by linarith
  have hi := hasDerivAt_id x
  have hl := (hi.const_add 1).log h1
  have hp := (((hi.pow 2).div_const 2).add hi).sub ((hi.const_add 1).mul hl)
  have hq := (hi.pow 3).div ((hi.add_const 2).const_mul 3) (by positivity)
  convert hp.sub hq using 1
  · rfl
  · dsimp [correctionSlope]
    field_simp [h1, h2]
    ring

/-- The dimension-free analytic inequality (E13), proved by derivatives rather
than assuming the integral representation used by the working note. -/
theorem entropyCorrection_lower {x : ℝ} (hx : 0 ≤ x) :
    x^3/(3*(x+2)) ≤ entropyCorrection x := by
  have hg : 0 ≤ correctionGap x :=
    nonneg_of_nonneg_derivative
      (fun y hy => correctionGap_derivative hy)
      (fun y hy => correctionSlope_nonneg hy)
      (by norm_num [correctionGap, entropyCorrection]) hx
  exact sub_nonneg.mp hg

/-- The strict inequality required in the exceptional-head entropy argument. -/
theorem entropyCorrection_head_strict {x : ℝ} (hx : 1 ≤ x) :
    (1-x^2/4)*(x-1) < entropyCorrection x := by
  have hx0 : 0 ≤ x := by linarith
  have hd : 0 < 12*(x+2) := by positivity
  have hp := entropy_quartic_positive hx
  have hid : 12*(x+2)*(x^3/(3*(x+2))-(1-x^2/4)*(x-1)) =
      3*x^4+7*x^3-18*x^2-12*x+24 := by
    field_simp
    ring
  have hh : 0 < x^3/(3*(x+2))-(1-x^2/4)*(x-1) := by
    apply (mul_pos_iff_of_pos_left hd).mp
    rwa [hid]
  exact (sub_pos.mp hh).trans_le (entropyCorrection_lower hx0)
end APPTReview
