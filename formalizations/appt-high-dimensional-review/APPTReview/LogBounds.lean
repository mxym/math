import APPTReview.SOS
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp

namespace APPTReview

/-- Exact derivative of the rational upper comparator for logarithm. -/
theorem log_ratio_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log t - 2 * (t - 1) / (t + 1))
      ((x - 1)^2 / (x * (x + 1)^2)) x := by
  have hxp : x + 1 ≠ 0 := by linarith
  have hd := (Real.hasDerivAt_log hx.ne').sub
    ((((hasDerivAt_id x).sub_const 1).const_mul 2).div
      ((hasDerivAt_id x).add_const 1) hxp)
  convert hd using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- The lower-side logarithm bound used in the entropy-head proof. -/
theorem log_le_twice_sub_div_add {x : ℝ} (hx : 0 < x) (h1 : x ≤ 1) :
    Real.log x ≤ 2 * (x - 1) / (x + 1) := by
  let g : ℝ → ℝ := fun t => Real.log t - 2 * (t - 1) / (t + 1)
  have hd : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt g
      ((t - 1)^2 / (t * (t + 1)^2)) t := by
    intro t ht
    exact log_ratio_derivative ht
  have hm : MonotoneOn g (Set.Ioi (0 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (by simpa using ht)).hasDerivWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa using ht
      positivity
  have he := hm hx (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) h1
  dsimp [g] at he
  simp only [Real.log_one, sub_self, mul_zero, zero_div] at he
  linarith

/-- Entropy deviation kernel, defined at the singular endpoint by Real.log 0 = 0. -/
noncomputable def entropyKernel (x : ℝ) : ℝ := (1 + x) * Real.log (1 + x) - x

/-- The nonlinear negative-side bound is valid even at a zero eigenvalue. -/
theorem entropy_negative_bound {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    entropyKernel (-y) ≤ y^2 / (2 - y) := by
  have hden : 0 < 2 - y := by linarith
  by_cases he : y = 1
  · subst y
    norm_num [entropyKernel]
  · have hp : 0 < 1 - y := sub_pos.mpr (lt_of_le_of_ne hy1 he)
    have hl := log_le_twice_sub_div_add hp (by linarith : 1 - y ≤ 1)
    have hc := mul_le_mul_of_nonneg_left hl hp.le
    apply (le_div_iff₀ hden).2
    dsimp [entropyKernel]
    have hid : (1 + -y) = 1 - y := by ring
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_right hc hden.le
    field_simp at hmul ⊢
    nlinarith


/-- Derivative comparison on the nonnegative half-line, including its endpoint. -/
theorem nonneg_of_nonneg_derivative {f f' : ℝ → ℝ}
    (hf : ∀ x : ℝ, 0 ≤ x → HasDerivAt f (f' x) x)
    (hd : ∀ x : ℝ, 0 ≤ x → 0 ≤ f' x) (h0 : 0 ≤ f 0) :
    ∀ x : ℝ, 0 ≤ x → 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro x hx
      exact (hf x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hp : 0 < x := by simpa using hx
      exact (hf x hp.le).hasDerivWithinAt
    · intro x hx
      have hp : 0 < x := by simpa using hx
      exact hd x hp.le
  intro x hx
  exact h0.trans (hm (by simp) hx hx)

private noncomputable def gapSlope (x : ℝ) : ℝ :=
  x - Real.log (1 + x) - 2*x^2*(x+3)/(3*(x+2)^2)

private theorem gapSlope_derivative {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt gapSlope (x^3*(x+4)/(3*(x+1)*(x+2)^3)) x := by
  have h1 : 1 + x ≠ 0 := by linarith
  have h2 : 3 * (x + 2)^2 ≠ 0 := by positivity
  have hl := (Real.hasDerivAt_log h1).comp x ((hasDerivAt_id x).const_add 1)
  have hn := (((hasDerivAt_id x).pow 2).const_mul 2).mul ((hasDerivAt_id x).add_const 3)
  have hd := (((hasDerivAt_id x).add_const 2).pow 2).const_mul 3
  have h := ((hasDerivAt_id x).sub hl).sub (hn.div hd h2)
  convert h using 1
  · rfl
  · dsimp
    field_simp
    ring

private theorem gapSlope_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gapSlope x := by
  apply nonneg_of_nonneg_derivative (f := gapSlope)
    (f' := fun t => t^3*(t+4)/(3*(t+1)*(t+2)^3))
  · intro t ht
    exact gapSlope_derivative ht
  · intro t ht
    positivity
  · norm_num [gapSlope]
  · exact hx

private noncomputable def positiveGap (x : ℝ) : ℝ :=
  x^2/2 - entropyKernel x - x^3/(3*(x+2))

private theorem positiveGap_derivative {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt positiveGap (gapSlope x) x := by
  have h1 : 1 + x ≠ 0 := by linarith
  have h2 : 3 * (x + 2) ≠ 0 := by positivity
  have hl := (Real.hasDerivAt_log h1).comp x ((hasDerivAt_id x).const_add 1)
  have hk := (((hasDerivAt_id x).const_add 1).mul hl).sub (hasDerivAt_id x)
  have hq := ((hasDerivAt_id x).pow 3).div
    (((hasDerivAt_id x).add_const 2).const_mul 3) h2
  have h := ((((hasDerivAt_id x).pow 2).div_const 2).sub hk).sub hq
  convert h using 1
  · rfl
  · dsimp [gapSlope]
    field_simp
    ring

/-- Nonlinear positive-side lower estimate used before the quartic SOS. -/
theorem entropy_positive_gap_bound {x : ℝ} (hx : 0 ≤ x) :
    x^3 / (3*(x+2)) ≤ x^2/2 - entropyKernel x := by
  have hh : 0 ≤ positiveGap x := by
    apply nonneg_of_nonneg_derivative (f := positiveGap) (f' := gapSlope)
    · intro t ht
      exact positiveGap_derivative ht
    · intro t ht
      exact gapSlope_nonneg ht
    · norm_num [positiveGap, entropyKernel]
    · exact hx
  dsimp [positiveGap] at hh
  linarith

/-- The strictly positive margin in the nonlinear entropy-head proof. -/
theorem entropy_head_outlier_margin {x : ℝ} (hx : 1 ≤ x) (h2 : x ≤ 2) :
    (1 - x^2/4)*(x-1) + 37/1344 ≤ x^2/2 - entropyKernel x := by
  have hgap := entropy_positive_gap_bound (by linarith : 0 ≤ x)
  have hpoly : (37/28 : ℝ) ≤ 3*x^4+7*x^3-18*x^2-12*x+24 := by
    have hs : 0 ≤ (x-1)^3 := pow_nonneg (sub_nonneg.mpr hx) _
    have h4 : 0 ≤ (x-1)^4 := pow_nonneg (sub_nonneg.mpr hx) _
    have he : 3*x^4+7*x^3-18*x^2-12*x+24 =
      3*(x-1)^4+19*(x-1)^3+21*((x-1)-5/14)^2+37/28 := by ring
    rw [he]
    nlinarith [sq_nonneg ((x-1)-5/14)]
  have hden : 0 < 12*(x+2) := by linarith
  have hid : x^3/(3*(x+2)) - (1-x^2/4)*(x-1) =
      (3*x^4+7*x^3-18*x^2-12*x+24)/(12*(x+2)) := by
    field_simp
    ring
  have hstrict : (37/1344 : ℝ) ≤ x^3/(3*(x+2)) - (1-x^2/4)*(x-1) := by
    rw [hid]
    apply (le_div_iff₀ hden).2
    nlinarith
  linarith

end APPTReview

