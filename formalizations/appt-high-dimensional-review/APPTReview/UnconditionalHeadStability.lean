import APPTReview.PhysicalHeadStability

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Keep both nonnegative losses in the small-positive-outlier sector. -/
theorem entropyHead_small_joint_deficit {k : ℕ}
    {a : Fin (k+1) → ℝ} {β : Fin (k+2) → ℝ}
    (h : EntropyHeadConditions a β) (ha : a 0≤3/5) :
    (5/39:ℝ)*(a 0)^3+(2/5)*β 0≤2-entropyHead a β := by
  have hp:=entropyHead_prebound a β h.a_nonneg h.a_max h.beta_nonneg h.beta_antitone h.beta_le_one h.star_budget
  have hg:=entropy_positive_gap_bound (h.a_nonneg 0)
  have hg0:=entropyGap_nonneg (h.a_nonneg 0)
  have hd : 0<3*(a 0+2) := by have hh:=h.a_nonneg 0;positivity
  change (a 0)^3/(3*(a 0+2))≤entropyGap (a 0) at hg
  have hmul:=(div_le_iff₀ hd).mp hg
  have hden:=mul_le_mul_of_nonneg_left (show 3*(a 0+2)≤39/5 by linarith) hg0
  have hβ:=mul_nonneg (h.beta_nonneg 0) (show 0≤3/5-a 0 by linarith)
  nlinarith

/-- A moderate or large positive outlier causes a uniform, nonzero deficit. -/
theorem entropyHead_three_fifths_deficit {k : ℕ}
    {a : Fin (k+1) → ℝ} {β : Fin (k+2) → ℝ}
    (h : EntropyHeadConditions a β) (ha : 3/5≤a 0) :
    (37/1344:ℝ)≤2-entropyHead a β := by
  by_cases ha1 : 1≤a 0
  · exact entropyHead_large_outlier_deficit h ha1
  have ha1' : a 0≤1 := (lt_of_not_ge ha1).le
  have hp:=entropyHead_prebound a β h.a_nonneg h.a_max h.beta_nonneg h.beta_antitone h.beta_le_one h.star_budget
  have hg:=entropy_positive_gap_bound (h.a_nonneg 0)
  have hd : 0<3*(a 0+2) := by have hh:=h.a_nonneg 0;positivity
  have hpoly : 0≤(5*a 0-3)*(65*(a 0)^2+39*a 0+18) := by
    apply mul_nonneg (by linarith)
    positivity
  have hr : (9/325:ℝ)≤(a 0)^3/(3*(a 0+2)) := by
    apply (le_div_iff₀ hd).2
    nlinarith
  have hβ:=mul_nonpos_of_nonneg_of_nonpos (h.beta_nonneg 0) (show a 0-1≤0 by linarith)
  dsimp [entropyGap] at hp
  linarith

/-- Unconditional cubic stability from the head, a universal contrast cap and
trace normalization in the small-negative-outlier sector. -/
theorem entropyHead_unconditional_contrast {k : ℕ}
    {a : Fin (k+1) → ℝ} {β : Fin (k+2) → ℝ}
    (h : EntropyHeadConditions a β) (x : ℝ) (hx : 0≤x) (hcap : x≤2)
    (hflat : β 0≤1/2 → x≤2*(a 0+β 0)) :
    x^3≤300*(2-entropyHead a β) := by
  have hΔ:=entropyHead_deficit_nonneg h
  by_cases ha : 3/5≤a 0
  · have hd:=entropyHead_three_fifths_deficit h ha
    have hh:=pow_le_pow_left₀ hx hcap 3
    norm_num at hh
    linarith
  have ha' : a 0≤3/5 := (lt_of_not_ge ha).le
  have hd:=entropyHead_small_joint_deficit h ha'
  by_cases hb : β 0≤1/2
  · have hcube:=pow_le_pow_left₀ hx (hflat hb) 3
    have hsum : (a 0+β 0)^3≤4*((a 0)^3+(β 0)^3) := by
      have hp:=mul_nonneg (sq_nonneg (a 0-β 0)) (add_nonneg (h.a_nonneg 0) (h.beta_nonneg 0))
      nlinarith only [hp]
    have hb2 : (β 0)^2≤1/4 := by nlinarith [h.beta_nonneg 0]
    have hb3:=mul_le_mul_of_nonneg_right hb2 (h.beta_nonneg 0)
    have ha3:=pow_nonneg (h.a_nonneg 0) 3
    nlinarith only [hcube,hsum,hb3,ha3,hd,h.beta_nonneg 0]
  · have hb' : 1/2≤β 0 := (lt_of_not_ge hb).le
    have ha3:=pow_nonneg (h.a_nonneg 0) 3
    have hh:=pow_le_pow_left₀ hx hcap 3
    norm_num at hh
    nlinarith

end APPTReview
