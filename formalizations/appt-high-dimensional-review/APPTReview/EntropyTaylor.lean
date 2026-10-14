import APPTReview.EntropyNormalization

namespace APPTReview

/-- Elementary first-derivative minimum principle, used on a closed interval
that stays strictly away from the singular logarithmic endpoint. -/
theorem interval_zero_minimum (δ : ℝ) (hδ : 0≤δ) (f df : ℝ → ℝ)
    (hd : ∀ x∈Set.Icc (-δ) δ,HasDerivAt f (df x) x) (hz : f 0=0)
    (hl : ∀ x∈Set.Icc (-δ) 0,df x≤0)
    (hr : ∀ x∈Set.Icc 0 δ,0≤df x)
    (x : ℝ) (hx : x∈Set.Icc (-δ) δ) : 0≤f x := by
  by_cases hp : 0≤x
  · have hm : MonotoneOn f (Set.Icc 0 δ) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 δ)
      · intro y hy;exact (hd y ⟨by linarith [hy.1],hy.2⟩).continuousAt.continuousWithinAt
      · intro y hy
        have hy' : y∈Set.Icc 0 δ := interior_subset hy
        exact (hd y ⟨by linarith [hy'.1],hy'.2⟩).hasDerivWithinAt
      · intro y hy;exact hr y (interior_subset hy)
    simpa only [hz] using hm ⟨le_rfl,hδ⟩ ⟨hp,hx.2⟩ hp
  · have hm : AntitoneOn f (Set.Icc (-δ) 0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (-δ) 0)
      · intro y hy;exact (hd y ⟨hy.1,by linarith [hy.2]⟩).continuousAt.continuousWithinAt
      · intro y hy
        have hy' : y∈Set.Icc (-δ) 0 := interior_subset hy
        exact (hd y ⟨hy'.1,by linarith [hy'.2]⟩).hasDerivWithinAt
      · intro y hy;exact hl y (interior_subset hy)
    have hn : x≤0 := le_of_not_ge hp
    simpa only [hz] using hm ⟨hx.1,hn⟩ ⟨by linarith,le_rfl⟩ hn

theorem entropyKernel_hasDerivAt (x : ℝ) (hx : -1<x) :
    HasDerivAt entropyKernel (Real.log (1+x)) x := by
  have hpos : 0<1+x := by linarith
  have ha := (hasDerivAt_id x).const_add 1
  have hl := (Real.hasDerivAt_log (ne_of_gt hpos)).comp x ha
  have hh := (ha.mul hl).sub (hasDerivAt_id x)
  convert hh using 1
  · rfl
  · dsimp;field_simp <;> ring

/-- Sharp local two-sided quadratic bounds with an explicit uniform error.
No Taylor formula is applied to an exceptional zero or fixed-height outlier. -/
theorem entropyKernel_quadratic_bounds (δ x : ℝ) (hδ : 0≤δ) (hδ1 : δ<1)
    (hx : |x|≤δ) :
    x^2/(2*(1+δ))≤entropyKernel x ∧ entropyKernel x≤x^2/(2*(1-δ)) := by
  have hdP : 0<1-δ := by linarith
  have hdQ : 0<1+δ := by linarith
  have hxi : x∈Set.Icc (-δ) δ := abs_le.mp hx
  have hlog (y : ℝ) (hy : y∈Set.Icc (-δ) δ) :
      y/(1+y)≤Real.log (1+y) ∧ Real.log (1+y)≤y := by
    have hp : 0<1+y := by linarith [hy.1]
    have h1 := Real.one_sub_inv_le_log_of_pos hp
    have he : 1-(1+y)⁻¹=y/(1+y) := by field_simp;ring
    rw [he] at h1
    exact ⟨h1,by simpa using Real.log_le_sub_one_of_pos hp⟩
  have hupper : 0≤x^2/(2*(1-δ))-entropyKernel x := by
    apply interval_zero_minimum δ hδ (fun y => y^2/(2*(1-δ))-entropyKernel y)
      (fun y => y/(1-δ)-Real.log (1+y))
    · intro y hy
      have hh := (((hasDerivAt_id y).pow 2).div_const (2*(1-δ))).sub
        (entropyKernel_hasDerivAt y (by linarith [hy.1]))
      convert hh using 1
      · rfl
      · dsimp;field_simp <;> ring
    · norm_num [entropyKernel]
    · intro y hy
      have hyl : y∈Set.Icc (-δ) δ := ⟨hy.1,hy.2.trans hδ⟩
      have hp : 0<1+y := by linarith [hy.1]
      have hc : y/(1-δ)≤y/(1+y) := (div_le_div_iff₀ hdP hp).2 (by
        have ht := mul_nonpos_of_nonpos_of_nonneg hy.2 (show 0≤y+δ by linarith [hy.1]);nlinarith)
      linarith [(hlog y hyl).1]
    · intro y hy
      have hyl : y∈Set.Icc (-δ) δ := ⟨by linarith [hy.1],hy.2⟩
      have hc : y≤y/(1-δ) := (le_div_iff₀ hdP).2 (by nlinarith [mul_nonneg hy.1 hδ])
      linarith [(hlog y hyl).2]
    · exact hxi
  have hlower : 0≤entropyKernel x-x^2/(2*(1+δ)) := by
    apply interval_zero_minimum δ hδ (fun y => entropyKernel y-y^2/(2*(1+δ)))
      (fun y => Real.log (1+y)-y/(1+δ))
    · intro y hy
      have hh := (entropyKernel_hasDerivAt y (by linarith [hy.1])).sub
        (((hasDerivAt_id y).pow 2).div_const (2*(1+δ)))
      convert hh using 1
      · rfl
      · dsimp;field_simp <;> ring
    · norm_num [entropyKernel]
    · intro y hy
      have hyl : y∈Set.Icc (-δ) δ := ⟨hy.1,hy.2.trans hδ⟩
      have hc : y≤y/(1+δ) := (le_div_iff₀ hdQ).2 (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hy.2 hδ])
      linarith [(hlog y hyl).2]
    · intro y hy
      have hyl : y∈Set.Icc (-δ) δ := ⟨by linarith [hy.1],hy.2⟩
      have hp : 0<1+y := by linarith [hy.1]
      have hc : y/(1+δ)≤y/(1+y) := (div_le_div_iff₀ hdQ hp).2 (by
        have ht := mul_nonneg hy.1 (sub_nonneg.mpr hy.2);nlinarith)
      linarith [(hlog y hyl).1]
    · exact hxi
  exact ⟨by linarith,by linarith⟩

/-- Remainder bounds preserve the better lower-side denominator. -/
theorem entropyRemainder_bounds (δ x : ℝ) (hδ : 0≤δ) (hδ1 : δ<1)
    (hx : |x|≤δ) :
    -(δ/(2*(1+δ)))*x^2≤entropyRemainder x ∧
      entropyRemainder x≤(δ/(2*(1-δ)))*x^2 := by
  have hh := entropyKernel_quadratic_bounds δ x hδ hδ1 hx
  have hp : 1+δ≠0 := by positivity
  have hn : 1-δ≠0 := by linarith
  have h1 : x^2/(2*(1+δ))-x^2/2=-(δ/(2*(1+δ)))*x^2 := by field_simp;ring
  have h2 : x^2/(2*(1-δ))-x^2/2=(δ/(2*(1-δ)))*x^2 := by field_simp;ring
  unfold entropyRemainder
  constructor <;> linarith

end APPTReview
