import APPTReview.PlateauApproximation

open scoped BigOperators
namespace APPTReview

/-- Purity of a boundary mixture of two uniform-prefix spectra.
Here the longer support has length L+s and the cutting functional has
positive numerator h on the prefix of length i. -/
noncomputable def cutEdgePurity (L h i s : ℝ) : ℝ :=
  (h^2*(L+s)+2*i*h*s+i*s^2)/(h*L+(h+i)*s)^2

/-- A rational change of variable turns the edge objective into a quadratic. -/
theorem cutEdgePurity_quadratic (L h i s : ℝ) (hL : L≠0)
    (hden : h*L+(h+i)*s≠0) :
    cutEdgePurity L h i s = 1/L-(h/L)*(s/(h*L+(h+i)*s))+
      (i*(L-h-i)/L)*(s/(h*L+(h+i)*s))^2 := by
  unfold cutEdgePurity
  generalize hz : h*L+(h+i)*s = z at *
  field_simp
  rw [← hz]
  ring

/-- A quadratic with nonnegative leading coefficient has no larger value
between two endpoints. This lemma retains the exact affine chord inequality. -/
theorem quadratic_le_endpoint_max (a b c x y : ℝ) (ha : 0≤a)
    (hx : 0≤x) (hxy : x≤y) (hy : 0<y) :
    a*x^2+b*x+c ≤ max c (a*y^2+b*y+c) := by
  let C := max c (a*y^2+b*y+c)
  have hc : c≤C := le_max_left _ _
  have hf : a*y^2+b*y+c≤C := le_max_right _ _
  have h1 := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hxy)
  have h2 := mul_le_mul_of_nonneg_left hf hx
  have h3 : 0≤a*x*y*(y-x) := by positivity
  have hchord : y*(a*x^2+b*x+c) ≤ (y-x)*c+x*(a*y^2+b*y+c) := by nlinarith
  have htotal : y*(a*x^2+b*x+c) ≤ y*C := by nlinarith
  exact (mul_le_mul_iff_right₀ hy).mp htotal

/-- Every shortened-support edge is bounded by the zero-length and
full-support endpoints. The hypotheses cover all three prefix regions. -/
theorem cutEdgePurity_le_endpoints (L h i s m : ℝ)
    (hL : 0<L) (hh : 0<h) (hi : 0 ≤ i) (hroom : h+i ≤ L)
    (hs : 0≤s) (hsm : s≤m) (hm : 0<m) :
    cutEdgePurity L h i s ≤ max (1/L) (cutEdgePurity L h i m) := by
  let d := h*L+(h+i)*s
  let e := h*L+(h+i)*m
  have hd : 0<d := by dsimp [d]; positivity
  have he : 0<e := by dsimp [e]; positivity
  have hx : 0≤s/d := div_nonneg hs hd.le
  have hy : 0<m/e := div_pos hm he
  have hxy : s/d≤m/e := by
    apply (div_le_div_iff₀ hd he).2
    have ht := mul_nonneg (mul_pos hh hL).le (sub_nonneg.mpr hsm)
    dsimp [d,e]
    nlinarith
  have ha : 0 ≤ i*(L-h-i)/L := by
    exact div_nonneg (mul_nonneg hi (by linarith)) hL.le
  have hb := quadratic_le_endpoint_max (i*(L-h-i)/L) (-(h/L)) (1/L)
    (s/d) (m/e) ha hx hxy hy
  rw [cutEdgePurity_quadratic L h i s (ne_of_gt hL) (ne_of_gt hd),
      cutEdgePurity_quadratic L h i m (ne_of_gt hL) (ne_of_gt he)]
  convert hb using 1 <;> dsimp only [d,e] <;> ring

/-- The endpoint bound is strict below the longer endpoint whenever its
zero-support endpoint is strictly below the proposed optimum. -/
theorem quadratic_lt_strict_endpoint (a b c x y C : ℝ) (ha : 0≤a)
    (hx : 0≤x) (hxy : x<y) (hy : 0<y) (hc : c<C)
    (hf : a*y^2+b*y+c≤C) : a*x^2+b*x+c<C := by
  have h1 := mul_lt_mul_of_pos_left hc (sub_pos.mpr hxy)
  have h2 := mul_le_mul_of_nonneg_left hf hx
  have h3 : 0≤a*x*y*(y-x) := by positivity
  have hchord : y*(a*x^2+b*x+c) ≤ (y-x)*c+x*(a*y^2+b*y+c) := by nlinarith
  have htotal : y*(a*x^2+b*x+c)<y*C := by nlinarith
  exact (mul_lt_mul_iff_right₀ hy).mp htotal

end APPTReview
