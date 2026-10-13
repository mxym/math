import APPTReview.FiniteScaleMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators NNReal
namespace APPTReview
attribute [local instance] Classical.propDecidable

noncomputable def rawAmplitudeScale (L x : ℝ) : ℝ := 1+2*Real.log x/L
noncomputable def amplitudeScale (L x : ℝ) : ℝ := max 0 (rawAmplitudeScale L x)

theorem amplitudeScale_bounds (L x : ℝ) (hL : 0<L) (hx : 0≤x) (hx1 : x≤1) :
    0≤amplitudeScale L x ∧ amplitudeScale L x≤1 := by
  have hl := Real.log_nonpos hx hx1
  constructor
  · exact le_max_left _ _
  · apply max_le (by norm_num)
    unfold rawAmplitudeScale
    have hh : 2*Real.log x/L≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le
    linarith

noncomputable def amplitudeScalePoint (L x : ℝ) (hL : 0<L) (hx : 0≤x) (hx1 : x≤1) :
    ScaleInterval :=
  ⟨⟨amplitudeScale L x,(amplitudeScale_bounds L x hL hx hx1).1⟩,
    ⟨by exact_mod_cast (amplitudeScale_bounds L x hL hx hx1).1,
      by exact_mod_cast (amplitudeScale_bounds L x hL hx hx1).2⟩⟩

/-- Good coordinates are changed by clipping by at most eta; zero coordinates
cannot satisfy this positive lower cutoff. -/
theorem amplitudeScale_clip_error (L x η : ℝ) (hL : 0<L) (hx : 0≤x) (hη : 0≤η)
    (hgood : Real.exp (-(1+η)*L)≤x^2) :
    rawAmplitudeScale L x≤amplitudeScale L x ∧
      amplitudeScale L x≤rawAmplitudeScale L x+η := by
  have hlog := Real.log_le_log (Real.exp_pos _) hgood
  rw [Real.log_exp,Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hraw : -η≤rawAmplitudeScale L x := by
    unfold rawAmplitudeScale
    have hh : -(1+η)≤2*Real.log x/L := (le_div_iff₀ hL).2 (by linarith)
    linarith
  exact ⟨le_max_right _ _,max_le (by linarith) (by linarith)⟩

/-- Matched products of good amplitudes lie in a common clipped logarithmic
band. Both endpoints use the same scale map, with the full clipping error. -/
theorem amplitude_product_band (L x y d η : ℝ) (hL : 0<L)
    (hx : 0≤x) (hy : 0≤y) (hη : 0≤η)
    (hxg : Real.exp (-(1+η)*L)≤x^2) (hyg : Real.exp (-(1+η)*L)≤y^2)
    (hlo : Real.exp ((d/2-1-η)*L)≤x*y)
    (hhi : x*y≤Real.exp ((d/2-1+η)*L)) :
    |amplitudeScale L x+amplitudeScale L y-d|≤4*η := by
  have hxy : 0<x*y := (Real.exp_pos _).trans_le hlo
  have hxP : 0<x := by
    by_contra h
    have he : x=0 := by linarith
    simp [he] at hxy
  have hyP : 0<y := by
    by_contra h
    have he : y=0 := by linarith
    simp [he] at hxy
  have hll := Real.log_le_log (Real.exp_pos _) hlo
  have hhh := Real.log_le_log hxy hhi
  rw [Real.log_exp,Real.log_mul (ne_of_gt hxP) (ne_of_gt hyP)] at hll
  rw [Real.log_exp,Real.log_mul (ne_of_gt hxP) (ne_of_gt hyP)] at hhh
  have hid : L*(rawAmplitudeScale L x+rawAmplitudeScale L y-d)=
      (2-d)*L+2*(Real.log x+Real.log y) := by
    unfold rawAmplitudeScale
    field_simp
    ring
  have hloR : d-2*η≤rawAmplitudeScale L x+rawAmplitudeScale L y := by
    have hh : L*(d-2*η)≤L*(rawAmplitudeScale L x+rawAmplitudeScale L y) := by nlinarith
    exact (mul_le_mul_iff_right₀ hL).mp hh
  have hhiR : rawAmplitudeScale L x+rawAmplitudeScale L y≤d+2*η := by
    have hh : L*(rawAmplitudeScale L x+rawAmplitudeScale L y)≤L*(d+2*η) := by nlinarith
    exact (mul_le_mul_iff_right₀ hL).mp hh
  have hxc := amplitudeScale_clip_error L x η hL hx hη hxg
  have hyc := amplitudeScale_clip_error L y η hL hy hη hyg
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Discarding very small amplitudes loses an exponentially small total mass.
The only dimension input is card(iota)<=exp L. -/
theorem small_amplitude_mass {ι : Type*} [Fintype ι] (s : ι → ℝ) (L η : ℝ)
    (hcard : (Fintype.card ι:ℝ)≤Real.exp L) :
    (∑ i,if Real.exp (-(1+η)*L)≤(s i)^2 then 0 else (s i)^2)≤Real.exp (-η*L) := by
  have hh : (∑ i,if Real.exp (-(1+η)*L)≤(s i)^2 then 0 else (s i)^2)≤
      (Fintype.card ι:ℝ)*Real.exp (-(1+η)*L) := by
    calc
      _ ≤ ∑ _i : ι,Real.exp (-(1+η)*L) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with h
        · positivity
        · exact le_of_lt (lt_of_not_ge h)
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_right hcard (Real.exp_pos (-(1+η)*L)).le
  have he : Real.exp L*Real.exp (-(1+η)*L)=Real.exp (-η*L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  exact hh.trans (hm.trans_eq he)

end APPTReview
