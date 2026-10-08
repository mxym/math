import BapatPeakToEndpoint
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace BapatRealExistence
noncomputable section

/-- Squared modulus envelope for the quartic real selector. -/
def selectorProfile (c s : ℝ) : ℝ := s * (1-s) * (1+c*s)^2

def selectorParameter (t : ℝ) : ℝ := (2*t-1) / (t*(3-4*t))

theorem selectorParameter_nonneg {t : ℝ} (ht : 1/2 ≤ t) (ht' : t < 3/4) :
    0 ≤ selectorParameter t := by
  unfold selectorParameter
  apply div_nonneg <;> nlinarith

theorem selectorParameter_root {t : ℝ} (ht : 1/2 ≤ t) (ht' : t < 3/4) :
    1-2*t+selectorParameter t*(3*t-4*t^2) = 0 := by
  have hp : 0 < t*(3-4*t) := mul_pos (by linarith) (by linarith)
  have hmul : selectorParameter t * (t*(3-4*t)) = 2*t-1 := by
    unfold selectorParameter
    exact div_mul_cancel₀ _ hp.ne'
  nlinarith [hmul]

theorem selectorProfile_hasDerivAt (c s : ℝ) :
    HasDerivAt (selectorProfile c)
      ((1+c*s)*(1-2*s+c*(3*s-4*s^2))) s := by
  convert ((hasDerivAt_id s).mul ((hasDerivAt_const s 1).sub (hasDerivAt_id s))).mul
    (((hasDerivAt_const s 1).add ((hasDerivAt_const s c).mul (hasDerivAt_id s))).pow 2) using 1
  · rfl
  · dsimp
    ring

theorem selector_critical_factor {c t s : ℝ} (ht : 0 < t)
    (hroot : 1-2*t+c*(3*t-4*t^2) = 0) :
    1-2*s+c*(3*s-4*s^2) = (t-s)*(t⁻¹+4*c*s) := by
  apply (mul_left_cancel₀ ht.ne' : t * _ = t * _ → _ = _)
  field_simp
  linear_combination s * hroot

theorem selectorProfile_strictMonoOn {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t)
    (hroot : 1-2*t+c*(3*t-4*t^2) = 0) :
    StrictMonoOn (selectorProfile c) (Icc 0 t) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by unfold selectorProfile; fun_prop)
  intro s hs
  rw [interior_Icc] at hs
  rw [(selectorProfile_hasDerivAt c s).deriv, selector_critical_factor ht hroot]
  have hs0 : 0 ≤ s := hs.1.le
  exact mul_pos (by nlinarith [mul_nonneg hc hs.1.le])
    (mul_pos (sub_pos.mpr hs.2) (by positivity))

theorem selectorProfile_strictAntiOn {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t)
    (hroot : 1-2*t+c*(3*t-4*t^2) = 0) :
    StrictAntiOn (selectorProfile c) (Icc t 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (by unfold selectorProfile; fun_prop)
  intro s hs
  rw [interior_Icc] at hs
  rw [(selectorProfile_hasDerivAt c s).deriv, selector_critical_factor ht hroot]
  have hspos : 0 < s := ht.trans hs.1
  exact mul_neg_of_pos_of_neg (by nlinarith [mul_nonneg hc hspos.le])
    (mul_neg_of_neg_of_pos (sub_neg.mpr hs.1) (by positivity))

/-- The quartic envelope has exactly one maximizing squared first-coordinate modulus. -/
theorem selectorProfile_unique_max {t s : ℝ} (ht : 1/2 ≤ t) (ht' : t < 3/4)
    (hs : s ∈ Icc 0 1) :
    selectorProfile (selectorParameter t) s ≤ selectorProfile (selectorParameter t) t ∧
      (selectorProfile (selectorParameter t) s = selectorProfile (selectorParameter t) t ↔ s=t) := by
  have ht0 : 0 < t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hc := selectorParameter_nonneg ht ht'
  have hr := selectorParameter_root ht ht'
  rcases lt_trichotomy s t with h | rfl | h
  · have hlt := selectorProfile_strictMonoOn hc ht0 hr ⟨hs.1,h.le⟩ ⟨ht0.le,le_rfl⟩ h
    exact ⟨hlt.le, ⟨fun he => False.elim (hlt.ne he),fun he => False.elim (h.ne he)⟩⟩
  · exact ⟨le_rfl, by simp⟩
  · have hlt := selectorProfile_strictAntiOn hc ht0 hr ⟨le_rfl,ht1⟩ ⟨h.le,hs.2⟩ h
    exact ⟨hlt.le, ⟨fun he => False.elim (hlt.ne he),fun he => False.elim (h.ne he.symm)⟩⟩

theorem selectorProfile_max_pos {t : ℝ} (ht : 1/2 ≤ t) (ht' : t < 3/4) :
    0 < selectorProfile (selectorParameter t) t := by
  have hc := selectorParameter_nonneg ht ht'
  unfold selectorProfile
  apply mul_pos (mul_pos (by linarith) (by linarith))
  exact sq_pos_of_pos (by nlinarith [mul_nonneg hc (show 0 ≤ t by linarith)])

end
end BapatRealExistence
