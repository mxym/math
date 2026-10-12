import BapatSelectorProfile

set_option autoImplicit false
open Set Metric

namespace BapatRealExistence
noncomputable section

def selectorQuartic (c : ℝ) (z : EuclideanSpace ℂ (Fin 4)) : ℂ :=
  z 0 * z 1 * (((1+c : ℝ) : ℂ) * (z 0)^2 - (z 1)^2)

theorem complex_four_norm_sq (z : EuclideanSpace ℂ (Fin 4)) :
    ‖z‖^2 = ‖z 0‖^2 + ‖z 1‖^2 + ‖z 2‖^2 + ‖z 3‖^2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  <;> ring

theorem selectorQuartic_triangle {c : ℝ} (hc : 0 ≤ c)
    (z : EuclideanSpace ℂ (Fin 4)) :
    ‖selectorQuartic c z‖^2 ≤ ‖z 0‖^2 * ‖z 1‖^2 *
      ((1+c)*‖z 0‖^2 + ‖z 1‖^2)^2 := by
  have h : ‖(((1+c : ℝ) : ℂ) * (z 0)^2 - (z 1)^2)‖ ≤
      (1+c)*‖z 0‖^2 + ‖z 1‖^2 := by
    calc
      _ ≤ ‖(((1+c : ℝ) : ℂ) * (z 0)^2)‖ + ‖(z 1)^2‖ := norm_sub_le _ _
      _ = _ := by
        rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ 1+c by linarith)]
  unfold selectorQuartic
  simp only [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 2) (by positivity)

theorem selector_envelope_le {c s r : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hr : 0 ≤ r) (hsr : s+r ≤ 1) :
    s*r*((1+c)*s+r)^2 ≤ selectorProfile c s := by
  have hs1 : 0 ≤ 1-s := by linarith
  have hr1 : r ≤ 1-s := by linarith
  have hbase : (1+c)*s+r ≤ 1+c*s := by nlinarith
  have hbase0 : 0 ≤ (1+c)*s+r := by positivity
  unfold selectorProfile
  exact mul_le_mul (mul_le_mul_of_nonneg_left hr1 hs)
    (pow_le_pow_left₀ hbase0 hbase 2) (by positivity) (by positivity)

theorem selector_envelope_strict {c s r : ℝ} (hc : 0 ≤ c) (hs : 0 < s)
    (hr : 0 ≤ r) (hsr : s+r < 1) :
    s*r*((1+c)*s+r)^2 < selectorProfile c s := by
  have hr1 : r < 1-s := by linarith
  have hbase : (1+c)*s+r ≤ 1+c*s := by nlinarith
  have hbase0 : 0 ≤ (1+c)*s+r := by positivity
  have hpos : 0 < (1+c*s)^2 := sq_pos_of_pos (by nlinarith [mul_nonneg hc hs.le])
  unfold selectorProfile
  calc
    s*r*((1+c)*s+r)^2 ≤ s*r*(1+c*s)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase0 hbase 2) (by positivity)
    _ < _ := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hr1 hs) hpos

theorem selectorQuartic_bound {t : ℝ} (ht : 1/2 ≤ t) (ht' : t < 3/4)
    (z : ComplexUnitSphere4) :
    ‖selectorQuartic (selectorParameter t) z‖^2 ≤ selectorProfile (selectorParameter t) t := by
  have hc := selectorParameter_nonneg ht ht'
  have hz : ‖(z : EuclideanSpace ℂ (Fin 4))‖ = 1 := by simpa using z.property
  have hn := complex_four_norm_sq (z : EuclideanSpace ℂ (Fin 4))
  rw [hz] at hn
  have hsum : ‖(z : EuclideanSpace ℂ (Fin 4)) 0‖^2 +
      ‖(z : EuclideanSpace ℂ (Fin 4)) 1‖^2 ≤ 1 := by
    nlinarith [sq_nonneg ‖(z : EuclideanSpace ℂ (Fin 4)) 2‖,
      sq_nonneg ‖(z : EuclideanSpace ℂ (Fin 4)) 3‖]
  exact (selectorQuartic_triangle hc z).trans
    ((selector_envelope_le hc (sq_nonneg _) (sq_nonneg _) hsum).trans
      (selectorProfile_unique_max ht ht' ⟨sq_nonneg _, by nlinarith [sq_nonneg ‖(z : EuclideanSpace ℂ (Fin 4)) 1‖]⟩).1)

/-- Equality forces the first two squared coordinate moduli and zero exterior coordinates. -/
theorem selectorQuartic_equality_moduli {t : ℝ} (ht : 1/2 ≤ t) (ht' : t < 3/4)
    (z : ComplexUnitSphere4)
    (heq : ‖selectorQuartic (selectorParameter t) z‖^2 = selectorProfile (selectorParameter t) t) :
    ‖(z : EuclideanSpace ℂ (Fin 4)) 0‖^2 = t ∧
    ‖(z : EuclideanSpace ℂ (Fin 4)) 1‖^2 = 1-t ∧
    (z : EuclideanSpace ℂ (Fin 4)) 2 = 0 ∧ (z : EuclideanSpace ℂ (Fin 4)) 3 = 0 := by
  let s := ‖(z : EuclideanSpace ℂ (Fin 4)) 0‖^2
  let r := ‖(z : EuclideanSpace ℂ (Fin 4)) 1‖^2
  have hs : 0 ≤ s := sq_nonneg _
  have hr : 0 ≤ r := sq_nonneg _
  have hc := selectorParameter_nonneg ht ht'
  have hz : ‖(z : EuclideanSpace ℂ (Fin 4))‖ = 1 := by simpa using z.property
  have hn := complex_four_norm_sq (z : EuclideanSpace ℂ (Fin 4))
  rw [hz] at hn
  have hsum : s+r ≤ 1 := by
    dsimp [s,r]
    nlinarith [sq_nonneg ‖(z : EuclideanSpace ℂ (Fin 4)) 2‖,
      sq_nonneg ‖(z : EuclideanSpace ℂ (Fin 4)) 3‖]
  have htri := selectorQuartic_triangle hc (z : EuclideanSpace ℂ (Fin 4))
  have henv := selector_envelope_le hc hs hr hsum
  have hmax := selectorProfile_unique_max ht ht' (s := s) ⟨hs,by linarith⟩
  have hst : s=t := hmax.2.mp (le_antisymm hmax.1 (by linarith))
  have hmass : s+r=1 := by
    by_contra h
    have hlt := selector_envelope_strict hc (show 0 < s by rw [hst]; linarith) hr
      (lt_of_le_of_ne hsum h)
    linarith
  refine ⟨hst, by linarith, ?_, ?_⟩
  · apply norm_eq_zero.mp
    dsimp [s,r] at hmass
    nlinarith [sq_nonneg ‖(z : EuclideanSpace ℂ (Fin 4)) 3‖,
      norm_nonneg ((z : EuclideanSpace ℂ (Fin 4)) 2)]
  · apply norm_eq_zero.mp
    dsimp [s,r] at hmass
    nlinarith [sq_nonneg ‖(z : EuclideanSpace ℂ (Fin 4)) 2‖,
      norm_nonneg ((z : EuclideanSpace ℂ (Fin 4)) 3)]

end
end BapatRealExistence
