import Entry005.Targets
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Pure gates for the ORIGINAL constants. They contain no new geometric
premises in the threshold conclusion. The final Main wrapper explicitly takes
the still unproved local and coarse geometric statements as inputs. -/

noncomputable section
open MeasureTheory

namespace Entry005

theorem original_small_error_budget {d : ℕ} (hd : 1 ≤ d) (e : ℝ)
    (he : e ≤ eSharp d) : Q d * (d + 1) * e ≤ rSharp d := by
  have hc : 0 < Q d * (d + 1) := by have := Q_pos hd; positivity
  have h := mul_le_mul_of_nonneg_left he hc.le
  have hi : Q d * (d + 1) * eSharp d = rSharp d := by
    unfold eSharp
    field_simp [(Q_pos hd).ne']
  rwa [hi] at h

theorem original_small_error_implies_M_budget {d : ℕ} (hd : 1 ≤ d) (e : ℝ)
    (he : e ≤ eSharp d) : M d * (Q d * (d + 1) * e) ≤ 1 := by
  have h := (original_small_error_budget hd e he).trans (min_le_left _ _)
  have hb := b_pos hd
  unfold M
  have hdiv : (Q d * (d + 1) * e) / b d ≤ 1 :=
    (div_le_iff₀ hb).mpr (by simpa using h)
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hdiv

theorem original_sharp_threshold {d : ℕ} (hd : 2 ≤ d) :
    aSharp d * (eSharp d) ^ (1 / ((d - 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
  have hd1 : 1 ≤ d := by omega
  let m := d - 1
  let T := 8 * M d * d * L d
  let C := J d * Q d * (d + 1)
  have hm : m ≠ 0 := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hm)
  have hJ := J_pos hd1
  have hQ := Q_pos hd1
  have hM := M_pos hd1
  have hL := L_pos hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have he := eSharp_pos hd
  have hbudget : C * eSharp d ≤ 1 / T ^ m := by
    have hr : rSharp d ≤ 1 / (J d * T ^ m) := min_le_right _ _
    have hbound := (le_div_iff₀ (mul_pos hJ (pow_pos hT m))).mp hr
    apply (le_div_iff₀ (pow_pos hT m)).mpr
    have hi : C * eSharp d = J d * rSharp d := by
      dsimp [C]
      unfold eSharp
      field_simp
    rw [hi]
    nlinarith
  have hroot := Real.rpow_le_rpow (mul_nonneg hC.le he.le) hbudget
    (show 0 ≤ 1 / (m : ℝ) by positivity)
  have hident : (1 / T ^ m : ℝ) ^ (1 / (m : ℝ)) = 1 / T := by
    rw [one_div, Real.inv_rpow (pow_nonneg hT.le m), one_div,
      Real.pow_rpow_inv_natCast hT.le hm]
    exact (one_div T).symm
  rw [hident, Real.mul_rpow hC.le he.le] at hroot
  have hmul := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ 4 * M d * d * L d by positivity)
  have ht : 4 * M d * d * L d * (1 / T) = 1 / 2 := by
    dsimp [T]
    field_simp
    ring
  rw [ht] at hmul
  exact (by simpa only [aSharp, C, m, mul_assoc] using hmul)

theorem original_threshold_gate : thresholdGateGoal := by
  intro d hd
  exact original_sharp_threshold (by omega)

theorem original_global_scalar_gluing {d : ℕ} (hd : 2 ≤ d) (E e : ℝ)
    (he : 0 ≤ e)
    (hlocal : e ≤ eSharp d → E ≤ aSharp d * e ^ (1 / ((d - 1 : ℕ) : ℝ)))
    (hcoarse : E ≤ R0 d - 1) :
    E ≤ gSharp d * e ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
  let r : ℝ := 1 / ((d - 1 : ℕ) : ℝ)
  have hd1 : 1 ≤ d := by omega
  have he0 := eSharp_pos hd
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hep : 0 ≤ e ^ r := Real.rpow_nonneg he _
  by_cases hsmall : e ≤ eSharp d
  · exact (hlocal hsmall).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hep)
  · have hlarge : eSharp d ≤ e := le_of_lt (lt_of_not_ge hsmall)
    have hp := Real.rpow_le_rpow he0.le hlarge hr
    have hc : 0 ≤ R0 d - 1 := by
      have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      unfold R0
      nlinarith
    have hpow := Real.rpow_pos_of_pos he0 r
    have hinv := mul_le_mul_of_nonneg_left hp
      (mul_nonneg hc (inv_nonneg.mpr hpow.le))
    have hcancel : (R0 d - 1) * ((eSharp d) ^ r)⁻¹ * (eSharp d) ^ r = R0 d - 1 := by
      rw [mul_assoc, inv_mul_cancel₀ hpow.ne', mul_one]
    rw [hcancel] at hinv
    have heq : (R0 d - 1) * ((eSharp d) ^ r)⁻¹ =
        (R0 d - 1) * (eSharp d) ^ (-r) := by rw [Real.rpow_neg he0.le]
    rw [heq] at hinv
    exact hcoarse.trans (hinv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hep))

theorem sharpMain_of_local_and_actual_coarse
    (hlocal : sharpLocalGoal)
    (hnonnegative : ∀ d : ℕ, 3 ≤ d → ∀ K : ConvexBody (Space d),
      (interior (K : Set (Space d))).Nonempty → 0 ≤ entryDefect (K : Set (Space d)))
    (hcoarse : ∀ d : ℕ, 3 ≤ d → ∀ K : ConvexBody (Space d),
      (interior (K : Set (Space d))).Nonempty →
      ∀ S : Affine.Simplex ℝ (Space d) d, maximumInscribed K S →
        excess (K : Set (Space d)) S ≤ R0 d - 1) : sharpMainGoal := by
  intro d hd K hK S hS
  exact original_global_scalar_gluing (by omega) (excess (K : Set (Space d)) S)
    (entryDefect (K : Set (Space d))) (hnonnegative d hd K hK)
    (hlocal d hd K hK S hS (hnonnegative d hd K hK)) (hcoarse d hd K hK S hS)

end Entry005
