import Hydrology.FiniteBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

namespace HydrologyIdentifiability
open scoped BigOperators
noncomputable section

/-- The order-two Hankel determinant of any finite weighted rate spectrum is a
half weighted sum of squared pairwise rate gaps. -/
theorem finiteMoment_hankel_vandermonde {k : ℕ} (w l : Fin k → ℝ) :
    finiteMoment w l 0 * finiteMoment w l 2 - (finiteMoment w l 1)^2 =
      (1 / 2 : ℝ) * ∑ i, ∑ j, w i * w j * (l i - l j)^2 := by
  classical
  unfold finiteMoment
  simp only [pow_zero, pow_one, mul_one]
  have hgap :
      (∑ i, ∑ j, w i * w j * (l i - l j)^2) =
        (∑ i, ∑ j, w i * w j * (l i^2 + l j^2 - 2 * l i * l j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hgap]
  have hswap :
      (∑ i, ∑ j, w i * w j * l j^2) =
        (∑ i, ∑ j, w i * w j * l i^2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hexpand :
      (∑ i, ∑ j, w i * w j * (l i^2 + l j^2 - 2 * l i * l j)) =
        ∑ i, ∑ j, (w i * w j * l i^2 + w i * w j * l j^2 -
          2 * (w i * w j * l i * l j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hexpand]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hswap]
  have hprod :
      (∑ i, w i * l i)^2 =
        ∑ i, ∑ j, (w i * l i) * (w j * l j) := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [hprod]
  ring_nf
  simp only [Finset.mul_sum, Finset.sum_mul]
  have hfirst :
      (∑ x, ∑ y, w y * (w x * l x ^ 2)) =
        ∑ x, ∑ y, w x * l x ^ 2 * w y := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hcross :
      (∑ x, ∑ y, w x * l x * w y * l y) =
        ∑ x, ∑ y, w x * w y * l x * l y := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hC :
      (∑ x, ∑ y, w x * w y * l x ^ 2) =
        ∑ x, ∑ y, w x * l x ^ 2 * w y := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hfirst, hcross, hC]
  ring_nf
  simp only [Finset.sum_neg_distrib]
  ring

end
end HydrologyIdentifiability

namespace HydrologyIdentifiability

/-- Nonnegative weights make the finite-spectrum Hankel determinant nonnegative. -/
theorem finiteMoment_hankel_nonneg {k : ℕ} (w l : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    0 ≤ finiteMoment w l 0 * finiteMoment w l 2 -
      (finiteMoment w l 1)^2 := by
  rw [finiteMoment_hankel_vandermonde]
  have hsum : 0 ≤ ∑ i, ∑ j, w i * w j * (l i - l j)^2 := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (hw i) (hw j)) (sq_nonneg _)
  nlinarith [hsum]

end HydrologyIdentifiability

namespace HydrologyIdentifiability

/-- If two positive-weight modes have distinct rates, the order-two Hankel
certificate is strictly positive. -/
theorem finiteMoment_hankel_pos_of_distinct {k : ℕ} (w l : Fin k → ℝ)
    (hw : ∀ i, 0 < w i)
    (hdistinct : ∃ i j, l i ≠ l j) :
    0 < finiteMoment w l 0 * finiteMoment w l 2 -
      (finiteMoment w l 1)^2 := by
  rw [finiteMoment_hankel_vandermonde]
  obtain ⟨i₀, j₀, hrate⟩ := hdistinct
  have hinner_nonneg : ∀ i, 0 ≤ ∑ j, w i * w j * (l i - l j)^2 := by
    intro i
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (le_of_lt (hw i)) (le_of_lt (hw j))) (sq_nonneg _)
  have hinner_pos : 0 < ∑ j, w i₀ * w j * (l i₀ - l j)^2 := by
    apply Finset.sum_pos' (fun j hj =>
      mul_nonneg (mul_nonneg (le_of_lt (hw i₀)) (le_of_lt (hw j))) (sq_nonneg _))
    refine ⟨j₀, Finset.mem_univ _, ?_⟩
    have hsq : 0 < (l i₀ - l j₀)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hrate)
    exact mul_pos (mul_pos (hw i₀) (hw j₀)) hsq
  have hdouble : 0 < ∑ i, ∑ j, w i * w j * (l i - l j)^2 := by
    apply Finset.sum_pos' (fun i hi => hinner_nonneg i)
    exact ⟨i₀, Finset.mem_univ _, hinner_pos⟩
  nlinarith [hdouble]

end HydrologyIdentifiability
