import CofactorLogarithmicUpper

/-! Finite Gibbs inequality, proved directly from log t <= t-1. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {V : Type*} [Fintype V]

theorem finite_gibbs_inequality (p g : V → ℝ)
    (hp : ∀ i, 0 < p i) (hg : ∀ i, 0 < g i)
    (hs : ∑ i, p i = 1) (ht : ∑ i, g i ≤ 1) :
    -(∑ i, p i * Real.log (p i)) ≤ -(∑ i, p i * Real.log (g i)) := by
  have hpoint : ∀ i, p i * (Real.log (g i)-Real.log (p i)) ≤ g i-p i := by
    intro i
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (hg i) (hp i))) (hp i).le
    rw [Real.log_div (ne_of_gt (hg i)) (ne_of_gt (hp i))] at h
    have he : p i * (g i/p i-1) = g i-p i := by
      field_simp [ne_of_gt (hp i)]
    rwa [he] at h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp_rw [mul_sub,Finset.sum_sub_distrib] at hsum
  rw [hs] at hsum
  linarith

theorem finite_geometric_mass (r : ℝ) (n : ℕ) :
    (∑ i : Fin n, (1-r)*r^i.val) = 1-r^n := by
  calc
    _ = ∑ j ∈ Finset.range n, (1-r)*r^j :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => (1-r)*r^j) n
    _ = 1-r^n := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ,ih,pow_succ]
        ring

end
end CofactorSpectral
