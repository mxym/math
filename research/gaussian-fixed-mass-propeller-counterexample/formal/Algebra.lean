import Mathlib.Tactic

/-! Partial formalization of the explicit counterexample's algebra.
Gaussian facet integrals, exact-mass selection and optimizer existence
are proved in the accompanying paper, not in this file. -/
namespace FacetExchange

theorem centered_constant (n : ℕ) (x : Fin n → ℝ) (w : ℝ)
    (h : ∑ i, x i = 0) :
    ∑ i, (x i - w)^2 = (∑ i, (x i)^2) + n * w^2 := by
  calc
    _ = ∑ i, ((x i)^2 - 2 * w * x i + w^2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, h, mul_zero, sub_zero, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem tangent_identity (A B r : ℝ) (hr : r^2 = 2) (hpos : 0 < r) :
    4*A/(2*r) - ((A+3*B)+(B-A))/(2*r) = r*(A-B) := by
  have hn : r ≠ 0 := ne_of_gt hpos
  field_simp
  rw [hr]
  ring

theorem exchange_identity (x y Δ : ℝ) :
    (x+Δ)^2 + (y-Δ)^2 - (x^2+y^2) = 2*(x-y)*Δ+2*Δ^2 := by
  ring

theorem strict_margin (A B r : ℝ) (hA : 0 < A) (hB : A < B)
    (hr : 7/5 < r) :
    let η := (B-A)/(100*(A+B))
    0 < η ∧ η < 1/100 ∧
      r*(B-A) - 2*η*(3*A+B) - 5*η*(A+B) > B-A := by
  dsimp
  have hs : 0 < A+B := by linarith
  have hd : 0 < 100*(A+B) := by positivity
  have he : 0 < (B-A)/(100*(A+B)) := div_pos (by linarith) hd
  have hsmall : (B-A)/(100*(A+B)) < 1/100 := by
    apply (div_lt_iff₀ hd).mpr
    linarith
  have hid : (B-A)/(100*(A+B)) * (100*(A+B)) = B-A :=
    div_mul_cancel₀ _ (ne_of_gt hd)
  have hcoef : 2*((B-A)/(100*(A+B)))*(3*A+B) ≤
      6*((B-A)/(100*(A+B)))*(A+B) := by nlinarith
  have hprod : 0 < (r - 11/100 - 1)*(B-A) := mul_pos (by linarith) (by linarith)
  refine ⟨he, hsmall, ?_⟩
  nlinarith

-- Concrete nonvacuity and wrong-sign control.
example : (2 : ℝ) - 1 > 0 := by norm_num
example : ¬ ((1 : ℝ) - 2 > 0) := by norm_num

#print axioms centered_constant
#print axioms tangent_identity
#print axioms exchange_identity
#print axioms strict_margin
end FacetExchange
