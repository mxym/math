import CofactorFactorialEstimate
import Mathlib.Data.Nat.Factorial.BigOperators

/-! The actual binomial lower bound below a prescribed fractional dimension. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

theorem binomial_lower (N h : ℕ) (δ : ℝ) (hδ : δ < 1) (hh : h ≤ N)
    (hfrac : (h : ℝ) ≤ δ*(N : ℝ)) :
    ((N : ℝ)*(1-δ))^h/(h.factorial : ℝ) ≤ (N.choose h : ℝ) := by
  have hb : 0 ≤ (N : ℝ)*(1-δ) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hp : ((N : ℝ)*(1-δ))^h ≤ (N.descFactorial h : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
    calc
      _ = ∏ _i ∈ Finset.range h, (N : ℝ)*(1-δ) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod₀ (fun _ _ => hb)
        intro i hi
        have hi' : i < h := Finset.mem_range.mp hi
        have hiN : i ≤ N := (Nat.le_of_lt hi').trans hh
        have hiR : (i : ℝ) ≤ (h : ℝ) := by exact_mod_cast Nat.le_of_lt hi'
        rw [Nat.cast_sub hiN]
        nlinarith
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul] at hp
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (h.factorial : ℝ))).2
  simpa only [mul_comm] using hp

end
end CofactorSpectral
