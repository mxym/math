import CofactorEntropyProduct
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The elementary upper factorial estimate needed in the explicit subset tail. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

theorem log_factorial_eq_sum (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ i ∈ Finset.range n, Real.log ((i : ℝ)+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [Real.log_mul (by positivity) (by positivity),ih,Finset.sum_range_succ]
    push_cast
    ring

theorem log_factorial_upper (n : ℕ) :
    Real.log ((n+1).factorial : ℝ) ≤
      (n+1 : ℝ)*Real.log (n+1 : ℝ)-(n+1 : ℝ)+1+Real.log (n+1 : ℝ) := by
  have hm : MonotoneOn Real.log (Set.Icc (1 : ℝ) (1+(n : ℝ))) := by
    intro x hx y hy hxy
    exact Real.log_le_log (by linarith [hx.1]) hxy
  have h := hm.sum_le_integral
  rw [log_factorial_eq_sum,Finset.sum_range_succ]
  have hi : (∫ x in (1 : ℝ)..1+(n : ℝ), Real.log x) =
      (n+1 : ℝ)*Real.log (n+1 : ℝ)-(n+1 : ℝ)+1 := by
    rw [integral_log]
    simp only [Real.log_one,mul_zero,sub_zero]
    ring
  rw [hi] at h
  have he : (∑ i ∈ Finset.range n, Real.log ((i : ℝ)+1)) =
      ∑ i ∈ Finset.range n, Real.log (1+(i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [add_comm]
  rw [he]
  linarith

theorem factorial_upper (n : ℕ) :
    ((n+1).factorial : ℝ) ≤
      Real.exp 1*(n+1 : ℝ)*((n+1 : ℝ)/Real.exp 1)^(n+1) := by
  have hn : (0 : ℝ) < n+1 := by positivity
  have hf : (0 : ℝ) < ((n+1).factorial : ℝ) := by positivity
  have he : Real.log (Real.exp 1*(n+1 : ℝ)*((n+1 : ℝ)/Real.exp 1)^(n+1)) =
      (n+1 : ℝ)*Real.log (n+1 : ℝ)-(n+1 : ℝ)+1+Real.log (n+1 : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity)
      (by positivity),Real.log_pow,Real.log_div hn.ne' (Real.exp_ne_zero _),Real.log_exp]
    push_cast
    ring
  apply (Real.log_le_log_iff hf (by positivity)).mp
  rw [he]
  exact log_factorial_upper n

end
end CofactorSpectral
