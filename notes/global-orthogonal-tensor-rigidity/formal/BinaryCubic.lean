import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Algebraic identities and scalar inequality in the binary-cubic theorem.
The angular maximization and tensor distance interpretation remain written
proofs, not statements verified by these Lean lemmas. -/

namespace QuantitativeJacobian

theorem binary_norm_identity (a b c d : ℝ) :
    (a + c)^2 + 3*(b + d/3)^2 + 3*(-a + c/3)^2 + (-b + d)^2 =
    4*(a^2+b^2) + (4/3 : ℝ)*(c^2+d^2) := by
  ring

theorem binary_commutator_identity (a b c d : ℝ) :
    (a+c)*(-a+c/3) + (b+d/3)*(-b+d) -
      (b+d/3)^2 - (-a+c/3)^2 =
    2*((c^2+d^2)/9-(a^2+b^2)) := by
  ring

theorem angular_amplitude_identity (a b c d : ℝ) :
    (a*c-b*d)^2+(a*d+b*c)^2 = (a^2+b^2)*(c^2+d^2) := by
  ring

theorem optimal_binary_scalar_bound (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A-B/3)^2 ≤ |A^2-B^2/9| := by
  by_cases h : B/3 ≤ A
  · have hp : 0 ≤ A^2-B^2/9 := by nlinarith
    rw [abs_of_nonneg hp]
    have hm := mul_nonneg hB (sub_nonneg.mpr h)
    nlinarith
  · have hn : A^2-B^2/9 ≤ 0 := by
      have hl : A ≤ B/3 := le_of_not_ge h
      nlinarith
    rw [abs_of_nonpos hn]
    have hl : 0 ≤ B/3-A := by linarith
    have hm := mul_nonneg hA hl
    nlinarith

#print axioms binary_norm_identity
#print axioms binary_commutator_identity
#print axioms angular_amplitude_identity
#print axioms optimal_binary_scalar_bound

end QuantitativeJacobian
