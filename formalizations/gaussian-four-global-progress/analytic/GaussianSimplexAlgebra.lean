import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! General finite weighted Cauchy and scalar radial identities.
Gaussian integrals and the imported multi-bubble theorem are not formalized. -/
open scoped BigOperators
namespace GaussianSimplexAlgebra

theorem weighted_cauchy {ι : Type*} (s : Finset ι) (w ell : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * ell i)^2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ell i^2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg (ell i)))
  intro i hi
  exact le_of_eq (by ring)

theorem perimeter_to_trace (n S c C T : ℝ) (hn : 0 < n)
    (hlower : n*c^2/2 ≤ S^2) (hcs : S^2 ≤ T*C/2) :
    c^2 ≤ C*T/n := by
  apply (le_div_iff₀ hn).2
  nlinarith

theorem radial_quotient_identity (n t C d T c : ℝ)
    (hd : t*d=(C-T/n)/2) :
    (t*(2*C*d)-(C^2-c^2))/t^2 = (c^2-C*T/n)/t^2 := by
  have he : t*(2*C*d)=C^2-C*T/n := by
    calc
      t*(2*C*d)=2*C*(t*d) := by ring
      _=2*C*((C-T/n)/2) := by rw [hd]
      _=C^2-C*T/n := by ring
  rw [he]
  congr 1
  ring

theorem deficit_derivative_nonpositive (t C T n c : ℝ)
    (hbound : c^2 ≤ C*T/n) : (c^2-C*T/n)/t^2 ≤ 0 := by
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbound) (sq_nonneg t)

#print axioms weighted_cauchy
#print axioms perimeter_to_trace
#print axioms radial_quotient_identity
#print axioms deficit_derivative_nonpositive
end GaussianSimplexAlgebra
