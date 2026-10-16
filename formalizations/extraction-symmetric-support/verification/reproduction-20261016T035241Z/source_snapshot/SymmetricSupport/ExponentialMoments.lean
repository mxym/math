import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic

open scoped BigOperators
open MeasureTheory Set

namespace SymmetricSupport

/-- The radial moment used in an actual complex Gaussian construction. -/
theorem integral_exponential_moment (n : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ n * Real.exp (-x)) = (n.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ) + 1) (r := 1) (by positivity) (by norm_num)
  simpa only [add_sub_cancel_right, Real.rpow_natCast, one_mul, one_div, inv_one,
    Real.one_rpow, one_mul, Real.Gamma_nat_eq_factorial] using h

theorem integrable_exponential_moment (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-x)) (Ioi 0) := by
  simpa only [add_sub_cancel_right, Real.rpow_natCast, mul_comm] using
    (Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity))

/-- Independent radial coordinates have the product factorial moment, with actual
Lebesgue integrals and their actual positive densities. -/
theorem integral_product_exponential_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) :
    (∫ x : ι → ℝ, ∏ i, (x i) ^ n i * Real.exp (-x i)
      ∂Measure.pi (fun _ : ι => volume.restrict (Ioi 0))) =
      ∏ i, ((n i).factorial : ℝ) := by
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun i (t : ℝ) => t ^ n i * Real.exp (-t))]
  simp only [integral_exponential_moment]

end SymmetricSupport
