import BapatComplexGaussian
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ComplexConjugate

namespace BapatRealExistence
noncomputable section
variable (ι : Type*) [Fintype ι]

/-- Lebesgue measure in complex coordinates, transported to the Hilbert norm. -/
def complexProductHaar : Measure (EuclideanSpace ℂ ι) :=
  Measure.map (WithLp.toLp 2) (volume : Measure (ι → ℂ))

instance complexProductHaar_isAddHaar : IsAddHaarMeasure (complexProductHaar ι) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℂ)).symm.isAddHaarMeasure_map volume

theorem complexProductHaar_measurePreserving :
    MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℂ)) volume (complexProductHaar ι) :=
  (MeasurableEquiv.toLp 2 (ι → ℂ)).measurable.measurePreserving volume

theorem complexProductHaar_finrank :
    Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι)]
  simp [Complex.finrank_real_complex]

variable {ι}

def complexMonomial (α : ι → ℕ) (z : EuclideanSpace ℂ ι) : ℂ := ∏ i, (z i)^(α i)

theorem gaussian_product_factor (α β : ι → ℕ) (z : ι → ℂ) :
    complexMonomial α (WithLp.toLp 2 z) * conj (complexMonomial β (WithLp.toLp 2 z)) *
      (Real.exp (-‖WithLp.toLp 2 z‖^2) : ℂ) =
      ∏ i, gaussianMonomial (α i) (β i) (z i) := by
  simp only [complexMonomial, WithLp.toLp_ofLp, PiLp.toLp_apply, map_prod, map_pow,
    gaussianMonomial, Finset.prod_mul_distrib, EuclideanSpace.norm_sq_eq]
  congr 1
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  rw [Finset.sum_neg_distrib]

/-- Exact multivariable Gaussian orthogonality in the actual complex Hilbert space. -/
theorem complexMonomial_gaussian_integral (α β : ι → ℕ) :
    (∫ z, complexMonomial α z * conj (complexMonomial β z) *
      (Real.exp (-‖z‖^2) : ℂ) ∂complexProductHaar ι) =
      if α = β then (Real.pi : ℂ)^(Fintype.card ι) * ∏ i, ((α i).factorial : ℂ)
      else 0 := by
  rw [← (complexProductHaar_measurePreserving ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℂ)).measurableEmbedding]
  simp_rw [MeasurableEquiv.toLp_apply, gaussian_product_factor]
  exact gaussianMonomial_prod_integral α β

theorem complexMonomial_zero (z : EuclideanSpace ℂ ι) :
    complexMonomial (fun _ => 0) z = 1 := by simp [complexMonomial]

theorem complex_gaussian_integral :
    (∫ z, (Real.exp (-‖z‖^2) : ℂ) ∂complexProductHaar ι) =
      (Real.pi : ℂ)^(Fintype.card ι) := by
  simpa only [complexMonomial_zero, map_one, one_mul, ↓reduceIte,
    Nat.factorial_zero, Nat.cast_one, Finset.prod_const_one, mul_one] using
    complexMonomial_gaussian_integral (ι := ι) (fun _ => 0) (fun _ => 0)

theorem complexMonomial_smul (α : ι → ℕ) (a : ℝ) (z : EuclideanSpace ℂ ι) :
    complexMonomial α (a • z) = (a : ℂ)^(∑ i, α i) * complexMonomial α z := by
  simp only [complexMonomial, PiLp.smul_apply, Complex.real_smul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem complexMonomial_pair_homogeneous (α β : ι → ℕ) (d : ℕ)
    (hα : ∑ i, α i = d) (hβ : ∑ i, β i = d)
    (a : ℝ) (z : EuclideanSpace ℂ ι) :
    complexMonomial α (a • z) * conj (complexMonomial β (a • z)) =
      (a : ℂ)^(2*d) * (complexMonomial α z * conj (complexMonomial β z)) := by
  simp only [complexMonomial_smul, hα, hβ, map_mul, map_pow, Complex.conj_ofReal]
  rw [two_mul, pow_add]
  ring

end
end BapatRealExistence
