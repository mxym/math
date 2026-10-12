import BapatGaussianAngular
import BapatComplexProductMeasure

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ComplexConjugate

namespace BapatRealExistence
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The unit-sphere angular mass is determined from the Gaussian integral of one. -/
theorem complexProductHaar_sphere_mass :
    ((complexProductHaar ι).toSphere.real univ : ℂ) *
      (((Fintype.card ι-1).factorial : ℂ) / 2) =
        (Real.pi : ℂ)^(Fintype.card ι) := by
  have h := homogeneous_gaussian_integral_even_dim (complexProductHaar ι)
    (Fintype.card ι) 0 Fintype.card_pos (complexProductHaar_finrank ι)
    (fun _ => (1 : ℂ)) (by intros; simp)
  simp only [one_mul, Nat.add_zero, integral_const, Complex.real_smul, mul_one] at h
  rw [complex_gaussian_integral] at h
  exact h.symm

/-- Exact normalized complex-sphere monomial moments. -/
theorem complex_sphere_moment (α β : ι → ℕ) (d : ℕ)
    (hα : ∑ i, α i = d) (hβ : ∑ i, β i = d) :
    (∫ z : sphere (0 : EuclideanSpace ℂ ι) 1,
      complexMonomial α z * conj (complexMonomial β z)
      ∂normalizedSphere (complexProductHaar ι)) =
      if α = β then ((∏ i, (α i).factorial : ℕ) : ℂ) *
        ((Fintype.card ι-1).factorial : ℂ) / ((Fintype.card ι+d-1).factorial : ℂ)
      else 0 := by
  have h := homogeneous_gaussian_integral_even_dim (complexProductHaar ι)
    (Fintype.card ι) d Fintype.card_pos (complexProductHaar_finrank ι)
    (fun z => complexMonomial α z * conj (complexMonomial β z))
    (fun a _ z => complexMonomial_pair_homogeneous α β d hα hβ a z)
  rw [complexMonomial_gaussian_integral, integral_toSphere_eq_mass_mul_normalized] at h
  have hm := complexProductHaar_sphere_mass (ι := ι)
  have hπ : (Real.pi : ℂ)^(Fintype.card ι) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hf0 : ((Fintype.card ι-1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hfd : ((Fintype.card ι+d-1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hm0 : ((complexProductHaar ι).toSphere.real univ : ℂ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hm
    exact hπ hm.symm
  split_ifs with heq
  · rw [if_pos heq] at h
    rw [← hm] at h
    apply (eq_div_iff hfd).mpr
    apply (mul_left_cancel₀ hm0)
    push_cast
    linear_combination -2 * h
  · rw [if_neg heq] at h
    have hz := (mul_eq_zero.mp h.symm).resolve_right (div_ne_zero hfd (by norm_num))
    exact (mul_eq_zero.mp hz).resolve_left hm0

end
end BapatRealExistence
