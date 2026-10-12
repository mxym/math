import BapatSphereInvariance
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Complex.Isometry

set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate

namespace BapatRealExistence

noncomputable section

theorem complex_radial_gaussian_integral (k : ℕ) :
    (∫ z : ℂ, ‖z‖^k * Real.exp (-‖z‖^2)) =
      Real.pi * Real.Gamma (((k : ℝ)+2)/2) := by
  have h := Complex.integral_rpow_mul_exp_neg_rpow
    (p := 2) (q := (k : ℝ)) (by norm_num) (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  simpa [Real.rpow_natCast, Real.rpow_two] using h

theorem complex_radial_gaussian_integrable (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖^k * Real.exp (-‖z‖^2)) := by
  apply Integrable.of_integral_ne_zero
  rw [complex_radial_gaussian_integral]
  exact (mul_pos Real.pi_pos (Real.Gamma_pos_of_pos (by positivity))).ne'

def gaussianMonomial (k l : ℕ) (z : ℂ) : ℂ :=
  z^k * (conj z)^l * (Real.exp (-‖z‖^2) : ℂ)

theorem norm_gaussianMonomial (k l : ℕ) (z : ℂ) :
    ‖gaussianMonomial k l z‖ = ‖z‖^(k+l) * Real.exp (-‖z‖^2) := by
  simp only [gaussianMonomial, norm_mul, norm_pow, Complex.norm_conj,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← pow_add]

theorem gaussianMonomial_integrable (k l : ℕ) : Integrable (gaussianMonomial k l) := by
  apply (integrable_norm_iff (by unfold gaussianMonomial; fun_prop)).mp
  simpa only [norm_gaussianMonomial] using complex_radial_gaussian_integrable (k+l)

theorem gaussianMonomial_self (k : ℕ) (z : ℂ) :
    gaussianMonomial k k z = (‖z‖^(2*k) * Real.exp (-‖z‖^2) : ℝ) := by
  simp only [gaussianMonomial, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← pow_mul]

theorem gaussianMonomial_self_integral (k : ℕ) :
    (∫ z : ℂ, gaussianMonomial k k z) = (Real.pi : ℂ) * (k.factorial : ℂ) := by
  simp_rw [gaussianMonomial_self]
  rw [integral_complex_ofReal, complex_radial_gaussian_integral]
  have he : (((2*k : ℕ) : ℝ)+2)/2 = (k : ℝ)+1 := by push_cast; ring
  rw [he, Real.Gamma_nat_eq_factorial]
  push_cast
  rfl

/-- A phase distinguishing two different powers, with no choice of a primitive root. -/
theorem exists_phase_opposite (k l : ℕ) (hkl : k ≠ l) :
    ∃ a : Circle, (a : ℂ)^k * (conj (a : ℂ))^l = -1 := by
  let θ : ℝ := Real.pi / ((k : ℝ) - l)
  have hd : (k : ℝ) - l ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hkl)
  have ht : (k : ℝ)*θ - (l : ℝ)*θ = Real.pi := by
    dsimp [θ]
    field_simp
  refine ⟨Circle.exp θ, ?_⟩
  calc
    _ = (((Circle.exp θ)^k / (Circle.exp θ)^l : Circle) : ℂ) := by
      simp only [div_eq_mul_inv, ← inv_pow, Circle.coe_mul, Circle.coe_pow,
        Circle.coe_inv_eq_conj]
    _ = (Circle.exp ((k : ℝ)*θ - (l : ℝ)*θ) : ℂ) := by
      rw [Circle.exp_sub, Circle.exp_natCast_mul, Circle.exp_natCast_mul]
    _ = -1 := by rw [ht, Circle.coe_exp, Complex.exp_pi_mul_I]

theorem gaussianMonomial_rotation (k l : ℕ) (a : Circle) (z : ℂ) :
    gaussianMonomial k l (rotation a z) =
      ((a : ℂ)^k * (conj (a : ℂ))^l) * gaussianMonomial k l z := by
  unfold gaussianMonomial
  rw [(rotation a).norm_map]
  simp only [rotation_apply, mul_pow, map_mul]
  ring

theorem gaussianMonomial_integral_of_ne (k l : ℕ) (hkl : k ≠ l) :
    (∫ z : ℂ, gaussianMonomial k l z) = 0 := by
  obtain ⟨a, ha⟩ := exists_phase_opposite k l hkl
  have hm := (rotation a).measurePreserving.integral_comp
    (rotation a).toHomeomorph.measurableEmbedding (gaussianMonomial k l)
  simp_rw [gaussianMonomial_rotation, ha] at hm
  rw [integral_const_mul] at hm
  linear_combination -(1/2 : ℂ) * hm

theorem gaussianMonomial_integral (k l : ℕ) :
    (∫ z : ℂ, gaussianMonomial k l z) =
      if k = l then (Real.pi : ℂ) * (k.factorial : ℂ) else 0 := by
  split_ifs with h
  · subst l; exact gaussianMonomial_self_integral k
  · exact gaussianMonomial_integral_of_ne k l h

section FiniteProduct

variable {ι : Type*} [Fintype ι]

theorem gaussianMonomial_prod_integrable (α β : ι → ℕ) :
    Integrable (fun z : ι → ℂ => ∏ i, gaussianMonomial (α i) (β i) (z i)) :=
  Integrable.fintype_prod fun i => gaussianMonomial_integrable (α i) (β i)

theorem gaussianMonomial_prod_integral (α β : ι → ℕ) :
    (∫ z : ι → ℂ, ∏ i, gaussianMonomial (α i) (β i) (z i)) =
      if α = β then (Real.pi : ℂ)^(Fintype.card ι) * ∏ i, ((α i).factorial : ℂ)
      else 0 := by
  classical
  rw [integral_fintype_prod_volume_eq_prod]
  simp_rw [gaussianMonomial_integral]
  split_ifs with h
  · subst β
    simp [Finset.prod_mul_distrib]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

end FiniteProduct
end
end BapatRealExistence
