import BapatComplexGaussian

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal

namespace BapatRealExistence
noncomputable section

/-- Gaussian radial integral for Lebesgue polar coordinates of dimension `n`. -/
theorem gaussian_radial_integral (n k : ℕ) (hn : 0 < n) :
    (∫ r : Ioi (0 : ℝ), (r : ℝ)^k * Real.exp (-(r : ℝ)^2)
      ∂volumeIoiPow (n-1)) =
      (1/2 : ℝ) * Real.Gamma (((n : ℝ)+k)/2) := by
  have hr : (∫ r in Ioi (0 : ℝ), r^(n-1+k) * Real.exp (-r^2)) =
      (1/2 : ℝ) * Real.Gamma (((n : ℝ)+k)/2) := by
    have h := _root_.integral_rpow_mul_exp_neg_rpow
      (p := 2) (q := ((n-1+k : ℕ) : ℝ)) (by norm_num)
      (by have := Nat.cast_nonneg (α := ℝ) (n-1+k); linarith)
    have he : (((n-1+k : ℕ) : ℝ)+1)/2 = ((n : ℝ)+k)/2 := by
      rw [Nat.cast_add, Nat.cast_sub hn, Nat.cast_one]
      ring
    simpa only [Real.rpow_natCast, Real.rpow_two, he] using h
  rw [← hr]
  simp only [volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => Real.toNNReal (r^(n-1)) • (r^k * Real.exp (-r^2)))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hr) _)]
    simp only [pow_add]
    ring
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Separate a homogeneous integrand from its radial Gaussian weight. -/
theorem homogeneous_gaussian_integral (μ : Measure E) [IsAddHaarMeasure μ]
    (h : E → ℂ) (k : ℕ)
    (hh : ∀ (r : ℝ), 0 < r → ∀ x, h (r • x) = (r : ℂ)^k * h x) :
    (∫ x, h x * (Real.exp (-‖x‖^2) : ℂ) ∂μ) =
      (∫ x : sphere (0 : E) 1, h x ∂μ.toSphere) *
        ((1/2 : ℝ) * Real.Gamma ((((Module.finrank ℝ E : ℕ) : ℝ)+k)/2) : ℝ) := by
  let g : sphere (0 : E) 1 × Ioi (0 : ℝ) → ℂ :=
    fun x => h x.1 * ((x.2 : ℝ)^k * Real.exp (-(x.2 : ℝ)^2) : ℝ)
  calc
    _ = ∫ x : ({(0)}ᶜ : Set E), h x * (Real.exp (-‖(x : E)‖^2) : ℂ)
          ∂μ.comap (↑) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl
        (fun x : E => h x * (Real.exp (-‖x‖^2) : ℂ)),
        restrict_compl_singleton]
    _ = ∫ x, g x ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) := by
      rw [← μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) g]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      have hn : 0 < ‖(x : E)‖ := norm_pos_iff.mpr x.property
      simp only [g, homeomorphUnitSphereProd_apply_fst_coe,
        homeomorphUnitSphereProd_apply_snd_coe]
      change h (x : E) * (Real.exp (-‖(x : E)‖^2) : ℂ) =
        h (‖(x : E)‖⁻¹ • (x : E)) *
          ((‖(x : E)‖^k * Real.exp (-‖(x : E)‖^2) : ℝ) : ℂ)
      rw [hh _ (inv_pos.mpr hn), Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_inv]
      simp only [inv_pow]
      field_simp [Complex.ofReal_ne_zero.mpr hn.ne']
    _ = (∫ x : sphere (0 : E) 1, h x ∂μ.toSphere) *
        ∫ r : Ioi (0 : ℝ), (((r : ℝ)^k * Real.exp (-(r : ℝ)^2) : ℝ) : ℂ)
          ∂volumeIoiPow (Module.finrank ℝ E-1) := by
      simpa only [g] using (integral_prod_mul (μ := μ.toSphere)
        (ν := volumeIoiPow (Module.finrank ℝ E-1))
        (fun x : sphere (0 : E) 1 => h x)
        (fun r : Ioi (0 : ℝ) => (((r : ℝ)^k * Real.exp (-(r : ℝ)^2) : ℝ) : ℂ)))
    _ = _ := by
      rw [integral_complex_ofReal, gaussian_radial_integral _ _ Module.finrank_pos]

theorem homogeneous_gaussian_integral_even_dim (μ : Measure E) [IsAddHaarMeasure μ]
    (r d : ℕ) (hr : 0 < r) (hdim : Module.finrank ℝ E = 2*r)
    (h : E → ℂ)
    (hh : ∀ (a : ℝ), 0 < a → ∀ x, h (a • x) = (a : ℂ)^(2*d) * h x) :
    (∫ x, h x * (Real.exp (-‖x‖^2) : ℂ) ∂μ) =
      (∫ x : sphere (0 : E) 1, h x ∂μ.toSphere) *
        (((r+d-1).factorial : ℂ) / 2) := by
  rw [homogeneous_gaussian_integral μ h (2*d) hh, hdim]
  have he : (((2*r : ℕ) : ℝ)+(2*d : ℕ))/2 = ((r+d-1 : ℕ) : ℝ)+1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r+d)]
    push_cast
    ring
  rw [he, Real.Gamma_nat_eq_factorial]
  push_cast
  ring

theorem integral_toSphere_eq_mass_mul_normalized (μ : Measure E) [IsAddHaarMeasure μ]
    (h : sphere (0 : E) 1 → ℂ) :
    (∫ x, h x ∂μ.toSphere) =
      (μ.toSphere.real univ : ℂ) * ∫ x, h x ∂normalizedSphere μ := by
  have hm0 : μ.toSphere univ ≠ 0 := by
    intro hz
    exact μ.toSphere_ne_zero (measure_univ_eq_zero.mp hz)
  have hm : μ.toSphere.real univ ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hm0, measure_ne_top _ _⟩
  rw [normalizedSphere, integral_smul_measure, ENNReal.toReal_inv]
  simp only [Complex.real_smul, ← measureReal_def, Complex.ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hm), one_mul]

end
end BapatRealExistence
