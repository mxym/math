import GaussianFour.Profile
import GaussianOneCell

/-! Actual masses and moments of the four ordered Gaussian intervals. -/
open MeasureTheory ProbabilityTheory Set
namespace GaussianFour
open GaussianMeasureBridge

noncomputable def scalarMass (s : Set ℝ) : ℝ := ((gaussianReal 0 1) s).toReal
noncomputable def scalarMoment (s : Set ℝ) : ℝ := ∫ x in s, x ∂gaussianReal 0 1

def intervalCells (a b c : ℝ) : Fin 4 → Set ℝ := ![Iic a, Ioc a b, Ioc b c, Ioi c]

lemma scalarMass_density (s : Set ℝ) : scalarMass s = ∫ x in s, standardDensity x := by
  unfold scalarMass
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  exact ENNReal.toReal_ofReal (integral_nonneg fun x => (standardDensity_pos x).le)

lemma scalarMass_Ioi (a : ℝ) : scalarMass (Ioi a) = gaussianTail a :=
  (gaussianTail_eq_probability a).symm

lemma scalarMass_Iic (a : ℝ) : scalarMass (Iic a) = 1 - gaussianTail a := by
  rw [scalarMass_density]
  have h := integral_add_compl (μ := volume) (s := Ioi a)
    (f := standardDensity) measurableSet_Ioi integrable_standardDensity
  rw [compl_Ioi, show (∫ x, standardDensity x) = 1 from
    integral_gaussianPDFReal_eq_one 0 one_ne_zero] at h
  change gaussianTail a + _ = 1 at h
  linarith

lemma scalarMass_Ioc {a b : ℝ} (h : a ≤ b) :
    scalarMass (Ioc a b) = gaussianTail a - gaussianTail b := by
  rw [scalarMass_density, ← intervalIntegral.integral_of_le h,
    ← gaussianTail_sub_eq_interval]

/-- Equal actual interval masses force exactly the Gaussian quartile thresholds. -/
theorem equal_mass_interval_thresholds {a b c : ℝ} (hab : a ≤ b)
    (hm : ∀ i, scalarMass (intervalCells a b c i) = 1 / 4) :
    a = -quarterQuantile ∧ b = 0 ∧ c = quarterQuantile := by
  have h0 := hm 0
  have h1 := hm 1
  have h3 := hm 3
  change scalarMass (Iic a) = 1 / 4 at h0
  change scalarMass (Ioc a b) = 1 / 4 at h1
  change scalarMass (Ioi c) = 1 / 4 at h3
  rw [scalarMass_Iic] at h0
  rw [scalarMass_Ioc hab] at h1
  rw [scalarMass_Ioi] at h3
  have ha : gaussianTail a = gaussianTail (-quarterQuantile) := by
    rw [gaussianTail_neg, quarterQuantile_tail]
    linarith
  have hb : gaussianTail b = gaussianTail 0 := by rw [gaussianTail_zero]; linarith
  exact ⟨gaussianTail_strictAnti.injective ha, gaussianTail_strictAnti.injective hb,
    gaussianTail_strictAnti.injective (h3.trans quarterQuantile_tail.symm)⟩

lemma scalarMoment_Ioi (a : ℝ) : scalarMoment (Ioi a) = standardDensity a :=
  gaussianReal_halfline_firstMoment a

lemma scalarMoment_Iic (a : ℝ) : scalarMoment (Iic a) = -standardDensity a := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := IsGaussian.integrable_id
  have h := integral_add_compl (s := Ioi a) measurableSet_Ioi hi
  rw [compl_Ioi, integral_id_gaussianReal, gaussianReal_halfline_firstMoment] at h
  change _ + scalarMoment (Iic a) = 0 at h
  linarith

lemma scalarMoment_Ioc {a b : ℝ} (h : a ≤ b) :
    scalarMoment (Ioc a b) = standardDensity a - standardDensity b := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := IsGaussian.integrable_id
  have ht := intervalIntegral.integral_Ioi_sub_Ioi'
    (hi.integrableOn (s := Ioi a)) (hi.integrableOn (s := Ioi b))
  rw [gaussianReal_halfline_firstMoment, gaussianReal_halfline_firstMoment,
    intervalIntegral.integral_of_le h] at ht
  exact ht.symm

lemma scalarMass_Iio (a : ℝ) : scalarMass (Iio a) = scalarMass (Iic a) := by
  simp only [scalarMass_density, integral_Iic_eq_integral_Iio]

lemma scalarMass_Ioo (a b : ℝ) : scalarMass (Ioo a b) = scalarMass (Ioc a b) := by
  simp only [scalarMass_density, integral_Ioc_eq_integral_Ioo]

lemma scalarMoment_Iio (a : ℝ) : scalarMoment (Iio a) = scalarMoment (Iic a) := by
  letI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (by norm_num : (1 : NNReal) ≠ 0)
  simp only [scalarMoment, integral_Iic_eq_integral_Iio]

lemma scalarMoment_Ioo (a b : ℝ) : scalarMoment (Ioo a b) = scalarMoment (Ioc a b) := by
  letI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (by norm_num : (1 : NNReal) ≠ 0)
  simp only [scalarMoment, integral_Ioc_eq_integral_Ioo]

/-- The four exact first moments are actual Bochner integrals, not prescribed data. -/
theorem quartile_interval_moments :
    (fun i => scalarMoment (intervalCells (-quarterQuantile) 0 quarterQuantile i)) =
    ![-quarterDensity, quarterDensity - standardDensity 0,
      standardDensity 0 - quarterDensity, quarterDensity] := by
  funext i
  fin_cases i <;> simp [intervalCells, scalarMoment_Iic, scalarMoment_Ioi,
    scalarMoment_Ioc (show -quarterQuantile ≤ 0 by linarith [quarterQuantile_pos]),
    scalarMoment_Ioc quarterQuantile_pos.le, standardDensity_neg, quarterDensity]

/-- The canonical quartile cells really have the required Gaussian masses. -/
theorem quartile_interval_masses (i : Fin 4) :
    scalarMass (intervalCells (-quarterQuantile) 0 quarterQuantile i) = 1 / 4 := by
  fin_cases i <;> simp [intervalCells, scalarMass_Iic, scalarMass_Ioi,
    scalarMass_Ioc (show -quarterQuantile ≤ 0 by linarith [quarterQuantile_pos]),
    scalarMass_Ioc quarterQuantile_pos.le, gaussianTail_neg, quarterQuantile_tail,
    gaussianTail_zero] <;> norm_num

end GaussianFour
