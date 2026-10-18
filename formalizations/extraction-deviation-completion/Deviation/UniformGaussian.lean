import Deviation.GaussianRegularity
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter Metric

namespace ExtractionDeviation
noncomputable section

theorem thickening_Iic_subset (δ y : ℝ) : thickening δ (Iic y) ⊆ Iic (y+δ) := by
  intro x hx
  obtain ⟨z,hz,hxz⟩ := mem_thickening_iff.mp hx
  rw [Real.dist_eq] at hxz
  have h := (abs_lt.mp hxz).2
  change z ≤ y at hz
  change x ≤ y+δ
  linarith

/-- A finite CDF smoothing estimate in terms of the Lévy--Prokhorov distance.
This estimate is proved; it is distinct from the missing Esseen Fourier
smoothing inequality required for a Berry--Esseen `k^(-1/2)` CDF rate. -/
theorem gaussian_cdf_error_of_levyProkhorov_lt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ)
    (hLP : levyProkhorovEDist μ (gaussianReal 0 1) < ENNReal.ofReal δ) (y : ℝ) :
    |μ.real (Iic y)-gaussianCDF 1 y| ≤ (gaussianPeak+1)*δ := by
  have hU0 := left_measure_le_of_levyProkhorovEDist_lt hLP (B := Iic y) measurableSet_Iic
  have hL0 := right_measure_le_of_levyProkhorovEDist_lt hLP (B := Iic (y-δ)) measurableSet_Iic
  rw [ENNReal.toReal_ofReal hδ.le] at hU0 hL0
  have hUe : μ (Iic y) ≤ gaussianReal 0 1 (Iic (y+δ))+ENNReal.ofReal δ :=
    hU0.trans (add_le_add (measure_mono (thickening_Iic_subset δ y)) le_rfl)
  have hsub : thickening δ (Iic (y-δ)) ⊆ Iic y := by
    simpa only [sub_add_cancel] using thickening_Iic_subset δ (y-δ)
  have hLe : gaussianReal 0 1 (Iic (y-δ)) ≤ μ (Iic y)+ENNReal.ofReal δ :=
    hL0.trans (add_le_add (measure_mono hsub) le_rfl)
  have hU := ENNReal.toReal_mono (by finiteness) hUe
  have hL := ENNReal.toReal_mono (by finiteness) hLe
  rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hδ.le] at hU hL
  change μ.real (Iic y) ≤ gaussianCDF 1 (y+δ)+δ at hU
  change gaussianCDF 1 (y-δ) ≤ μ.real (Iic y)+δ at hL
  have hgU := gaussianCDF_sub_le_peak y (y+δ) (by linarith)
  have hgL := gaussianCDF_sub_le_peak (y-δ) y (by linarith)
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Gaussian weak convergence implies CDF convergence uniformly over every
real threshold, including arbitrarily varying or diverging threshold sequences. -/
theorem gaussian_cdf_uniform_of_weak (μ : ℕ → ProbabilityMeasure ℝ)
    (hμ : Tendsto μ atTop (𝓝 (⟨gaussianReal 0 1,by infer_instance⟩ : ProbabilityMeasure ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ y : ℝ,
      |(μ k : Measure ℝ).real (Iic y)-gaussianCDF 1 y| < ε := by
  let G : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1,by infer_instance⟩
  have hLP := LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto G |>.comp hμ
  have hd := tendsto_iff_dist_tendsto_zero.mp hLP
  intro ε hε
  let δ := ε/(2*(gaussianPeak+1))
  have hPeak := gaussianPeak_pos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdlt := hd.eventually (Iio_mem_nhds hδ)
  filter_upwards [hdlt] with k hk
  have hED : levyProkhorovEDist (μ k : Measure ℝ) (gaussianReal 0 1) < ENNReal.ofReal δ := by
    apply (ENNReal.toReal_lt_toReal (levyProkhorovEDist_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hδ.le]
    exact hk
  intro y
  have h := gaussian_cdf_error_of_levyProkhorov_lt (μ k : Measure ℝ) δ hδ hED y
  have hP : gaussianPeak+1 ≠ 0 := by linarith
  have heq : (gaussianPeak+1)*δ = ε/2 := by dsimp [δ]; field_simp
  rw [heq] at h
  linarith

end
end ExtractionDeviation
