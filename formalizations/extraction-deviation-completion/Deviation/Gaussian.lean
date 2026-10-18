import Spectrum.Probability
import Mathlib.Probability.CDF

open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory ProbabilityTheory

namespace ExtractionDeviation
noncomputable section

/-- The actual centred Gaussian CDF; variance, not standard deviation, is the parameter. -/
def gaussianCDF (v : ℝ≥0) (x : ℝ) : ℝ := (gaussianReal 0 v).real (Iic x)

theorem gaussianCDF_eq_cdf (v : ℝ≥0) (x : ℝ) :
    gaussianCDF v x = cdf (gaussianReal 0 v) x := (cdf_eq_real _ _).symm

theorem gaussianCDF_mono (v : ℝ≥0) : Monotone (gaussianCDF v) := by
  simpa only [funext (gaussianCDF_eq_cdf v)] using (monotone_cdf (gaussianReal 0 v))

theorem gaussianCDF_strictMono (v : ℝ≥0) (hv : v ≠ 0) : StrictMono (gaussianCDF v) := by
  intro x y hxy
  have hpos : 0 < (gaussianReal 0 v).real (Ioc x y) := by
    apply ENNReal.toReal_pos
    · intro hzero
      have hvol := gaussianReal_absolutelyContinuous' 0 hv hzero
      have hyx : y ≤ x := by
        simpa only [Real.volume_Ioc, ENNReal.ofReal_eq_zero, sub_nonpos] using hvol
      exact (not_le_of_gt hxy) hyx
    · exact measure_ne_top _ _
  have hd : (gaussianReal 0 v).real (Ioc x y) = gaussianCDF v y - gaussianCDF v x := by
    rw [← Iic_sdiff_Iic, measureReal_sdiff (Iic_subset_Iic.mpr hxy.le) measurableSet_Iic]
    rfl
  linarith

theorem gaussianCDF_continuous (v : ℝ≥0) (hv : v ≠ 0) : Continuous (gaussianCDF v) := by
  let f := cdf (gaussianReal 0 v)
  letI := nullSingletonClass_gaussianReal (μ := 0) hv
  have heq : gaussianCDF v = f := funext (gaussianCDF_eq_cdf v)
  rw [heq]
  apply continuous_iff_continuousAt.mpr
  intro x
  apply f.mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [f.rightLim_eq]
  have hs : ENNReal.ofReal (f x - Function.leftLim f x) = 0 := by
    rw [← f.measure_singleton, measure_cdf]
    exact measure_singleton x
  have hle : f x ≤ Function.leftLim f x := sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hs)
  exact le_antisymm (f.mono.leftLim_le le_rfl) hle

theorem gaussianCDF_tendsto_atBot (v : ℝ≥0) :
    Tendsto (gaussianCDF v) atBot (𝓝 0) := by
  simpa only [funext (gaussianCDF_eq_cdf v)] using tendsto_cdf_atBot (gaussianReal 0 v)

theorem gaussianCDF_tendsto_atTop (v : ℝ≥0) :
    Tendsto (gaussianCDF v) atTop (𝓝 1) := by
  simpa only [funext (gaussianCDF_eq_cdf v)] using tendsto_cdf_atTop (gaussianReal 0 v)

theorem gaussianCDF_exists_unique (v : ℝ≥0) (hv : v ≠ 0) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1) : ∃! x, gaussianCDF v x = ε := by
  obtain ⟨a,ha⟩ := ((gaussianCDF_tendsto_atBot v).eventually (Iio_mem_nhds hε)).exists
  obtain ⟨b,hb⟩ := ((gaussianCDF_tendsto_atTop v).eventually (Ioi_mem_nhds hε')).exists
  obtain ⟨x,hx⟩ := mem_range_of_exists_le_of_exists_ge (gaussianCDF_continuous v hv)
    ⟨a,ha.le⟩ ⟨b,hb.le⟩
  refine ⟨x,hx,?_⟩
  intro y hy
  exact (gaussianCDF_strictMono v hv).injective (hy.trans hx.symm)

/-- The Gaussian inverse is defined by the unique actual CDF preimage on `(0,1)`. -/
def gaussianQuantile (v : ℝ≥0) (hv : v ≠ 0) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) : ℝ :=
  (gaussianCDF_exists_unique v hv ε hε hε').choose

theorem gaussianCDF_quantile (v : ℝ≥0) (hv : v ≠ 0) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1) :
    gaussianCDF v (gaussianQuantile v hv ε hε hε') = ε :=
  (gaussianCDF_exists_unique v hv ε hε hε').choose_spec.1

theorem gaussianCDF_lt_iff (v : ℝ≥0) (hv : v ≠ 0) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1) (x : ℝ) :
    gaussianCDF v x < ε ↔ x < gaussianQuantile v hv ε hε hε' := by
  simpa only [gaussianCDF_quantile v hv ε hε hε'] using
    ((gaussianCDF_strictMono v hv).lt_iff_lt (a := x)
      (b := gaussianQuantile v hv ε hε hε'))

theorem gaussianCDF_le_iff (v : ℝ≥0) (hv : v ≠ 0) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1) (x : ℝ) :
    gaussianCDF v x ≤ ε ↔ x ≤ gaussianQuantile v hv ε hε hε' := by
  simpa only [gaussianCDF_quantile v hv ε hε hε'] using
    ((gaussianCDF_strictMono v hv).le_iff_le (a := x)
      (b := gaussianQuantile v hv ε hε hε'))

theorem gaussianCDF_neg (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    gaussianCDF v (-x) = 1 - gaussianCDF v x := by
  letI := nullSingletonClass_gaussianReal (μ := 0) hv
  have hmap : (gaussianReal 0 v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := v))
  have hpre : (fun x : ℝ => -x) ⁻¹' Iic (-x) = Ici x := by
    ext y
    simp only [mem_preimage, mem_Iic, neg_le_neg_iff, mem_Ici]
  have heq : gaussianCDF v (-x) = (gaussianReal 0 v).real (Ici x) := by
    unfold gaussianCDF Measure.real
    conv_lhs => rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic, hpre]
  rw [heq]
  have hc := measureReal_compl (μ := gaussianReal 0 v) (s := Iio x) measurableSet_Iio
  have ha : (gaussianReal 0 v).real (Iio x) = gaussianCDF v x := by
    exact measureReal_congr (Iio_ae_eq_Iic (μ := gaussianReal 0 v))
  simpa only [compl_Iio, ha, measureReal_def, measure_univ, ENNReal.toReal_one] using hc

theorem gaussianQuantile_compl (v : ℝ≥0) (hv : v ≠ 0) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1) :
    gaussianQuantile v hv (1-ε) (by linarith) (by linarith) =
      -gaussianQuantile v hv ε hε hε' := by
  apply (gaussianCDF_strictMono v hv).injective
  rw [gaussianCDF_quantile, gaussianCDF_neg v hv, gaussianCDF_quantile]

theorem gaussianCDF_scale (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    gaussianCDF v x = gaussianCDF 1 (x / Real.sqrt v) := by
  have hvR : 0 < (v:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs : 0 < Real.sqrt (v:ℝ) := Real.sqrt_pos.mpr hvR
  have hvar : NNReal.mk ((Real.sqrt (v:ℝ))^2) (sq_nonneg _) * 1 = v := by
    ext
    simp [Real.sq_sqrt hvR.le]
  have hmap : (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt (v:ℝ) * y) =
      gaussianReal 0 v := by
    simpa only [mul_zero, hvar] using
      (gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt (v:ℝ)))
  unfold gaussianCDF Measure.real
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext y
  change Real.sqrt (v:ℝ) * y ≤ x ↔ y ≤ x / Real.sqrt (v:ℝ)
  rw [mul_comm]
  exact (le_div_iff₀ hs).symm

theorem gaussianQuantile_scale (v : ℝ≥0) (hv : v ≠ 0) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1) :
    gaussianQuantile v hv ε hε hε' =
      Real.sqrt (v:ℝ) * gaussianQuantile 1 one_ne_zero ε hε hε' := by
  have hs : Real.sqrt (v:ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))
  apply (gaussianCDF_strictMono v hv).injective
  rw [gaussianCDF_quantile, gaussianCDF_scale v hv, mul_div_cancel_left₀ _ hs,
    gaussianCDF_quantile]

end
end ExtractionDeviation
