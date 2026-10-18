import Deviation.GaussianRegularity
import Deviation.FiniteQuantile
import Mathlib.MeasureTheory.Integral.Bochner.Set

open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set

namespace ExtractionDeviation
noncomputable section

/-- The signed CDF discrepancy after adding independent noise of law `μ`.
The following results prove the real-space part of Esseen smoothing; a
band-limited kernel and the Fourier inversion estimate are still separate. -/
def smoothedCDFDifference (F G : ℝ → ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y,F (x-y)-G (x-y) ∂μ

theorem bounded_difference_integrable (F G : ℝ → ℝ) (hF : Measurable F)
    (hG : Measurable G) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (D : ℝ) (hD : ∀ x,|F x-G x|≤D) (z : ℝ) :
    Integrable (fun y => F (z-y)-G (z-y)) μ := by
  apply (integrable_const D).mono'
    (((hF.comp (measurable_const.sub measurable_id)).sub
      (hG.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
  exact ae_of_all _ (fun y => by
    change ‖F (z-y)-G (z-y)‖≤D
    simpa only [Real.norm_eq_abs] using hD (z-y))

theorem cdf_noise_upper_pointwise (F G : ℝ → ℝ) (hF : Monotone F)
    (M : ℝ≥0) (hG : LipschitzWith M G) (D a : ℝ) (ha : 0≤a)
    (hD : ∀ x,|F x-G x|≤D) (x y : ℝ) :
    F x-G x ≤ F (x+a-y)-G (x+a-y)+(M:ℝ)*(a+|y|)+
      (Ioi a).indicator (fun _ => 2*D) y := by
  have hM : 0≤(M:ℝ)*(a+|y|) := by positivity
  by_cases hy : y≤a
  · have hFy := hF (show x≤x+a-y by linarith)
    have hGxy := hG.norm_sub_le (x+a-y) x
    have hd : |(x+a-y)-x|≤a+|y| := by
      calc
        _ = |a+ -y| := by congr 1; ring
        _ ≤ |a|+|-y| := abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg ha,abs_neg]
    rw [Real.norm_eq_abs,Real.norm_eq_abs] at hGxy
    have hGdiff := (le_abs_self (G (x+a-y)-G x)).trans
      (hGxy.trans (mul_le_mul_of_nonneg_left hd M.coe_nonneg))
    rw [indicator_of_notMem (show y∉Ioi a by simpa using not_lt.mpr hy)]
    linarith
  · have hDx := (abs_le.mp (hD x)).2
    have hDy := (abs_le.mp (hD (x+a-y))).1
    rw [indicator_of_mem (show y∈Ioi a from lt_of_not_ge hy)]
    linarith

theorem cdf_noise_lower_pointwise (F G : ℝ → ℝ) (hF : Monotone F)
    (M : ℝ≥0) (hG : LipschitzWith M G) (D a : ℝ) (ha : 0≤a)
    (hD : ∀ x,|F x-G x|≤D) (x y : ℝ) :
    -(F x-G x) ≤ -(F (x-a-y)-G (x-a-y))+(M:ℝ)*(a+|y|)+
      (Iio (-a)).indicator (fun _ => 2*D) y := by
  have hM : 0≤(M:ℝ)*(a+|y|) := by positivity
  by_cases hy : -a≤y
  · have hFy := hF (show x-a-y≤x by linarith)
    have hGxy := hG.norm_sub_le x (x-a-y)
    have hd : |x-(x-a-y)|≤a+|y| := by
      calc
        _ = |a+y| := by congr 1; ring
        _ ≤ |a|+|y| := abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg ha]
    rw [Real.norm_eq_abs,Real.norm_eq_abs] at hGxy
    have hGdiff := (le_abs_self (G x-G (x-a-y))).trans
      (hGxy.trans (mul_le_mul_of_nonneg_left hd M.coe_nonneg))
    rw [indicator_of_notMem (show y∉Iio (-a) by simpa using not_lt.mpr hy)]
    linarith
  · have hDx := (abs_le.mp (hD x)).1
    have hDy := (abs_le.mp (hD (x-a-y))).2
    rw [indicator_of_mem (show y∈Iio (-a) from lt_of_not_ge hy)]
    linarith

theorem integrate_noise_comparison (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : ℝ → ℝ) (hg : Integrable g μ) (habs : Integrable (fun y : ℝ => |y|) μ)
    (E : Set ℝ) (hE : MeasurableSet E) (A D a : ℝ) (M : ℝ≥0)
    (h : ∀ y,A≤g y+(M:ℝ)*(a+|y|)+E.indicator (fun _ => 2*D) y) :
    A≤(∫ y,g y ∂μ)+(M:ℝ)*(a+∫ y,|y| ∂μ)+2*D*μ.real E := by
  have hca : Integrable (fun y : ℝ => a+|y|) μ := (integrable_const a).add habs
  have hm : Integrable (fun y : ℝ => (M:ℝ)*(a+|y|)) μ := hca.const_mul (M:ℝ)
  have hgm : Integrable (fun y : ℝ => g y+(M:ℝ)*(a+|y|)) μ := hg.add hm
  have he := (integrable_const (2*D) (μ:=μ)).indicator hE
  have hi := integral_mono (integrable_const A) ((hg.add hm).add he) h
  change (∫ _ : ℝ,A ∂μ)≤∫ y,g y+(M:ℝ)*(a+|y|)+E.indicator (fun _ => 2*D) y ∂μ at hi
  rw [integral_add hgm he,integral_add hg hm] at hi
  simp only [integral_const_mul,integral_add (integrable_const a) habs,integral_const,
    probReal_univ,integral_indicator_const _ hE,smul_eq_mul,one_mul,
    mul_comm (μ.real E) (2*D)] at hi
  exact hi

/-- A quantitative real-space smoothing estimate. The discrepancy `D` appears
only through the explicit noise tails, allowing a strict contraction when
their common bound is less than one half. -/
theorem noise_smoothing_abs_error_le (F G : ℝ → ℝ) (hF : Monotone F)
    (hmF : Measurable F) (M : ℝ≥0) (hG : LipschitzWith M G)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (habs : Integrable (fun y : ℝ => |y|) μ)
    (D a η δ : ℝ) (ha : 0≤a) (hD : ∀ x,|F x-G x|≤D)
    (hηu : μ.real (Ioi a)≤η) (hηl : μ.real (Iio (-a))≤η)
    (hsm : ∀ z,|smoothedCDFDifference F G μ z|≤δ) (x : ℝ) :
    |F x-G x|≤δ+(M:ℝ)*(a+∫ y,|y| ∂μ)+2*D*η := by
  have hD0 : 0≤D := (abs_nonneg _).trans (hD 0)
  apply abs_le.mpr
  constructor
  · have hi := integrate_noise_comparison μ _
      (bounded_difference_integrable F G hmF hG.continuous.measurable μ D hD (x-a)).neg
      habs _ measurableSet_Iio (-(F x-G x)) D a M
      (cdf_noise_lower_pointwise F G hF M hG D a ha hD x)
    have hs := (abs_le.mp (hsm (x-a))).1
    change -(F x-G x)≤(∫ y,-(F (x-a-y)-G (x-a-y)) ∂μ)+
      (M:ℝ)*(a+∫ y,|y| ∂μ)+2*D*μ.real (Iio (-a)) at hi
    rw [integral_neg] at hi
    have ht := mul_le_mul_of_nonneg_left hηl (by positivity : 0≤2*D)
    change -δ≤∫ y,F (x-a-y)-G (x-a-y) ∂μ at hs
    linarith
  · have hi := integrate_noise_comparison μ _
      (bounded_difference_integrable F G hmF hG.continuous.measurable μ D hD (x+a))
      habs _ measurableSet_Ioi (F x-G x) D a M
      (cdf_noise_upper_pointwise F G hF M hG D a ha hD x)
    have hs := (abs_le.mp (hsm (x+a))).2
    have ht := mul_le_mul_of_nonneg_left hηu (by positivity : 0≤2*D)
    change (∫ y,F (x+a-y)-G (x+a-y) ∂μ)≤δ at hs
    linarith

/-- The actual uniform CDF discrepancy, rather than an externally supplied
error certificate. -/
def cdfSupError (F G : ℝ → ℝ) : ℝ := sSup (range (fun x => |F x-G x|))

theorem cdfSupError_bddAbove (F G : ℝ → ℝ)
    (hF : ∀ x,0≤F x ∧ F x≤1) (hG : ∀ x,0≤G x ∧ G x≤1) :
    BddAbove (range (fun x => |F x-G x|)) := by
  refine ⟨1,?_⟩
  rintro _ ⟨x,rfl⟩
  exact abs_le.mpr ⟨by linarith [(hF x).1,(hG x).2],
    by linarith [(hF x).2,(hG x).1]⟩

theorem le_cdfSupError (F G : ℝ → ℝ)
    (hF : ∀ x,0≤F x ∧ F x≤1) (hG : ∀ x,0≤G x ∧ G x≤1) (x : ℝ) :
    |F x-G x|≤cdfSupError F G :=
  le_csSup (cdfSupError_bddAbove F G hF hG) (mem_range_self x)

/-- The real-space smoothing inequality is closed using the actual supremum;
there is no assumed bound on the desired unsmoothed discrepancy. -/
theorem cdfSupError_noise_smoothing (F G : ℝ → ℝ) (hF : Monotone F)
    (hF01 : ∀ x,0≤F x ∧ F x≤1) (hG01 : ∀ x,0≤G x ∧ G x≤1)
    (M : ℝ≥0) (hG : LipschitzWith M G)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (habs : Integrable (fun y : ℝ => |y|) μ)
    (a η δ : ℝ) (ha : 0≤a) (hη : η<1/2)
    (hηu : μ.real (Ioi a)≤η) (hηl : μ.real (Iio (-a))≤η)
    (hsm : ∀ z,|smoothedCDFDifference F G μ z|≤δ) :
    cdfSupError F G≤(δ+(M:ℝ)*(a+∫ y,|y| ∂μ))/(1-2*η) := by
  have hpoint := noise_smoothing_abs_error_le F G hF hF.measurable M hG μ habs
    (cdfSupError F G) a η δ ha (le_cdfSupError F G hF01 hG01) hηu hηl hsm
  have hsup : cdfSupError F G≤δ+(M:ℝ)*(a+∫ y,|y| ∂μ)+2*cdfSupError F G*η := by
    apply csSup_le (range_nonempty _) 
    rintro _ ⟨x,rfl⟩
    exact hpoint x
  apply (le_div_iff₀ (show 0<1-2*η by linarith)).mpr
  nlinarith

theorem firstMoment_tail_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (habs : Integrable (fun y : ℝ => |y|) μ) (E : Set ℝ) (hE : MeasurableSet E)
    (a : ℝ) (hEa : ∀ y∈E,a≤|y|) :
    a*μ.real E≤∫ y,|y| ∂μ := by
  have hi := integral_mono ((integrable_const a (μ:=μ)).indicator hE) habs
    (show E.indicator (fun _ => a)≤fun y : ℝ => |y| from fun y => by
      by_cases hy : y∈E
      · rw [indicator_of_mem hy]; exact hEa y hy
      · rw [indicator_of_notMem hy]; exact abs_nonneg _)
  rw [integral_indicator_const a hE,smul_eq_mul,mul_comm] at hi
  exact hi

/-- The two noise tail bounds are obtained from the actual first moment,
leaving no externally supplied tail estimate. -/
theorem cdfSupError_firstMoment_smoothing (F G : ℝ → ℝ) (hF : Monotone F)
    (hF01 : ∀ x,0≤F x ∧ F x≤1) (hG01 : ∀ x,0≤G x ∧ G x≤1)
    (M : ℝ≥0) (hG : LipschitzWith M G)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (habs : Integrable (fun y : ℝ => |y|) μ)
    (a δ : ℝ) (ha : 0<a) (hm : 4*(∫ y,|y| ∂μ)≤a)
    (hsm : ∀ z,|smoothedCDFDifference F G μ z|≤δ) :
    cdfSupError F G≤2*δ+2*(M:ℝ)*(a+∫ y,|y| ∂μ) := by
  have hu := firstMoment_tail_le μ habs (Ioi a) measurableSet_Ioi a
    (fun y hy => hy.le.trans (le_abs_self y))
  have hl := firstMoment_tail_le μ habs (Iio (-a)) measurableSet_Iio a
    (fun y hy => by
      have h := neg_le_abs y
      change y < -a at hy
      linarith)
  have h := cdfSupError_noise_smoothing F G hF hF01 hG01 M hG μ habs
    a (1/4) δ ha.le (by norm_num) (by nlinarith) (by nlinarith) hsm
  norm_num at h
  linarith

variable {ι : Type*} [Fintype ι]

theorem finiteCDF_mem_unitInterval (p f : ι → ℝ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (x : ℝ) : 0≤finiteCDF p f x ∧ finiteCDF p f x≤1 := by
  unfold finiteCDF
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact hp i
    · exact le_rfl
  · calc
      _ ≤ ∑ i,p i := Finset.sum_le_sum (fun i _ => by split_ifs <;> simpa using hp i)
      _ = 1 := hs

/-- A finite-law Gaussian smoothing theorem instantiated at the actual finite
CDF. The smoothing term is explicitly a convolution integral, not a disguised
Berry--Esseen conclusion. -/
theorem finiteCDF_gaussian_noise_smoothing (p f : ι → ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (habs : Integrable (fun y : ℝ => |y|) μ)
    (a η δ : ℝ) (ha : 0≤a) (hη : η<1/2)
    (hηu : μ.real (Ioi a)≤η) (hηl : μ.real (Iio (-a))≤η)
    (hsm : ∀ z,|smoothedCDFDifference (finiteCDF p f) (gaussianCDF 1) μ z|≤δ) :
    cdfSupError (finiteCDF p f) (gaussianCDF 1)≤
      (δ+gaussianPeak*(a+∫ y,|y| ∂μ))/(1-2*η) := by
  have hG01 : ∀ x,0≤gaussianCDF 1 x ∧ gaussianCDF 1 x≤1 := by
    intro x
    exact ⟨measureReal_nonneg,measureReal_le_one⟩
  have h := cdfSupError_noise_smoothing (finiteCDF p f) (gaussianCDF 1)
    (finiteCDF_mono p f hp) (finiteCDF_mem_unitInterval p f hp hs) hG01
    gaussianPeak.toNNReal gaussianCDF_lipschitz μ habs a η δ ha hη hηu hηl hsm
  simpa only [Real.coe_toNNReal _ gaussianPeak_pos.le] using h

end
end ExtractionDeviation
