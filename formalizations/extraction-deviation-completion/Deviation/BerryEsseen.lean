import Deviation.DampedSmoothing
import Deviation.TriangularInformation

open scoped BigOperators NNReal ENNReal Topology MeasureTheory
open MeasureTheory ProbabilityTheory Filter Set ExtractionSpectrum

namespace ExtractionDeviation
noncomputable section

/-- One fixed explicit finite Berry--Esseen constant. Its two integral
components are proved finite in `FourierIntegral` and `SincKernel`. No claim of
an optimized numerical constant is made. -/
def berryEsseenConstant : ℝ := 1+5*fourierGaussianMoment/sincKernelIntegral+
  128*gaussianPeak*(5*sincNoiseMoment+1)

theorem berryEsseenConstant_ge_one : 1≤berryEsseenConstant := by
  have h1 : 0≤5*fourierGaussianMoment/sincKernelIntegral :=
    div_nonneg (mul_nonneg (by norm_num) fourierGaussianMoment_nonneg) sincKernelIntegral_pos.le
  have h2 : 0≤128*gaussianPeak*(5*sincNoiseMoment+1) := by
    positivity [gaussianPeak_pos,sincNoiseMoment_nonneg]
  unfold berryEsseenConstant
  linarith

theorem standardGaussian_firstMoment_integrable :
    Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) := by
  have hi : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)
  simpa only [Real.norm_eq_abs,Function.id_def] using hi.norm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem standardizedIIDMeasure_firstMoment_integrable (p f : ι → ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1) (k : ℕ) :
    Integrable (fun z : ℝ => |z|) (standardizedIIDMeasure p f hp hs k) := by
  rw [standardizedIIDMeasure,integrable_map_measure continuous_abs.aestronglyMeasurable
    (measurable_of_countable _).aemeasurable]
  let C := ∑ w : Fin k → ι,|standardizedWordSum p f k w|
  apply (integrable_const C).mono' ((measurable_of_countable _).aestronglyMeasurable)
  apply ae_of_all
  intro w
  change ‖|standardizedWordSum p f k w|‖≤C
  rw [Real.norm_eq_abs,abs_abs]
  exact Finset.single_le_sum (f:=fun v : Fin k → ι => |standardizedWordSum p f k v|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ w)

theorem finite_iid_berryEsseen_sup_ge_two (p f : ι → ℝ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (hv : 0<finiteVariance p f) (k : ℕ) (hk : 2≤k) :
    cdfSupError (measureCDF (standardizedIIDMeasure p f hp hs k)) (gaussianCDF 1)≤
      berryEsseenConstant*lyapunovRatio p f k := by
  let μ := standardizedIIDMeasure p f hp hs k
  let β := lyapunovRatio p f k
  let R := (64*β)⁻¹
  have hβ : 0<β := lyapunovRatio_pos p f hp hs hv k (by omega)
  have hR : 0<R := inv_pos.mpr (by positivity)
  have hwindow : 64*β*R≤1 := by dsimp [R]; rw [mul_inv_cancel₀ (by positivity)]
  have hdamp : ∀ u : ℝ,16*β*|u|≤1 → ‖charFun μ u-charFun (gaussianReal 0 1) u‖≤
      5*β*|u|^3*Real.exp (-u^2/8) := by
    intro u hu
    rw [← gaussianChar_eq_charFun, charFun_standardizedIIDMeasure]
    exact standardized_iid_fourier_damped p f hp hs hv k hk u hu
  have hsm := smoothedCDFDifference_damped_bound μ (gaussianReal 0 1)
    (standardizedIIDMeasure_firstMoment_integrable p f hp hs k)
    standardGaussian_firstMoment_integrable β R hβ.le hR hwindow hdamp
  have h := sinc_noise_gaussian_smoothing (measureCDF μ) (measureCDF_mono μ)
    (measureCDF_mem_unitInterval μ) R ((5*β*fourierGaussianMoment)/(2*sincKernelIntegral)) hR hsm
  apply h.trans
  have hI : sincKernelIntegral≠0 := ne_of_gt sincKernelIntegral_pos
  have hR0 : 64*β≠0 := by positivity
  have hid : 2*((5*β*fourierGaussianMoment)/(2*sincKernelIntegral))+
      (2*gaussianPeak*(5*sincNoiseMoment+1))/R=
      (berryEsseenConstant-1)*β := by
    dsimp [R,berryEsseenConstant]
    field_simp
    ring
  rw [hid]
  nlinarith

/-- Full finite-block Berry--Esseen bound for the actual finite iid measure.
All positive block lengths are covered, with zero-probability atoms retained.
No CDF approximation, CLT statement, or smoothing certificate is a premise. -/
theorem finite_iid_berryEsseen_sup (p f : ι → ℝ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (hv : 0<finiteVariance p f) (k : ℕ) (hk : 0<k) :
    cdfSupError (measureCDF (standardizedIIDMeasure p f hp hs k)) (gaussianCDF 1)≤
      berryEsseenConstant*lyapunovRatio p f k := by
  by_cases hk2 : 2≤k
  · exact finite_iid_berryEsseen_sup_ge_two p f hp hs hv k hk2
  have hk1 : k=1 := by omega
  subst k
  have hβ : 1≤lyapunovRatio p f 1 := by
    simpa using lyapunovRatio_ge_inv_sqrt p f hp hs hv 1 (by norm_num)
  have hsup : cdfSupError (measureCDF (standardizedIIDMeasure p f hp hs 1)) (gaussianCDF 1)≤1 := by
    apply csSup_le (range_nonempty _)
    rintro _ ⟨x,rfl⟩
    have hF := measureCDF_mem_unitInterval (standardizedIIDMeasure p f hp hs 1) x
    have hG : 0≤gaussianCDF 1 x ∧ gaussianCDF 1 x≤1 :=
      ⟨measureReal_nonneg,measureReal_le_one⟩
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hC := berryEsseenConstant_ge_one
  exact hsup.trans (by nlinarith)

theorem finite_iid_berryEsseen (p f : ι → ℝ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (hv : 0<finiteVariance p f) (k : ℕ) (hk : 0<k) (x : ℝ) :
    |(standardizedIIDMeasure p f hp hs k).real (Iic x)-gaussianCDF 1 x|≤
      berryEsseenConstant*lyapunovRatio p f k := by
  have hG : ∀ y,0≤gaussianCDF 1 y ∧ gaussianCDF 1 y≤1 :=
    fun _ => ⟨measureReal_nonneg,measureReal_le_one⟩
  exact (le_cdfSupError _ _ (measureCDF_mem_unitInterval _) hG x).trans
    (finite_iid_berryEsseen_sup p f hp hs hv k hk)

end
end ExtractionDeviation
