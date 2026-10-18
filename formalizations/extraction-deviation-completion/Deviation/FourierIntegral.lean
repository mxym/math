import Deviation.NormalizedDamping
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

open scoped BigOperators NNReal ENNReal Topology
open ExtractionSpectrum MeasureTheory ProbabilityTheory Filter Set

namespace ExtractionDeviation
noncomputable section

/-- An absolute finite Gaussian moment; it does not depend on the input law,
alphabet, variance, or block length. -/
def fourierGaussianMoment : ℝ := ∫ t : ℝ, t^2*Real.exp (-t^2/8)

theorem fourierGaussianMoment_integrable :
    Integrable (fun t : ℝ => t^2*Real.exp (-t^2/8)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/8)
    (by norm_num : (-1:ℝ)<2)
  simpa only [show (2:ℝ)=(2:ℕ) by norm_num,Real.rpow_natCast,
    show ∀ t : ℝ, -(1/8)*t^2 = -t^2/8 by intro t; ring] using h

theorem fourierGaussianMoment_nonneg : 0 ≤ fourierGaussianMoment :=
  integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteChar_continuous (p f : ι → ℝ) : Continuous (finiteChar p f) := by
  unfold finiteChar
  fun_prop

def normalizedFourierIntegrand (p f : ι → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ‖finiteChar (iidLaw p k) (standardizedWordSum p f k) t-gaussianChar 1 t‖/|t|

theorem normalizedFourierIntegrand_measurable (p f : ι → ℝ) (k : ℕ) :
    Measurable (normalizedFourierIntegrand p f k) := by
  unfold normalizedFourierIntegrand
  apply Measurable.div
  · apply Continuous.measurable
    apply Continuous.norm
    exact (finiteChar_continuous _ _).sub (by unfold gaussianChar; fun_prop)
  · exact continuous_abs.measurable

theorem normalizedFourierIntegrand_nonneg (p f : ι → ℝ) (k : ℕ) (t : ℝ) :
    0 ≤ normalizedFourierIntegrand p f k t := div_nonneg (norm_nonneg _) (abs_nonneg _)

theorem normalizedFourierIntegrand_bound (p f : ι → ℝ) (hp : ∀ i,0 ≤ p i)
    (hs : ∑ i,p i=1) (hv : 0<finiteVariance p f) (k : ℕ) (hk : 2≤k)
    (t : ℝ) (ht : 16*lyapunovRatio p f k*|t|≤1) :
    normalizedFourierIntegrand p f k t ≤
      (5*lyapunovRatio p f k)*(t^2*Real.exp (-t^2/8)) := by
  by_cases ht0 : t=0
  · simp [normalizedFourierIntegrand,ht0]
  have hat : 0 < |t| := abs_pos.mpr ht0
  apply (div_le_iff₀ hat).mpr
  have h := standardized_iid_fourier_damped p f hp hs hv k hk t ht
  apply h.trans_eq
  rw [show |t|^3=|t|^2*|t| by ring,sq_abs]
  ring

/-- The truncated Esseen Fourier integral is bounded by a universal constant
times the Lyapunov ratio.  This is the Fourier estimate, not yet the separate
Fourier-to-CDF smoothing inequality. -/
theorem normalizedFourierIntegral_bound (p f : ι → ℝ) (hp : ∀ i,0 ≤ p i)
    (hs : ∑ i,p i=1) (hv : 0<finiteVariance p f) (k : ℕ) (hk : 2≤k)
    (R : ℝ) (hR : 0<R) (hwindow : 16*lyapunovRatio p f k*R≤1) :
    IntegrableOn (normalizedFourierIntegrand p f k) (Ioc (-R) R) ∧
    (∫ t in Ioc (-R) R,normalizedFourierIntegrand p f k t) ≤
      (5*lyapunovRatio p f k)*fourierGaussianMoment := by
  have hβ : 0≤lyapunovRatio p f k :=
    (lyapunovRatio_pos p f hp hs hv k (by omega)).le
  have hbound : ∀ t ∈ Ioc (-R) R, normalizedFourierIntegrand p f k t ≤
      (5*lyapunovRatio p f k)*(t^2*Real.exp (-t^2/8)) := by
    intro t ht
    have hat : |t|≤R := abs_le.mpr ⟨ht.1.le,ht.2⟩
    apply normalizedFourierIntegrand_bound p f hp hs hv k hk t
    exact (mul_le_mul_of_nonneg_left hat (by positivity)).trans hwindow
  have hg := fourierGaussianMoment_integrable.const_mul (5*lyapunovRatio p f k)
  have hfi : IntegrableOn (normalizedFourierIntegrand p f k) (Ioc (-R) R) := by
    apply hg.integrableOn.mono' (normalizedFourierIntegrand_measurable p f k).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (normalizedFourierIntegrand_nonneg p f k t)]
    exact hbound t ht
  refine ⟨hfi,?_⟩
  calc
    _ ≤ ∫ t in Ioc (-R) R,(5*lyapunovRatio p f k)*(t^2*Real.exp (-t^2/8)) :=
      setIntegral_mono_on hfi hg.integrableOn measurableSet_Ioc hbound
    _ ≤ ∫ t : ℝ,(5*lyapunovRatio p f k)*(t^2*Real.exp (-t^2/8)) :=
      setIntegral_le_integral hg (ae_of_all _ (fun _ => by positivity))
    _ = _ := integral_const_mul _ _

/-- The maximal explicit frequency window is selected from the actual moments,
and its truncation cost is exactly linear in the Lyapunov ratio. -/
theorem normalizedFourierIntegral_lyapunov_window (p f : ι → ℝ)
    (hp : ∀ i,0 ≤ p i) (hs : ∑ i,p i=1) (hv : 0<finiteVariance p f)
    (k : ℕ) (hk : 2≤k) :
    let R := (16*lyapunovRatio p f k)⁻¹
    0<R ∧ R⁻¹=16*lyapunovRatio p f k ∧
    (∫ t in Ioc (-R) R,normalizedFourierIntegrand p f k t) ≤
      (5*lyapunovRatio p f k)*fourierGaussianMoment := by
  dsimp only
  have hβ := lyapunovRatio_pos p f hp hs hv k (by omega)
  have h16 : 0<16*lyapunovRatio p f k := by positivity
  refine ⟨inv_pos.mpr h16,inv_inv _,?_⟩
  exact (normalizedFourierIntegral_bound p f hp hs hv k hk _ (inv_pos.mpr h16)
    (by rw [mul_inv_cancel₀ (ne_of_gt h16)])).2

end
end ExtractionDeviation
