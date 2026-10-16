import Deviation.Triangular
import Deviation.UniformGaussian

open scoped BigOperators NNReal ENNReal Topology ComplexOrder
open MeasureTheory ProbabilityTheory Filter Set ExtractionSpectrum Matrix

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem standardizedIIDMeasure_real_Iic (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (k : ℕ) (y : ℝ) :
    (standardizedIIDMeasure p f hp hs k).real (Iic y) =
      finiteCDF (iidLaw p k) (standardizedWordSum p f k) y := by
  have hmap : (standardizedIIDMeasure p f hp hs k).real (Iic y) =
      (finiteMeasure (iidLaw p k) (iidLaw_nonneg p hp k) (iidLaw_sum p hs k)).real
        {w | standardizedWordSum p f k w ≤ y} := by
    unfold standardizedIIDMeasure Measure.real
    rw [Measure.map_apply (measurable_of_countable _) measurableSet_Iic]
    rfl
  rw [hmap,finiteMeasure_real_event]
  rfl

theorem standardizedInformationMeasure_Iic (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < varentropy p) (k : ℕ) (hk : 0 < k) (x : ℝ) :
    (standardizedIIDMeasure p (selfInformation p) hp hs k).real
      (Iic ((x-k*entropy p)/Real.sqrt ((k:ℝ)*varentropy p))) = iidInformationEvent p k x := by
  rw [standardizedIIDMeasure_real_Iic]
  unfold finiteCDF iidInformationEvent
  apply Finset.sum_congr rfl
  intro w hw
  have hsqrt : 0 < Real.sqrt ((k:ℝ)*varentropy p) :=
    Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hk) hv)
  have hiff : standardizedWordSum p (selfInformation p) k w ≤
      (x-k*entropy p)/Real.sqrt ((k:ℝ)*varentropy p) ↔
      (∑ j, -Real.log (p (w j))) ≤ x := by
    rw [standardizedWordSum_eq]
    change ((∑ j, -Real.log (p (w j)))-(k:ℝ)*entropy p)/Real.sqrt ((k:ℝ)*varentropy p) ≤
      (x-k*entropy p)/Real.sqrt ((k:ℝ)*varentropy p) ↔ _
    rw [div_le_div_iff_of_pos_right hsqrt]
    constructor <;> intro h <;> linarith
  simp only [hiff]

def thirdInformationMoment (p : ι → ℝ) : ℝ := thirdAbsoluteMoment p (selfInformation p)

theorem variance_three_halves (v : ℝ) (hv : 0 < v) : v^(3/2:ℝ) = v*Real.sqrt v := by
  rw [show (3/2:ℝ) = 1+1/2 by ring,Real.rpow_add hv,Real.rpow_one,← Real.sqrt_eq_rpow]

variable {a : ℕ → Type*} [∀ k, Fintype (a k)] [∀ k, DecidableEq (a k)]
  [∀ k, MeasurableSpace (a k)] [∀ k, MeasurableSingletonClass (a k)]

/-- The triangular finite iid Gaussian approximation is uniform over all
thresholds. This is a proved qualitative conclusion from an explicit moment
ratio, and permits varying alphabet, observable and variance. -/
theorem triangular_iid_uniform_gaussian
    (p f : (k : ℕ) → a k → ℝ) (hp : ∀ k i, 0 ≤ p k i) (hs : ∀ k, ∑ i, p k i = 1)
    (hv : ∀ k, 0 < finiteVariance (p k) (f k))
    (hLyap : Tendsto (fun k : ℕ => thirdAbsoluteMoment (p k) (f k) /
      (finiteVariance (p k) (f k)*Real.sqrt (finiteVariance (p k) (f k))*Real.sqrt k))
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ y : ℝ,
      |(standardizedIIDMeasure (p k) (f k) (hp k) (hs k) k).real (Iic y)-gaussianCDF 1 y| < ε := by
  exact gaussian_cdf_uniform_of_weak
    (fun k => ⟨standardizedIIDMeasure (p k) (f k) (hp k) (hs k) k,by infer_instance⟩)
    (triangular_iid_probabilityMeasure_gaussian p f hp hs hv hLyap)

/-- A uniform Gaussian approximation to the actual triangular iid information
spectrum. Its sole stochastic hypothesis is the directly computed third-moment
ratio `T/(V^(3/2) sqrt k) → 0`; singular spectra are allowed. -/
theorem triangular_information_uniform_gaussian
    (p : (k : ℕ) → a k → ℝ) (hp : ∀ k i, 0 ≤ p k i) (hs : ∀ k, ∑ i, p k i = 1)
    (hv : ∀ k, 0 < varentropy (p k))
    (hLyap : Tendsto (fun k : ℕ => thirdInformationMoment (p k) /
      ((varentropy (p k))^(3/2:ℝ)*Real.sqrt k)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ x : ℝ,
      |iidInformationEvent (p k) k x-
        gaussianCDF 1 ((x-k*entropy (p k))/Real.sqrt ((k:ℝ)*varentropy (p k)))| < ε := by
  have hLyap' : Tendsto (fun k : ℕ => thirdAbsoluteMoment (p k) (selfInformation (p k)) /
      (varentropy (p k)*Real.sqrt (varentropy (p k))*Real.sqrt k)) atTop (𝓝 0) := by
    apply hLyap.congr'
    filter_upwards with k
    rw [variance_three_halves _ (hv k)]
    rfl
  have h := triangular_iid_uniform_gaussian p (fun k => selfInformation (p k)) hp hs hv hLyap'
  intro ε hε
  filter_upwards [h ε hε,eventually_gt_atTop 0] with k hk hkpos
  intro x
  have hbound := hk ((x-k*entropy (p k))/Real.sqrt ((k:ℝ)*varentropy (p k)))
  rw [standardizedInformationMeasure_Iic (p k) (hp k) (hs k) (hv k) k hkpos x] at hbound
  exact hbound

/-- Arbitrarily moving thresholds are permitted; no convergence of the
standardized threshold is needed for the approximation error to vanish. -/
theorem triangular_information_moving_error
    (p : (k : ℕ) → a k → ℝ) (hp : ∀ k i, 0 ≤ p k i) (hs : ∀ k, ∑ i, p k i = 1)
    (hv : ∀ k, 0 < varentropy (p k))
    (hLyap : Tendsto (fun k : ℕ => thirdInformationMoment (p k) /
      ((varentropy (p k))^(3/2:ℝ)*Real.sqrt k)) atTop (𝓝 0)) (x : ℕ → ℝ) :
    Tendsto (fun k => iidInformationEvent (p k) k (x k)-
      gaussianCDF 1 ((x k-k*entropy (p k))/Real.sqrt ((k:ℝ)*varentropy (p k)))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [triangular_information_uniform_gaussian p hp hs hv hLyap ε hε] with k hk
  simpa only [Real.dist_eq,sub_zero] using hk (x k)

/-- Density spectra with changing dimensions are instantiated internally. The
tensor spectral weights are the actual iid eigenvalue products proved in the
frozen `Spectrum.Tensor` matrix bridge; no spectral approximation is assumed. -/
theorem density_triangular_information_uniform_gaussian (D : ℕ → ℕ)
    (X : (k : ℕ) → Matrix (Fin (D k)) (Fin (D k)) ℂ)
    (hX : ∀ k, (X k).PosSemidef ∧ (X k).trace = 1)
    (hv : ∀ k, 0 < varentropy (hX k).1.isHermitian.eigenvalues)
    (hLyap : Tendsto (fun k : ℕ => thirdInformationMoment (hX k).1.isHermitian.eigenvalues /
      ((varentropy (hX k).1.isHermitian.eigenvalues)^(3/2:ℝ)*Real.sqrt k)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ x : ℝ,
      |informationMass (iidLaw (hX k).1.isHermitian.eigenvalues k) x-
        gaussianCDF 1 ((x-k*entropy (hX k).1.isHermitian.eigenvalues)/
          Real.sqrt ((k:ℝ)*varentropy (hX k).1.isHermitian.eigenvalues))| < ε := by
  have h := triangular_information_uniform_gaussian
    (fun k => (hX k).1.isHermitian.eigenvalues) (fun k i => (hX k).1.eigenvalues_nonneg i)
    (fun k => density_eigenvalues_sum (X k) (hX k)) hv hLyap
  intro ε hε
  filter_upwards [h ε hε] with k hk
  intro x
  rw [informationMass_iidLaw _ (fun i => (hX k).1.eigenvalues_nonneg i) k]
  exact hk x

end
end ExtractionDeviation
