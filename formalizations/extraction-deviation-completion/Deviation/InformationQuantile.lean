import Deviation.FiniteQuantile

open scoped BigOperators NNReal ENNReal Topology
open Set Filter ExtractionSpectrum

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def wordInformation (p : ι → ℝ) (k : ℕ) (w : Fin k → ι) : ℝ :=
  ∑ j, selfInformation p (w j)

/-- The quantile of the actual finite iid spectral law, not an assumed Gaussian approximation. -/
def informationQuantile (p : ι → ℝ) (hs : ∑ i, p i = 1)
    (ε : ℝ) (hε : ε ≤ 1) (k : ℕ) : ℝ :=
  finiteQuantile (iidLaw p k) (wordInformation p k) (iidLaw_sum p hs k) ε hε

theorem finiteCDF_wordInformation (p : ι → ℝ) (k : ℕ) (x : ℝ) :
    finiteCDF (iidLaw p k) (wordInformation p k) x = iidInformationEvent p k x := rfl

theorem informationQuantile_cdf (p : ι → ℝ) (hs : ∑ i, p i = 1)
    (ε : ℝ) (hε : ε ≤ 1) (k : ℕ) :
    ε ≤ iidInformationEvent p k (informationQuantile p hs ε hε k) :=
  finiteQuantile_cdf (iidLaw p k) (wordInformation p k) (iidLaw_sum p hs k) ε hε

theorem informationQuantile_le_iff (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (ε : ℝ) (hε : ε ≤ 1) (hεpos : 0 < ε) (k : ℕ) (x : ℝ) :
    informationQuantile p hs ε hε k ≤ x ↔ ε ≤ iidInformationEvent p k x :=
  finiteQuantile_le_iff (iidLaw p k) (wordInformation p k) (iidLaw_nonneg p hp k)
    (iidLaw_sum p hs k) ε hε hεpos x

/-- Fixed-error quantile inversion for the finite iid spectrum, including singular input laws.
The CLT and the strict/continuous Gaussian CDF are proved dependencies, not hypotheses. -/
theorem informationQuantile_gaussian [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hv : 0 < varentropy p) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    Tendsto (fun k : ℕ => (informationQuantile p hs ε hε'.le k - k*entropy p) /
      Real.sqrt k) atTop
      (𝓝 (gaussianQuantile (varentropy p).toNNReal
        (ne_of_gt (Real.toNNReal_pos.mpr hv)) ε hε hε')) := by
  let v := (varentropy p).toNNReal
  have hvn : v ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hv)
  let q := gaussianQuantile v hvn ε hε hε'
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hLo : gaussianCDF v (q-δ/2) < ε :=
    (gaussianCDF_lt_iff v hvn ε hε hε' _).mpr (by dsimp [q]; linarith)
  have hHi : ε < gaussianCDF v (q+δ/2) := by
    rw [← gaussianCDF_quantile v hvn ε hε hε']
    exact gaussianCDF_strictMono v hvn (by dsimp [q]; linarith)
  have hL := (iidInformationEvent_gaussian p hp hs hv (q-δ/2)).eventually
    (Iio_mem_nhds hLo)
  have hU := (iidInformationEvent_gaussian p hp hs hv (q+δ/2)).eventually
    (Ioi_mem_nhds hHi)
  filter_upwards [hL,hU,eventually_gt_atTop 0] with k hkL hkU hk
  have hsqrt : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hlower : k*entropy p+(q-δ/2)*Real.sqrt k < informationQuantile p hs ε hε'.le k := by
    by_contra h
    have hh := (informationQuantile_le_iff p hp hs ε hε'.le hε k _).mp
      (le_of_not_gt h)
    linarith
  have hupper : informationQuantile p hs ε hε'.le k ≤
      k*entropy p+(q+δ/2)*Real.sqrt k :=
    (informationQuantile_le_iff p hp hs ε hε'.le hε k _).mpr hkU.le
  rw [Real.dist_eq, abs_lt]
  have hlow : q-δ/2 < (informationQuantile p hs ε hε'.le k - k*entropy p)/Real.sqrt k := by
    rw [lt_div_iff₀ hsqrt]
    linarith
  have hup : (informationQuantile p hs ε hε'.le k - k*entropy p)/Real.sqrt k ≤ q+δ/2 := by
    rw [div_le_iff₀ hsqrt]
    linarith
  constructor <;> dsimp only [q] at * <;> linarith

theorem informationQuantile_gaussian_standard [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hv : 0 < varentropy p) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    Tendsto (fun k : ℕ => (informationQuantile p hs ε hε'.le k - k*entropy p) /
      Real.sqrt k) atTop
      (𝓝 (Real.sqrt (varentropy p) * gaussianQuantile 1 one_ne_zero ε hε hε')) := by
  have h := informationQuantile_gaussian p hp hs hv ε hε hε'
  rw [gaussianQuantile_scale, Real.coe_toNNReal _ hv.le] at h
  exact h

end
end ExtractionDeviation
