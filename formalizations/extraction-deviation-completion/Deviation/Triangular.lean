import Deviation.FourierIID

open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set ExtractionSpectrum

namespace ExtractionDeviation
noncomputable section

variable {a : ℕ → Type*} [∀ k, Fintype (a k)] [∀ k, DecidableEq (a k)]
  [∀ k, MeasurableSpace (a k)] [∀ k, MeasurableSingletonClass (a k)]

/-- A real, constructed Gaussian limit for triangular finite iid rows. The
alphabet, input law, observable and variance may all change with `k`. The only
probabilistic premise is the explicit third-moment Lyapunov ratio, not a CLT. -/
theorem triangular_iid_charFun_gaussian
    (p f : (k : ℕ) → a k → ℝ) (hp : ∀ k i, 0 ≤ p k i) (hs : ∀ k, ∑ i, p k i = 1)
    (hv : ∀ k, 0 < finiteVariance (p k) (f k))
    (hLyap : Tendsto (fun k : ℕ => thirdAbsoluteMoment (p k) (f k) /
      (finiteVariance (p k) (f k)*Real.sqrt (finiteVariance (p k) (f k))*Real.sqrt k))
      atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun k => charFun (standardizedIIDMeasure (p k) (f k) (hp k) (hs k) k) t)
      atTop (𝓝 (charFun (gaussianReal 0 1) t)) := by
  have hLyap' : Tendsto (fun k : ℕ => lyapunovRatio (p k) (f k) k) atTop (𝓝 0) := by
    apply hLyap.congr'
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact (lyapunovRatio_eq (p k) (f k) (hv k) k hk).symm
  have hsmall : Tendsto (fun k : ℕ => t^4/(4*k)) atTop (𝓝 0) := by
    apply ((tendsto_const_nhds (x := t^4/4)).div_atTop tendsto_natCast_atTop_atTop).congr'
    filter_upwards with k
    ring
  have hbound := (hLyap'.const_mul (4*|t|^3)).add hsmall
  simp only [mul_zero,zero_add] at hbound
  have hnorm : Tendsto (fun k =>
      ‖charFun (standardizedIIDMeasure (p k) (f k) (hp k) (hs k) k) t-gaussianChar 1 t‖)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hbound
    filter_upwards [eventually_gt_atTop 0,
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (t^2))] with k hk ht
    exact charFun_standardizedIIDMeasure_bound (p k) (f k) (hp k) (hs k) (hv k) k hk t ht
  rw [show gaussianChar 1 t = charFun (gaussianReal 0 1) t from
    gaussianChar_eq_charFun (1:ℝ≥0) t] at hnorm
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

theorem triangular_iid_probabilityMeasure_gaussian
    (p f : (k : ℕ) → a k → ℝ) (hp : ∀ k i, 0 ≤ p k i) (hs : ∀ k, ∑ i, p k i = 1)
    (hv : ∀ k, 0 < finiteVariance (p k) (f k))
    (hLyap : Tendsto (fun k : ℕ => thirdAbsoluteMoment (p k) (f k) /
      (finiteVariance (p k) (f k)*Real.sqrt (finiteVariance (p k) (f k))*Real.sqrt k))
      atTop (𝓝 0)) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun k => ⟨standardizedIIDMeasure (p k) (f k) (hp k) (hs k) k,by infer_instance⟩)
      atTop (𝓝 ⟨gaussianReal 0 1,by infer_instance⟩) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  exact triangular_iid_charFun_gaussian p f hp hs hv hLyap t

theorem triangular_iid_cdf_gaussian
    (p f : (k : ℕ) → a k → ℝ) (hp : ∀ k i, 0 ≤ p k i) (hs : ∀ k, ∑ i, p k i = 1)
    (hv : ∀ k, 0 < finiteVariance (p k) (f k))
    (hLyap : Tendsto (fun k : ℕ => thirdAbsoluteMoment (p k) (f k) /
      (finiteVariance (p k) (f k)*Real.sqrt (finiteVariance (p k) (f k))*Real.sqrt k))
      atTop (𝓝 0)) (y : ℝ) :
    Tendsto (fun k => (standardizedIIDMeasure (p k) (f k) (hp k) (hs k) k).real (Iic y)) atTop
      (𝓝 (gaussianCDF 1 y)) := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have h := triangular_iid_probabilityMeasure_gaussian p f hp hs hv hLyap
  have hfront : gaussianReal 0 1 (frontier (Iic y)) = 0 := by simp only [frontier_Iic,measure_singleton]
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h (E := Iic y) hfront
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top (gaussianReal 0 1) (Iic y))).comp hm
  exact hreal

end
end ExtractionDeviation
