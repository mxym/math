import Deviation.QuantitativeTriangular

open scoped BigOperators ComplexOrder NNReal ENNReal Topology
open Set Filter Matrix ExtractionSpectrum MinimaxProfile
namespace ExtractionDeviation
noncomputable section

/-- A fully explicit sufficient dimension budget for the intrinsic family. -/
def dimensionLossBound (D k : ℕ) : ℝ :=
  Real.log 4+((D*D-1:ℕ):ℝ)*Real.log (k+D*D)+D*Real.log (k+1)

 theorem compressionLoss_le_dimensionLossBound (D k : ℕ) (hD : 0<D) :
    compressionLoss D k≤dimensionLossBound D k := compressionLoss_le D k hD

/-- A uniform variance floor reduces the Lyapunov condition to the actual
third centered absolute moment being o(sqrt k); dimensions may change. -/
 theorem informationLyapunov_of_variance_floor
    {a : ℕ → Type*} [∀ k,Fintype (a k)]
    (p : (k : ℕ) → a k → ℝ) (hp : ∀ k i,0≤p k i)
    (v : ℝ) (hv : 0<v) (hV : ∀ k,v≤varentropy (p k))
    (hT : Tendsto (fun k : ℕ => thirdInformationMoment (p k)/Real.sqrt k) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => thirdInformationMoment (p k)/
      ((varentropy (p k))^(3/2:ℝ)*Real.sqrt k)) atTop (𝓝 0) := by
  have hbound := hT.div_const (v^(3/2:ℝ))
  simp only [zero_div] at hbound
  apply squeeze_zero' (Eventually.of_forall (fun k => div_nonneg
    (thirdAbsoluteMoment_nonneg _ _ (hp k))
    (mul_nonneg (Real.rpow_nonneg (hv.le.trans (hV k)) _) (Real.sqrt_nonneg _)))) _ hbound
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hVk := hv.trans_le (hV k)
  rw [div_div]
  apply div_le_div_of_nonneg_left (thirdAbsoluteMoment_nonneg _ _ (hp k)) (by positivity)
  rw [mul_comm (Real.sqrt k)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hv.le (hV k) (by norm_num))
    (Real.sqrt_nonneg _)

 theorem sigma_tendsto_of_variance_floor (V : ℕ → ℝ)
    (v : ℝ) (hv : 0<v) (hV : ∀ k,v≤V k) :
    Tendsto (fun k : ℕ => Real.sqrt ((k:ℝ)*V k)) atTop atTop := by
  apply tendsto_atTop_mono (fun k => ?_)
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const
      (Real.sqrt_pos.mpr hv))
  change Real.sqrt (k:ℝ)*Real.sqrt v≤Real.sqrt ((k:ℝ)*V k)
  rw [← Real.sqrt_mul (Nat.cast_nonneg k)]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hV k) (Nat.cast_nonneg k))

 theorem compressionLoss_ratio_of_dimension_bound (D : ℕ → ℕ) (hD : ∀ k,0<D k)
    (V : ℕ → ℝ) (v : ℝ) (hv : 0<v) (hV : ∀ k,v≤V k)
    (hDim : Tendsto (fun k : ℕ => dimensionLossBound (D k) k/Real.sqrt k) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => compressionLoss (D k) k/Real.sqrt ((k:ℝ)*V k)) atTop (𝓝 0) := by
  have hbound := hDim.div_const (Real.sqrt v)
  simp only [zero_div] at hbound
  apply squeeze_zero' (Eventually.of_forall (fun k => div_nonneg
    (compressionLoss_nonneg _ _ (hD k)) (Real.sqrt_nonneg _))) _ hbound
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hdim := compressionLoss_le_dimensionLossBound (D k) k (hD k)
  have hnon : 0≤dimensionLossBound (D k) k :=
    (compressionLoss_nonneg _ _ (hD k)).trans hdim
  calc
    _ ≤ dimensionLossBound (D k) k/Real.sqrt ((k:ℝ)*V k) :=
      div_le_div_of_nonneg_right hdim (Real.sqrt_nonneg _)
    _ ≤ dimensionLossBound (D k) k/(Real.sqrt k*Real.sqrt v) := by
      apply div_le_div_of_nonneg_left hnon (by positivity)
      rw [← Real.sqrt_mul (Nat.cast_nonneg k)]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hV k) (Nat.cast_nonneg k))
    _ = _ := by rw [div_div]

/-- A concrete sufficient growing-dimension theorem for the actual family:
variance is uniformly positive, T=o(sqrt k), and the displayed explicit
polynomial rank loss is o(sqrt k). Both integer local output caps are retained.
The moving Gaussian threshold itself need not have a limit. -/
 theorem triangular_universal_gaussian_of_variance_floor (m n K : ℕ → ℕ)
    (hm : ∀ k,0<m k) (hn : ∀ k,0<n k)
    (hK : ∀ k,0<K k) (hKa : ∀ k,K k≤(m k)^k) (hKb : ∀ k,K k≤(n k)^k)
    (X : (k : ℕ) → Matrix (Fin (m k*n k)) (Fin (m k*n k)) ℂ)
    (hX : ∀ k,(X k).PosSemidef ∧ (X k).trace=1)
    (v : ℝ) (hv : 0<v) (hV : ∀ k,v≤varentropy (hX k).1.isHermitian.eigenvalues)
    (hT : Tendsto (fun k : ℕ => thirdInformationMoment (hX k).1.isHermitian.eigenvalues/
      Real.sqrt k) atTop (𝓝 0))
    (hDim : Tendsto (fun k : ℕ => dimensionLossBound (m k*n k) k/Real.sqrt k) atTop (𝓝 0)) :
    Tendsto (fun k =>
      (universalBlockProtocol (m k) (n k) k (K k) (hm k) (hn k) (hK k) (hKa k) (hKb k)).fidelity
        (tensorInput (m k) (n k) k (X k))-
      gaussianCDF 1 (((k:ℝ)*(Real.log (m k)+Real.log (n k))-2*Real.log (K k)-
        k*entropy (hX k).1.isHermitian.eigenvalues)/
        Real.sqrt ((k:ℝ)*varentropy (hX k).1.isHermitian.eigenvalues))) atTop (𝓝 0) := by
  exact triangular_universal_gaussian_error m n K hm hn hK hKa hKb X hX
    (fun k => hv.trans_le (hV k))
    (informationLyapunov_of_variance_floor (fun k => (hX k).1.isHermitian.eigenvalues)
      (fun k => (hX k).1.eigenvalues_nonneg) v hv hV hT)
    (sigma_tendsto_of_variance_floor _ v hv hV)
    (compressionLoss_ratio_of_dimension_bound _ (fun k => Nat.mul_pos (hm k) (hn k)) _ v hv hV hDim)

end
end ExtractionDeviation
