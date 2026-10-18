import Deviation.QuantitativeExtraction

open scoped BigOperators ComplexOrder NNReal ENNReal Topology
open Set Filter Matrix ExtractionSpectrum MinimaxProfile SymmetricSupport

namespace ExtractionDeviation
noncomputable section

theorem compressionLoss_nonneg (D k : ℕ) (hD : 0<D) : 0≤compressionLoss D k := by
  have hr : (1:ℝ)≤(symmetricProjector (D*D) k).rank := by
    exact_mod_cast symmetricProjector_rank_pos (D*D) k (Nat.mul_pos hD hD)
  have ho : 1≤orbitOverhead D k := by
    exact one_le_mul_of_one_le_of_one_le hr (one_le_pow₀ (by norm_cast; omega))
  exact add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg ho)

/-- A dimension-explicit upper bound on the actual intrinsic compression
loss; the exponent comes from the proved symmetric-projector rank formula. -/
theorem compressionLoss_le (D k : ℕ) (hD : 0<D) :
    compressionLoss D k ≤ Real.log 4+
      ((D*D-1:ℕ):ℝ)*Real.log (k+D*D)+D*Real.log (k+1) := by
  have hr : (0:ℝ)<(symmetricProjector (D*D) k).rank := by
    exact_mod_cast symmetricProjector_rank_pos (D*D) k (Nat.mul_pos hD hD)
  have hn : (symmetricProjector (D*D) k).rank ≤ (k+D*D)^(D*D-1) := by
    rw [symmetricProjector_rank_choose_complement (D*D) k (Nat.mul_pos hD hD)]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  have hl := Real.log_le_log hr (show ((symmetricProjector (D*D) k).rank:ℝ) ≤
      ((k+D*D:ℕ):ℝ)^(D*D-1) from by exact_mod_cast hn)
  rw [Real.log_pow] at hl
  unfold compressionLoss orbitOverhead
  rw [Real.log_mul (ne_of_gt hr) (by positivity),Real.log_pow]
  push_cast at hl ⊢
  linarith

theorem gaussian_sandwich_error (F y l u B E : ℝ)
    (hl : 0≤l) (hu : 0≤u) (hE : 0≤E)
    (hL : gaussianCDF 1 (y-l)-B≤F)
    (hU : F≤gaussianCDF 1 (y+u)+B+E) :
    |F-gaussianCDF 1 y|≤B+gaussianPeak*max l u+E := by
  have h1 := gaussianCDF_sub_le_peak (y-l) y (by linarith)
  have h2 := gaussianCDF_sub_le_peak y (y+u) (by linarith)
  have h3 := mul_le_mul_of_nonneg_left (le_max_left l u) gaussianPeak_pos.le
  have h4 := mul_le_mul_of_nonneg_left (le_max_right l u) gaussianPeak_pos.le
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

/-- Actual finite-block error around the unshifted Gaussian, with the exact
orbit loss, a freely chosen nonnegative smoothing length and no rank assumption. -/
theorem universalBlockProtocol_gaussian_error (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hk : 0<k) (hK : 0<K) (hKa : K≤m^k) (hKb : K≤n^k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues) (t : ℝ) (ht : 0≤t) :
    |(universalBlockProtocol m n k K hm hn hK hKa hKb).fidelity (tensorInput m n k X)-
      gaussianCDF 1 (((k:ℝ)*(Real.log m+Real.log n)-2*Real.log K-
        k*entropy hX.1.isHermitian.eigenvalues)/
        Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues))| ≤
      informationBerryEsseenError hX.1.isHermitian.eigenvalues k+
      gaussianPeak*max
        (compressionLoss (m*n) k/Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues))
        (t/Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues))+Real.exp (-t/2) := by
  apply gaussian_sandwich_error
  · exact div_nonneg (compressionLoss_nonneg _ _ (Nat.mul_pos hm hn)) (Real.sqrt_nonneg _)
  · exact div_nonneg ht (Real.sqrt_nonneg _)
  · exact (Real.exp_pos _).le
  · convert universalBlockProtocol_berryEsseen m n k K hm hn hk hK hKa hKb X hX hv using 1 <;> ring_nf
  · convert protocol_berryEsseen_upper m n k K hm hn hk hK
      (universalBlockProtocol m n k K hm hn hK hKa hKb) X hX hv t using 1 <;> ring_nf

variable {a : ℕ → Type*} [∀ k,Fintype (a k)] [∀ k,Nonempty (a k)]
  [∀ k,DecidableEq (a k)] [∀ k,MeasurableSpace (a k)] [∀ k,MeasurableSingletonClass (a k)]

/-- Quantile inversion for genuinely changing finite laws and variances.
Only the computed Lyapunov moment ratio tends to zero; no quantile limit is assumed. -/
theorem triangular_informationQuantile_gaussian
    (p : (k : ℕ) → a k → ℝ) (hp : ∀ k i,0≤p k i) (hs : ∀ k,∑ i,p k i=1)
    (hv : ∀ k,0<varentropy (p k))
    (hLyap : Tendsto (fun k : ℕ => thirdInformationMoment (p k)/
      ((varentropy (p k))^(3/2:ℝ)*Real.sqrt k)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0<ε) (hε' : ε<1) :
    Tendsto (fun k => (informationQuantile (p k) (hs k) ε hε'.le k-k*entropy (p k))/
      Real.sqrt ((k:ℝ)*varentropy (p k))) atTop
      (𝓝 (gaussianQuantile 1 one_ne_zero ε hε hε')) := by
  let q := gaussianQuantile 1 one_ne_zero ε hε hε'
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hLo : gaussianCDF 1 (q-δ/2)<ε :=
    (gaussianCDF_lt_iff 1 one_ne_zero ε hε hε' _).mpr (by dsimp [q]; linarith)
  have hHi : ε<gaussianCDF 1 (q+δ/2) := by
    rw [← gaussianCDF_quantile 1 one_ne_zero ε hε hε']
    exact gaussianCDF_strictMono 1 one_ne_zero (by dsimp [q]; linarith)
  let e := min (ε-gaussianCDF 1 (q-δ/2)) (gaussianCDF 1 (q+δ/2)-ε)/2
  have he : 0<e := by dsimp [e]; positivity
  filter_upwards [triangular_information_uniform_gaussian p hp hs hv hLyap e he,
    eventually_gt_atTop 0] with k hk hkpos
  let s := Real.sqrt ((k:ℝ)*varentropy (p k))
  have hspos : 0<s := Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hkpos) (hv k))
  have hL := hk (k*entropy (p k)+s*(q-δ/2))
  have hU := hk (k*entropy (p k)+s*(q+δ/2))
  have hsne := ne_of_gt hspos
  have hx (z : ℝ) : (k*entropy (p k)+s*z-k*entropy (p k))/s=z := by field_simp; ring
  change |_-gaussianCDF 1 ((k*entropy (p k)+s*(q-δ/2)-k*entropy (p k))/s)|<e at hL
  change |_-gaussianCDF 1 ((k*entropy (p k)+s*(q+δ/2)-k*entropy (p k))/s)|<e at hU
  rw [hx] at hL hU
  have heL : 2*e≤ε-gaussianCDF 1 (q-δ/2) := by dsimp [e]; linarith [min_le_left (ε-gaussianCDF 1 (q-δ/2)) (gaussianCDF 1 (q+δ/2)-ε)]
  have heU : 2*e≤gaussianCDF 1 (q+δ/2)-ε := by dsimp [e]; linarith [min_le_right (ε-gaussianCDF 1 (q-δ/2)) (gaussianCDF 1 (q+δ/2)-ε)]
  have hlow : k*entropy (p k)+s*(q-δ/2)< informationQuantile (p k) (hs k) ε hε'.le k := by
    by_contra h
    have hc := (informationQuantile_le_iff (p k) (hp k) (hs k) ε hε'.le hε k _).mp (le_of_not_gt h)
    have hh := (abs_lt.mp hL).2
    linarith
  have hupp : informationQuantile (p k) (hs k) ε hε'.le k≤k*entropy (p k)+s*(q+δ/2) := by
    apply (informationQuantile_le_iff (p k) (hp k) (hs k) ε hε'.le hε k _).mpr
    have hh := (abs_lt.mp hU).1
    linarith
  have hl : q-δ/2<(informationQuantile (p k) (hs k) ε hε'.le k-k*entropy (p k))/s := by
    rw [lt_div_iff₀ hspos]; nlinarith
  have hu : (informationQuantile (p k) (hs k) ε hε'.le k-k*entropy (p k))/s≤q+δ/2 := by
    rw [div_le_iff₀ hspos]; nlinarith
  rw [Real.dist_eq,abs_lt]
  constructor <;> change _ < _ <;> linarith

/-- Row-by-row Gaussian approximation for the actual universal extraction
family in growing dimensions. The precise three numerical conditions and both
natural output budgets are retained. Moving thresholds need not converge. -/
theorem triangular_universal_gaussian_error (m n K : ℕ → ℕ)
    (hm : ∀ k,0<m k) (hn : ∀ k,0<n k)
    (hK : ∀ k,0<K k) (hKa : ∀ k,K k≤(m k)^k) (hKb : ∀ k,K k≤(n k)^k)
    (X : (k : ℕ) → Matrix (Fin (m k*n k)) (Fin (m k*n k)) ℂ)
    (hX : ∀ k,(X k).PosSemidef ∧ (X k).trace=1)
    (hv : ∀ k,0<varentropy (hX k).1.isHermitian.eigenvalues)
    (hLyap : Tendsto (fun k : ℕ => thirdInformationMoment (hX k).1.isHermitian.eigenvalues/
      ((varentropy (hX k).1.isHermitian.eigenvalues)^(3/2:ℝ)*Real.sqrt k)) atTop (𝓝 0))
    (hSigma : Tendsto (fun k : ℕ => Real.sqrt ((k:ℝ)*
      varentropy (hX k).1.isHermitian.eigenvalues)) atTop atTop)
    (hLoss : Tendsto (fun k : ℕ => compressionLoss (m k*n k) k/
      Real.sqrt ((k:ℝ)*varentropy (hX k).1.isHermitian.eigenvalues)) atTop (𝓝 0)) :
    Tendsto (fun k =>
      (universalBlockProtocol (m k) (n k) k (K k) (hm k) (hn k) (hK k) (hKa k) (hKb k)).fidelity
        (tensorInput (m k) (n k) k (X k))-
      gaussianCDF 1 (((k:ℝ)*(Real.log (m k)+Real.log (n k))-2*Real.log (K k)-
        k*entropy (hX k).1.isHermitian.eigenvalues)/
        Real.sqrt ((k:ℝ)*varentropy (hX k).1.isHermitian.eigenvalues))) atTop (𝓝 0) := by
  let s := fun k : ℕ => Real.sqrt ((k:ℝ)*varentropy (hX k).1.isHermitian.eigenvalues)
  have hB : Tendsto (fun k => informationBerryEsseenError (hX k).1.isHermitian.eigenvalues k)
      atTop (𝓝 0) := by
    simpa only [mul_zero,informationBerryEsseenError,mul_div_assoc] using hLyap.const_mul berryEsseenConstant
  have ht := Real.tendsto_sqrt_atTop.comp hSigma
  have hdiv : Tendsto (fun k => Real.sqrt (s k)/s k) atTop (𝓝 0) := by
    apply (tendsto_inv_atTop_zero.comp ht).congr'
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hs : 0<s k := Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hk) (hv k))
    have hr := Real.sq_sqrt hs.le
    have htpos := Real.sqrt_pos.mpr hs
    change (Real.sqrt (s k))⁻¹ = Real.sqrt (s k) / s k
    field_simp
    nlinarith
  have htail : Tendsto (fun k => Real.exp (-Real.sqrt (s k)/2)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (ht.atTop_mul_const (by norm_num : (0:ℝ)<1/2)) using 1
    ext k; dsimp [Function.comp_def,s]; congr 1 <;> ring
  have hbound := (hB.add ((hLoss.max hdiv).const_mul gaussianPeak)).add htail
  simp only [max_self,mul_zero,add_zero] at hbound
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hbound
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact universalBlockProtocol_gaussian_error (m k) (n k) k (K k) (hm k) (hn k) hk
    (hK k) (hKa k) (hKb k) (X k) (hX k) (hv k) _ (Real.sqrt_nonneg _)

end
end ExtractionDeviation
