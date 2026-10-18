import Deviation.RoundedTarget
import MinimaxProfile.UniversalConverse

open scoped BigOperators ComplexOrder NNReal ENNReal Topology
open Set Filter Matrix ExtractionSpectrum MinimaxProfile

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def gaussianUpperEnvelope (p : ι → ℝ) (z : ℝ) (k : ℕ) : ℝ :=
  iidInformationEvent p k (k*entropy p-2*z*Real.sqrt k+gaussianSmoothing k) +
    Real.exp (-gaussianSmoothing k/2)

theorem gaussianUpperEnvelope_tendsto (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < varentropy p) (z : ℝ) :
    Tendsto (gaussianUpperEnvelope p z) atTop
      (𝓝 (gaussianCDF (varentropy p).toNNReal (-2*z))) := by
  have hcut : Tendsto (fun k : ℕ =>
      (k*entropy p-2*z*Real.sqrt k+gaussianSmoothing k-k*entropy p)/Real.sqrt k)
      atTop (𝓝 (-2*z)) := by
    have h := gaussianSmoothing_div_sqrt_tendsto.add_const (-2*z)
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hsq : Real.sqrt (k:ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hk)
    field_simp
    ring
  have hmass := iidInformationEvent_gaussian_moving p hp hs hv _ (-2*z) hcut
  have hexp : Tendsto (fun k : ℕ => Real.exp (-gaussianSmoothing k/2)) atTop (𝓝 0) := by
    have hlin := gaussianSmoothing_tendsto.atTop_mul_const (show (0:ℝ) < 1/2 by norm_num)
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin using 1
    ext k
    congr 1
    ring
  change Tendsto (fun k : ℕ =>
    iidInformationEvent p k (k*entropy p-2*z*Real.sqrt k+gaussianSmoothing k) +
      Real.exp (-gaussianSmoothing k/2)) atTop _
  simpa only [gaussianCDF, add_zero] using hmass.add hexp

def entropyCapacity (m n : ℕ) (p : Fin (m*n) → ℝ) : ℝ :=
  (Real.log m+Real.log n-entropy p)/2

/-- A uniform-in-target upper envelope for every actual state-aware finite-Kraus PPT protocol.
It imposes no local cap on `K`; this is needed for inverse fixed-error bounds. -/
theorem protocol_le_gaussianUpperEnvelope (m n k K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hk : 0 < k) (hK : 0 < K) (V : KrausPPTProtocol (m^k) (n^k) K)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (z : ℝ) (hsecond : z ≤ (Real.log K-k*entropyCapacity m n hX.1.isHermitian.eigenvalues) /
      Real.sqrt k) :
    V.fidelity (tensorInput m n k X) ≤ gaussianUpperEnvelope hX.1.isHermitian.eigenvalues z k := by
  have hsqrt : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hbound := V.tensor_information_bound m n k K hm hn hK X hX (gaussianSmoothing k)
  apply hbound.trans
  have hcut : Real.log (tensorBudget m n k K)+gaussianSmoothing k ≤
      k*entropy hX.1.isHermitian.eigenvalues-2*z*Real.sqrt k+gaussianSmoothing k := by
    rw [tensorBudget_log m n k K hm hn hK]
    have h := (le_div_iff₀ hsqrt).mp hsecond
    dsimp [entropyCapacity] at h
    linarith
  exact add_le_add (iidInformationEvent_mono _ (fun i => hX.1.eigenvalues_nonneg i) k hcut) le_rfl

theorem fixedError_uniform_upper (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (hv : 0 < varentropy hX.1.isHermitian.eigenvalues)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (z : ℝ)
    (hz : gaussianQuantile (varentropy hX.1.isHermitian.eigenvalues).toNNReal
      (ne_of_gt (Real.toNNReal_pos.mpr hv)) ε hε hε' / 2 < z) :
    ∀ᶠ k : ℕ in atTop, ∀ (K : ℕ) (hK : 0 < K)
      (V : KrausPPTProtocol (m^k) (n^k) K),
      z ≤ (Real.log K-k*entropyCapacity m n hX.1.isHermitian.eigenvalues)/Real.sqrt k →
      V.fidelity (tensorInput m n k X) < 1-ε := by
  let p := hX.1.isHermitian.eigenvalues
  let v := (varentropy p).toNNReal
  have hvn : v ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hv)
  have hgauss : gaussianCDF v (-2*z) < 1-ε := by
    have hlt : -2*z < -gaussianQuantile v hvn ε hε hε' := by linarith
    have h := gaussianCDF_strictMono v hvn hlt
    rw [gaussianCDF_neg v hvn, gaussianCDF_quantile] at h
    exact h
  have hlimit := gaussianUpperEnvelope_tendsto p (fun i => hX.1.eigenvalues_nonneg i)
    (density_eigenvalues_sum X hX) hv z
  filter_upwards [hlimit.eventually (Iio_mem_nhds hgauss),eventually_gt_atTop 0] with k hk hkpos
  intro K hK V hsecond
  exact (protocol_le_gaussianUpperEnvelope m n k K hm hn hkpos hK V X hX z hsecond).trans_lt hk

/-- The concrete common protocol works below every fixed Gaussian quantile.
The integer sequence is rounded and capped only at its finitely many early blocks. -/
theorem fixedError_universal_lower (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (hv : 0 < varentropy hX.1.isHermitian.eigenvalues)
    (hC : 0 < entropyCapacity m n hX.1.isHermitian.eigenvalues)
    (hCa : entropyCapacity m n hX.1.isHermitian.eigenvalues < Real.log m)
    (hCb : entropyCapacity m n hX.1.isHermitian.eigenvalues < Real.log n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (z : ℝ)
    (hz : z < gaussianQuantile (varentropy hX.1.isHermitian.eigenvalues).toNNReal
      (ne_of_gt (Real.toNNReal_pos.mpr hv)) ε hε hε' / 2) :
    let C := entropyCapacity m n hX.1.isHermitian.eigenvalues
    let K := cappedTarget m n C z
    let hK := fun k => cappedTarget_pos m n hm hn C z k
    ∀ᶠ k : ℕ in atTop,
      1-ε < (universalBlockProtocol m n k (K k) hm hn (hK k)
        (by exact (min_le_right _ _).trans (min_le_left _ _))
        (by exact (min_le_right _ _).trans (min_le_right _ _))).fidelity (tensorInput m n k X) := by
  dsimp only
  let p := hX.1.isHermitian.eigenvalues
  let C := entropyCapacity m n p
  let K := cappedTarget m n C z
  have hK := fun k => cappedTarget_pos m n hm hn C z k
  have hKa : ∀ k, K k ≤ m^k := fun k => (min_le_right _ _).trans (min_le_left _ _)
  have hKb : ∀ k, K k ≤ n^k := fun k => (min_le_right _ _).trans (min_le_right _ _)
  have hsecond := cappedTarget_secondOrder m n hm hn C z hC hCa hCb
  let V := fun k => universalBlockProtocol m n k (K k) hm hn (hK k) (hKa k) (hKb k)
  have hlow : gaussianCDF (varentropy p).toNNReal (-2*z) ≤
      liminf (fun k => (V k).fidelity (tensorInput m n k X)) atTop := by
    have hinfo := iidInformationEvent_gaussian_moving p (fun i => hX.1.eigenvalues_nonneg i)
      (density_eigenvalues_sum X hX) hv
      (fun k => (k:ℝ)*compressionCutoff m n k (K k)) (-2*z)
      (compressionCutoff_gaussian m n hm hn K hK _ z hsecond)
    unfold gaussianCDF
    rw [← hinfo.liminf_eq]
    apply liminf_le_liminf _ hinfo.isBoundedUnder_ge
      (isCoboundedUnder_ge_of_le atTop (fun k =>
        ((V k).fidelity_bounds (hK k) _ (tensorInput_density m n k X hX)).2))
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact (iidInformationEvent_le_empiricalEntropyMass hk p (fun i => hX.1.eigenvalues_nonneg i)
      (density_eigenvalues_sum X hX) _ _ le_rfl).trans
      (universalBlockProtocol_mass m n k (K k) hm hn hk (hK k) (hKa k) (hKb k) X hX)
  have hhigh := KrausPPTProtocol.tensor_gaussian_converse m n hm hn K hK V X hX hv z hsecond
  have hlimit := tendsto_of_le_liminf_of_limsup_le hlow hhigh
    (isBoundedUnder_of ⟨1,fun k =>
      ((V k).fidelity_bounds (hK k) _ (tensorInput_density m n k X hX)).2⟩)
    (isBoundedUnder_of ⟨0,fun k =>
      ((V k).fidelity_bounds (hK k) _ (tensorInput_density m n k X hX)).1⟩)
  have hgauss : 1-ε < gaussianCDF (varentropy p).toNNReal (-2*z) := by
    have hvn : (varentropy p).toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hv)
    have hlt : -gaussianQuantile (varentropy p).toNNReal hvn ε hε hε' < -2*z := by linarith
    have h := gaussianCDF_strictMono _ hvn hlt
    rw [gaussianCDF_neg _ hvn, gaussianCDF_quantile] at h
    exact h
  exact hlimit.eventually (Ioi_mem_nhds hgauss)

end
end ExtractionDeviation
