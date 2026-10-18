import OperationalCompletion.ReservedLaws
import Deviation.FixedErrorTarget
import Deviation.QuantitativeExtraction

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

def reservedTargets (m n k : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (ε : ℝ) : Set ℕ :=
  {K | ∃ hK : 0<K,1-ε≤(reservedProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X)}

def reservedFixedErrorTarget (m n k : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (ε : ℝ) : ℕ :=
  sSup (reservedTargets m n k hm hn hmn X ε)

theorem reservedTargets_subset_pptTargets (m n k : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (ε : ℝ) :
    reservedTargets m n k hm hn hmn X ε⊆pptTargets m n k X ε := by
  rintro K ⟨hK,hF⟩
  exact ⟨hK,reservedProtocol m n k K hm hn hmn hK,hF⟩

theorem reservedTargets_lower_bracket (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues)
    (hC : 0<entropyCapacity m n hX.1.isHermitian.eigenvalues)
    (hCa : entropyCapacity m n hX.1.isHermitian.eigenvalues<Real.log m)
    (ε : ℝ) (hε : 0<ε) (hε' : ε<1) (z : ℝ)
    (hz : z<gaussianQuantile (varentropy hX.1.isHermitian.eigenvalues).toNNReal
      (ne_of_gt (Real.toNNReal_pos.mpr hv)) ε hε hε'/2) :
    ∃ K : ℕ → ℕ,(∀ᶠ k : ℕ in atTop,K k∈reservedTargets m n k hm hn hmn X ε) ∧
      Tendsto (fun k : ℕ => (Real.log (K k)-
        k*entropyCapacity m n hX.1.isHermitian.eigenvalues)/Real.sqrt k) atTop (nhds z) := by
  let C := entropyCapacity m n hX.1.isHermitian.eigenvalues
  let v := (varentropy hX.1.isHermitian.eigenvalues).toNNReal
  let K := roundedTarget C z
  have hK := roundedTarget_pos C z
  have hsecond := roundedTarget_secondOrder C z hC
  refine ⟨K,?_,hsecond⟩
  have hlimit : Tendsto (fun k => (reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity
      (tensorInput m n k X)) atTop (nhds (gaussianCDF v (-2*z))) :=
    reserved_gaussian_limit m n hm hn hmn K hK X hX z hv hCa hsecond
  have hvn : v≠0 := ne_of_gt (Real.toNNReal_pos.mpr hv)
  have hgauss : 1-ε<gaussianCDF v (-2*z) := by
    have hlt : -gaussianQuantile v hvn ε hε hε' < -2*z := by linarith
    have h := gaussianCDF_strictMono v hvn hlt
    rwa [gaussianCDF_neg v hvn,gaussianCDF_quantile] at h
  exact (hlimit.eventually_const_lt hgauss).mono (fun k hk => ⟨hK k,hk.le⟩)

/-- The same fixed common family attains the genuine natural maximum target
and its full fixed-error Gaussian inverse, without target monotonicity. -/
theorem reservedFixedErrorTarget_gaussian (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues)
    (hC : 0<entropyCapacity m n hX.1.isHermitian.eigenvalues)
    (hCa : entropyCapacity m n hX.1.isHermitian.eigenvalues<Real.log m)
    (ε : ℝ) (hε : 0<ε) (hε' : ε<1) :
    (∀ᶠ k : ℕ in atTop,reservedFixedErrorTarget m n k hm hn hmn X ε∈
      reservedTargets m n k hm hn hmn X ε) ∧
    Tendsto (fun k : ℕ => (Real.log (reservedFixedErrorTarget m n k hm hn hmn X ε)-
      k*entropyCapacity m n hX.1.isHermitian.eigenvalues)/Real.sqrt k) atTop
        (nhds (Real.sqrt (varentropy hX.1.isHermitian.eigenvalues)*
          gaussianQuantile 1 one_ne_zero ε hε hε'/2)) := by
  have h := maximalTarget_gaussian_of_brackets (fun k => reservedTargets m n k hm hn hmn X ε)
    (entropyCapacity m n hX.1.isHermitian.eigenvalues)
    (gaussianQuantile (varentropy hX.1.isHermitian.eigenvalues).toNNReal
      (ne_of_gt (Real.toNNReal_pos.mpr hv)) ε hε hε'/2)
    (fun k K h => h.choose) (by
      intro z hz
      filter_upwards [pptTargets_upper_bracket m n hm hn X hX hv ε hε hε' z hz] with k hk
      intro K hK
      exact hk K (reservedTargets_subset_pptTargets m n k hm hn hmn X ε hK))
    (reservedTargets_lower_bracket m n hm hn hmn X hX hv hC hCa ε hε hε')
  refine ⟨h.1.mono (fun k hk => hk.2.2),?_⟩
  have hlimit := h.2
  rw [gaussianQuantile_scale,Real.coe_toNNReal _ hv.le] at hlimit
  exact hlimit

def reservedTotalLoss (m n k : ℕ) : ℝ := compressionLoss (m*n) k+reservationLoss m n k

theorem reservationSafeCutoff_expansion (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hk : 0<k) (hK : 0<K) :
    (k:ℝ)*reservationSafeCutoff m n k K=
      (k:ℝ)*(Real.log m+Real.log n)-2*Real.log K-reservedTotalLoss m n k := by
  have h := compressionCutoff_expansion m n k K hm hn hk hK
  have hkR : (k:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hk)
  unfold reservationSafeCutoff reservedTotalLoss compressionLoss
  field_simp
  nlinarith

/-- Finite-k BE for the actual common reserved protocol. The actual orbit rank,
reservation rank, integer targets and local sector cap are all retained. -/
theorem reservedProtocol_berryEsseen (m n k K : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (hk : 0<k) (hK : 0<K) (hKa : K≤reservationLocal m n k m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues) :
    gaussianCDF 1 (((k:ℝ)*(Real.log m+Real.log n)-2*Real.log K-reservedTotalLoss m n k-
      k*entropy hX.1.isHermitian.eigenvalues)/Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues))-
        informationBerryEsseenError hX.1.isHermitian.eigenvalues k≤
      (reservedProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X) := by
  have h := protocol_berryEsseen_lower_of_entropyMass m n k K hk
    (reservedProtocol m n k K hm hn hmn hK) X hX hv 1 (reservationSafeCutoff m n k K)
    (by norm_num) (by simpa only [one_mul] using
      reservedProtocol_safe_mass m n k K hm hn hmn hK hk hKa X hX)
  simpa only [one_mul,reservationSafeCutoff_expansion m n k K hm hn hk hK] using h

end
end OperationalCompletion
