import Deviation.QuantitativeQuantile
import Deviation.FixedErrorTarget
import Deviation.GaussianRegularity

open scoped BigOperators ComplexOrder NNReal ENNReal Topology
open Set Filter Matrix ExtractionSpectrum MinimaxProfile

namespace ExtractionDeviation
noncomputable section

/-- The exact finite loss of the intrinsic orbit-compression family. This is
the actual rank overhead, and is not the manuscript Schur overhead. -/
def compressionLoss (D k : ℕ) : ℝ := Real.log 4 + Real.log (orbitOverhead D k)

/-- Finite lower Gaussian bound for the actual density-independent protocol,
including its original integer quotient budget and both local output caps. -/
theorem universalBlockProtocol_berryEsseen (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hk : 0<k) (hK : 0<K) (hKa : K≤m^k) (hKb : K≤n^k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues) :
    gaussianCDF 1 (((k:ℝ)*(Real.log m+Real.log n)-2*Real.log K-
      compressionLoss (m*n) k-k*entropy hX.1.isHermitian.eigenvalues)/
      Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues))-
        informationBerryEsseenError hX.1.isHermitian.eigenvalues k ≤
      (universalBlockProtocol m n k K hm hn hK hKa hKb).fidelity (tensorInput m n k X) := by
  have he := (abs_le.mp (information_iid_berryEsseen hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) hv k hk
    (k*compressionCutoff m n k K))).1
  have hl := (iidInformationEvent_le_empiricalEntropyMass hk hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX)
    _ _ le_rfl).trans (universalBlockProtocol_mass m n k K hm hn hk hK hKa hKb X hX)
  rw [compressionCutoff_expansion m n k K hm hn hk hK] at he hl
  change -informationBerryEsseenError _ k ≤ _ at he
  dsimp only [compressionLoss]
  linarith

/-- Finite upper Gaussian bound for every actual finite Kraus PPT protocol.
There is no local output cap in this converse. -/
theorem protocol_berryEsseen_upper (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hk : 0<k) (hK : 0<K) (V : KrausPPTProtocol (m^k) (n^k) K)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues) (t : ℝ) :
    V.fidelity (tensorInput m n k X) ≤
      gaussianCDF 1 (((k:ℝ)*(Real.log m+Real.log n)-2*Real.log K+t-
        k*entropy hX.1.isHermitian.eigenvalues)/
        Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues))+
      informationBerryEsseenError hX.1.isHermitian.eigenvalues k+Real.exp (-t/2) := by
  have he := (abs_le.mp (information_iid_berryEsseen hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) hv k hk
    (Real.log (tensorBudget m n k K)+t))).2
  have hu := V.tensor_information_bound m n k K hm hn hK X hX t
  rw [tensorBudget_log m n k K hm hn hK] at he hu
  change _ ≤ informationBerryEsseenError _ k at he
  linarith

/-- A finite-error inverse lower bound for every feasible integer target of
the fixed common protocol. The computed moment error is proved internally. -/
theorem universalTarget_of_log_le (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hk : 0<k) (hK : 0<K) (hKa : K≤m^k) (hKb : K≤n^k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues)
    (ε : ℝ) (hε : ε<1)
    (hlo : informationBerryEsseenError hX.1.isHermitian.eigenvalues k<ε)
    (hlog : Real.log K ≤ k*entropyCapacity m n hX.1.isHermitian.eigenvalues-
      compressionLoss (m*n) k/2+
      Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues)/2*
      gaussianQuantile 1 one_ne_zero
        (ε-informationBerryEsseenError hX.1.isHermitian.eigenvalues k)
        (by linarith) (by
          have h := informationBerryEsseenError_nonneg _ (fun i => hX.1.eigenvalues_nonneg i) hv k
          linarith)) : K ∈ universalTargets m n k hm hn X ε := by
  have hB := informationBerryEsseenError_nonneg _ (fun i => hX.1.eigenvalues_nonneg i) hv k
  let q := gaussianQuantile 1 one_ne_zero
    (ε-informationBerryEsseenError hX.1.isHermitian.eigenvalues k)
    (by linarith) (by linarith)
  have hspos : 0<Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues) :=
    Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hk) hv)
  have hcut : -q ≤ ((k:ℝ)*(Real.log m+Real.log n)-2*Real.log K-
      compressionLoss (m*n) k-k*entropy hX.1.isHermitian.eigenvalues)/
      Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues) := by
    rw [le_div_iff₀ hspos]
    dsimp only [entropyCapacity] at hlog
    dsimp only [q]
    nlinarith
  have hg := gaussianCDF_mono 1 hcut
  rw [gaussianCDF_neg 1 one_ne_zero,show gaussianCDF 1 q =
    ε-informationBerryEsseenError hX.1.isHermitian.eigenvalues k from
      gaussianCDF_quantile _ _ _ _ _] at hg
  have hl := universalBlockProtocol_berryEsseen m n k K hm hn hk hK hKa hKb X hX hv
  exact ⟨hK,hKa,hKb,by linarith⟩

/-- Every successful target, including targets beyond the local caps, obeys
this explicit upper inverse bound. The smoothing parameter is free. -/
theorem pptTarget_log_le (m n k : ℕ) (hm : 0<m) (hn : 0<n) (hk : 0<k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues)
    (ε : ℝ) (hε : 0<ε) (t : ℝ)
    (hhi : ε+informationBerryEsseenError hX.1.isHermitian.eigenvalues k+Real.exp (-t/2)<1)
    (K : ℕ) (hK : K ∈ pptTargets m n k X ε) :
    Real.log K ≤ k*entropyCapacity m n hX.1.isHermitian.eigenvalues+t/2+
      Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues)/2*
      gaussianQuantile 1 one_ne_zero
        (ε+informationBerryEsseenError hX.1.isHermitian.eigenvalues k+Real.exp (-t/2))
        (by
          have h := informationBerryEsseenError_nonneg _ (fun i => hX.1.eigenvalues_nonneg i) hv k
          positivity) hhi := by
  obtain ⟨hK,V,hF⟩ := hK
  have hB := informationBerryEsseenError_nonneg _ (fun i => hX.1.eigenvalues_nonneg i) hv k
  have hu := protocol_berryEsseen_upper m n k K hm hn hk hK V X hX hv t
  let u := ((k:ℝ)*(Real.log m+Real.log n)-2*Real.log K+t-
    k*entropy hX.1.isHermitian.eigenvalues)/
    Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues)
  have hg : gaussianCDF 1 (-u) ≤
      ε+informationBerryEsseenError hX.1.isHermitian.eigenvalues k+Real.exp (-t/2) := by
    rw [gaussianCDF_neg 1 one_ne_zero]
    dsimp only [u]
    linarith
  have hq := (gaussianCDF_le_iff 1 one_ne_zero _ (by positivity) hhi (-u)).mp hg
  have hspos : 0<Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues) :=
    Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hk) hv)
  dsimp only [u] at hq
  have hq' := (div_le_iff₀ hspos).mp (show
      (-((k:ℝ)*(Real.log m+Real.log n)-2*Real.log K+t-
        k*entropy hX.1.isHermitian.eigenvalues))/
          Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues) ≤ _ from
      by simpa only [← neg_div] using hq)
  dsimp only [entropyCapacity]
  nlinarith

/-- Rounding down preserves the achievability inequality. Local caps are kept
at every block; the nonnegative logarithmic budget guarantees a positive target. -/
def finiteCappedTarget (m n k : ℕ) (L : ℝ) : ℕ :=
  min ⌊Real.exp L⌋₊ (min (m^k) (n^k))

theorem finiteCappedTarget_pos (m n k : ℕ) (hm : 0<m) (hn : 0<n)
    (L : ℝ) (hL : 0≤L) : 0<finiteCappedTarget m n k L := by
  apply lt_min _ (lt_min (Nat.pow_pos hm) (Nat.pow_pos hn))
  exact Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr hL)

theorem finiteCappedTarget_log_le (m n k : ℕ) (hm : 0<m) (hn : 0<n)
    (L : ℝ) (hL : 0≤L) : Real.log (finiteCappedTarget m n k L) ≤ L := by
  have hp : (0:ℝ)<finiteCappedTarget m n k L := by
    exact_mod_cast finiteCappedTarget_pos m n k hm hn L hL
  have hc : (finiteCappedTarget m n k L:ℝ) ≤ Real.exp L := by
    exact (show (finiteCappedTarget m n k L:ℝ) ≤ (⌊Real.exp L⌋₊:ℝ) from
      by exact_mod_cast min_le_left _ _).trans (Nat.floor_le (Real.exp_pos L).le)
  simpa only [Real.log_exp] using Real.log_le_log hp hc

/-- Entropy-prefix certificates from any actual Kraus protocol, including a
reserved sector of fractional width `a`, inherit the internally proved finite BE
bound. This interface keeps the sector coefficient and cutoff exact. -/
theorem protocol_berryEsseen_lower_of_entropyMass (m n k K : ℕ) (hk : 0<k)
    (V : KrausPPTProtocol (m^k) (n^k) K)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues)
    (a c : ℝ) (ha : 0≤a)
    (hprefix : a*empiricalEntropyMass hX.1.isHermitian.eigenvalues k c≤
      V.fidelity (tensorInput m n k X)) :
    a*(gaussianCDF 1 ((k*c-k*entropy hX.1.isHermitian.eigenvalues)/
      Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues))-
      informationBerryEsseenError hX.1.isHermitian.eigenvalues k)≤
        V.fidelity (tensorInput m n k X) := by
  have he := (abs_le.mp (information_iid_berryEsseen hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) hv k hk (k*c))).1
  have hmass := iidInformationEvent_le_empiricalEntropyMass hk hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) (k*c) c le_rfl
  apply (mul_le_mul_of_nonneg_left (show _ ≤ empiricalEntropyMass _ k c from by
    change -informationBerryEsseenError _ k≤_ at he
    linarith) ha).trans hprefix

/-- A rounded and locally capped actual target satisfying the finite inverse
bound is achievable, with no eventual or asymptotic feasibility premise. -/
theorem finiteCappedTarget_achievable (m n k : ℕ) (hm : 0<m) (hn : 0<n) (hk : 0<k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues)
    (ε : ℝ) (hε : ε<1)
    (hlo : informationBerryEsseenError hX.1.isHermitian.eigenvalues k<ε)
    (L : ℝ) (hL : 0≤L)
    (hbudget : L≤k*entropyCapacity m n hX.1.isHermitian.eigenvalues-
      compressionLoss (m*n) k/2+
      Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues)/2*
      gaussianQuantile 1 one_ne_zero
        (ε-informationBerryEsseenError hX.1.isHermitian.eigenvalues k)
        (by linarith) (by
          have h := informationBerryEsseenError_nonneg _ (fun i => hX.1.eigenvalues_nonneg i) hv k
          linarith)) : finiteCappedTarget m n k L∈universalTargets m n k hm hn X ε := by
  exact universalTarget_of_log_le m n k _ hm hn hk (finiteCappedTarget_pos m n k hm hn L hL)
    ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) X hX hv ε hε hlo
    ((finiteCappedTarget_log_le m n k hm hn L hL).trans hbudget)

/-- Flooring the exponential costs at most `log 2` whenever the logarithmic
budget is nonnegative, including the endpoint zero. -/
theorem log_natFloor_exp_bounds (L : ℝ) (hL : 0≤L) :
    L-Real.log 2≤Real.log (⌊Real.exp L⌋₊:ℝ) ∧ Real.log (⌊Real.exp L⌋₊:ℝ)≤L := by
  have hpos : (0:ℝ)<⌊Real.exp L⌋₊ := by
    exact_mod_cast Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr hL)
  have he : Real.exp L≤2*(⌊Real.exp L⌋₊:ℝ) := by
    have h := Nat.lt_floor_add_one (Real.exp L)
    have h1 : (1:ℝ)≤⌊Real.exp L⌋₊ := by exact_mod_cast (show 1≤⌊Real.exp L⌋₊ from by
      exact Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr hL))
    linarith
  constructor
  · have h := Real.log_le_log (Real.exp_pos L) he
    rw [Real.log_exp,Real.log_mul (by norm_num : (2:ℝ)≠0) hpos.ne'] at h
    linarith
  · simpa only [Real.log_exp] using Real.log_le_log hpos (Nat.floor_le (Real.exp_pos L).le)

/-- The exact local cap is retained in the finite logarithmic rounding loss. -/
theorem finiteCappedTarget_log_lower (m n k : ℕ) (hm : 0<m) (hn : 0<n)
    (L : ℝ) (hL : 0≤L) :
    min (L-Real.log 2) (min (k*Real.log m) (k*Real.log n))≤
      Real.log (finiteCappedTarget m n k L) := by
  unfold finiteCappedTarget
  by_cases h : ⌊Real.exp L⌋₊≤min (m^k) (n^k)
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (log_natFloor_exp_bounds L hL).1
  · rw [min_eq_right (le_of_not_ge h)]
    by_cases hmn : m^k≤n^k
    · rw [min_eq_left hmn,Nat.cast_pow,Real.log_pow]
      exact (min_le_right _ _).trans (min_le_left _ _)
    · rw [min_eq_right (le_of_not_ge hmn),Nat.cast_pow,Real.log_pow]
      exact (min_le_right _ _).trans (min_le_right _ _)

end
end ExtractionDeviation
