import Deviation.OperationalQuantile
import Deviation.NaturalMaximum

open scoped BigOperators ComplexOrder NNReal ENNReal Topology
open Set Filter Matrix ExtractionSpectrum MinimaxProfile

namespace ExtractionDeviation
noncomputable section

/-- Every genuinely achievable target in the original state-aware finite-Kraus PPT model. -/
def pptTargets (m n k : ℕ) (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (ε : ℝ) : Set ℕ :=
  {K | 0 < K ∧ ∃ V : KrausPPTProtocol (m^k) (n^k) K,
    1-ε ≤ V.fidelity (tensorInput m n k X)}

/-- Targets achieved by the fixed density-independent `universalBlockProtocol` function.
The protocol is chosen before `X`; only its performance is evaluated at `X`. -/
def universalTargets (m n k : ℕ) (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (ε : ℝ) : Set ℕ :=
  {K | ∃ (hK : 0 < K) (hKa : K ≤ m^k) (hKb : K ≤ n^k),
    1-ε ≤ (universalBlockProtocol m n k K hm hn hK hKa hKb).fidelity (tensorInput m n k X)}

def pptFixedErrorTarget (m n k : ℕ) (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (ε : ℝ) : ℕ :=
  sSup (pptTargets m n k X ε)

def universalFixedErrorTarget (m n k : ℕ) (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (ε : ℝ) : ℕ :=
  sSup (universalTargets m n k hm hn X ε)

theorem universalTargets_subset_pptTargets (m n k : ℕ) (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (ε : ℝ) :
    universalTargets m n k hm hn X ε ⊆ pptTargets m n k X ε := by
  intro K hK
  obtain ⟨hK,hKa,hKb,hF⟩ := hK
  exact ⟨hK,universalBlockProtocol m n k K hm hn hK hKa hKb,hF⟩

theorem pptTargets_upper_bracket (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (hv : 0 < varentropy hX.1.isHermitian.eigenvalues)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (z : ℝ)
    (hz : gaussianQuantile (varentropy hX.1.isHermitian.eigenvalues).toNNReal
      (ne_of_gt (Real.toNNReal_pos.mpr hv)) ε hε hε' / 2 < z) :
    ∀ᶠ k : ℕ in atTop, ∀ K ∈ pptTargets m n k X ε,
      (Real.log K-k*entropyCapacity m n hX.1.isHermitian.eigenvalues)/Real.sqrt k < z := by
  filter_upwards [fixedError_uniform_upper m n hm hn X hX hv ε hε hε' z hz] with k hk
  intro K hK
  obtain ⟨hK,V,hF⟩ := hK
  by_contra h
  exact not_lt_of_ge hF (hk K hK V (le_of_not_gt h))

theorem universalTargets_lower_bracket (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (hv : 0 < varentropy hX.1.isHermitian.eigenvalues)
    (hC : 0 < entropyCapacity m n hX.1.isHermitian.eigenvalues)
    (hCa : entropyCapacity m n hX.1.isHermitian.eigenvalues < Real.log m)
    (hCb : entropyCapacity m n hX.1.isHermitian.eigenvalues < Real.log n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (z : ℝ)
    (hz : z < gaussianQuantile (varentropy hX.1.isHermitian.eigenvalues).toNNReal
      (ne_of_gt (Real.toNNReal_pos.mpr hv)) ε hε hε' / 2) :
    ∃ K : ℕ → ℕ, (∀ᶠ k : ℕ in atTop, K k ∈ universalTargets m n k hm hn X ε) ∧
      Tendsto (fun k : ℕ => (Real.log (K k)-
        k*entropyCapacity m n hX.1.isHermitian.eigenvalues)/Real.sqrt k) atTop (𝓝 z) := by
  let C := entropyCapacity m n hX.1.isHermitian.eigenvalues
  refine ⟨cappedTarget m n C z,?_,cappedTarget_secondOrder m n hm hn C z hC hCa hCb⟩
  filter_upwards [fixedError_universal_lower m n hm hn X hX hv hC hCa hCb ε hε hε' z hz]
    with k hk
  refine ⟨cappedTarget_pos m n hm hn C z k,
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _),hk.le⟩

/-- The actual state-aware PPT fixed-error maximum has the Gaussian inverse expansion.
Every sufficiently large maximum is an attained natural target. No existence of
an optimal channel, spectrum bridge, CLT, or monotonicity is assumed. -/
theorem pptFixedErrorTarget_gaussian (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (hv : 0 < varentropy hX.1.isHermitian.eigenvalues)
    (hC : 0 < entropyCapacity m n hX.1.isHermitian.eigenvalues)
    (hCa : entropyCapacity m n hX.1.isHermitian.eigenvalues < Real.log m)
    (hCb : entropyCapacity m n hX.1.isHermitian.eigenvalues < Real.log n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    (∀ᶠ k : ℕ in atTop,
      pptFixedErrorTarget m n k X ε ∈ pptTargets m n k X ε) ∧
    Tendsto (fun k : ℕ => (Real.log (pptFixedErrorTarget m n k X ε)-
      k*entropyCapacity m n hX.1.isHermitian.eigenvalues)/Real.sqrt k) atTop
      (𝓝 (Real.sqrt (varentropy hX.1.isHermitian.eigenvalues) *
        gaussianQuantile 1 one_ne_zero ε hε hε' / 2)) := by
  have h := maximalTarget_gaussian_of_brackets (fun k => pptTargets m n k X ε)
    (entropyCapacity m n hX.1.isHermitian.eigenvalues)
    (gaussianQuantile (varentropy hX.1.isHermitian.eigenvalues).toNNReal
      (ne_of_gt (Real.toNNReal_pos.mpr hv)) ε hε hε' / 2)
    (fun k K h => h.1)
    (pptTargets_upper_bracket m n hm hn X hX hv ε hε hε') (by
      intro z hz
      obtain ⟨K,hK,hlimit⟩ := universalTargets_lower_bracket m n hm hn X hX hv
        hC hCa hCb ε hε hε' z hz
      exact ⟨K,hK.mono (fun k hk => universalTargets_subset_pptTargets m n k hm hn X ε hk),hlimit⟩)
  constructor
  · exact h.1.mono (fun k hk => hk.2.2)
  · have hlimit := h.2
    rw [gaussianQuantile_scale, Real.coe_toNNReal _ hv.le] at hlimit
    exact hlimit

/-- The same inverse expansion is attained by the fixed common local protocol
function, without assuming that its fidelities are monotone in the target. -/
theorem universalFixedErrorTarget_gaussian (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (hv : 0 < varentropy hX.1.isHermitian.eigenvalues)
    (hC : 0 < entropyCapacity m n hX.1.isHermitian.eigenvalues)
    (hCa : entropyCapacity m n hX.1.isHermitian.eigenvalues < Real.log m)
    (hCb : entropyCapacity m n hX.1.isHermitian.eigenvalues < Real.log n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    (∀ᶠ k : ℕ in atTop,
      universalFixedErrorTarget m n k hm hn X ε ∈ universalTargets m n k hm hn X ε) ∧
    Tendsto (fun k : ℕ => (Real.log (universalFixedErrorTarget m n k hm hn X ε)-
      k*entropyCapacity m n hX.1.isHermitian.eigenvalues)/Real.sqrt k) atTop
      (𝓝 (Real.sqrt (varentropy hX.1.isHermitian.eigenvalues) *
        gaussianQuantile 1 one_ne_zero ε hε hε' / 2)) := by
  have h := maximalTarget_gaussian_of_brackets (fun k => universalTargets m n k hm hn X ε)
    (entropyCapacity m n hX.1.isHermitian.eigenvalues)
    (gaussianQuantile (varentropy hX.1.isHermitian.eigenvalues).toNNReal
      (ne_of_gt (Real.toNNReal_pos.mpr hv)) ε hε hε' / 2)
    (fun k K h => h.choose)
    (by
      intro z hz
      filter_upwards [pptTargets_upper_bracket m n hm hn X hX hv ε hε hε' z hz] with k hk
      intro K hK
      exact hk K (universalTargets_subset_pptTargets m n k hm hn X ε hK))
    (universalTargets_lower_bracket m n hm hn X hX hv hC hCa hCb ε hε hε')
  constructor
  · exact h.1.mono (fun k hk => hk.2.2)
  · have hlimit := h.2
    rw [gaussianQuantile_scale, Real.coe_toNNReal _ hv.le] at hlimit
    exact hlimit

end
end ExtractionDeviation
