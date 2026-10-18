import OperationalCompletion.CappedRate

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

theorem ppt_variational_exponential_upper (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (V : ∀ k,KrausPPTProtocol (m^k) (n^k) (K k))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,(V k).fidelity (tensorInput m n k X)≤
      Real.exp (-(k:ℝ)*(fidelityExponent hX.1.isHermitian.eigenvalues R-ε)) := by
  letI : Nonempty (Fin (m*n)) := ⟨⟨0,Nat.mul_pos hm hn⟩⟩
  apply capped_variational_eventually_exponential hX.1.isHermitian.eigenvalues
    hX.1.eigenvalues_nonneg (density_eigenvalues_sum X hX)
    (fun k => (V k).fidelity (tensorInput m n k X))
    (fun k => localBeta m k (K k)) (fun k => normalizedBudget m n k (K k))
    (fun k => localBeta_pos m k (K k) hm (hK k))
    (fun k => normalizedBudget_pos m n k (K k) hm hn (hK k))
    (fun k => KrausPPTProtocol.tensor_localBeta m n k (K k) (hK k) (V k) X hX) ?_
    _ _ (localBeta_log_rate m hm K hK R hR) (normalizedBudget_rate m n hm hn K hK R hR) ε hε
  intro α hα hα2 k
  simpa only [normalizedBudget,mul_assoc] using
    KrausPPTProtocol.tensor_capped_holder m n k (K k) hm (hK k) (V k) X hX α hα hα2

/-- The matching all-rate fidelity exponent for the single actual local
protocol, with every positive integer target and arbitrary varying rate-zero
sequence included. -/
theorem grid_fidelity_exponent (m n : ℕ) (hm : 2≤m) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ) (hR0 : 0≤R)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    Tendsto (fun k : ℕ => -Real.log
      ((gridProtocol m n k (K k) (by omega) (by omega) hmn (hK k)).fidelity (tensorInput m n k X))/k)
        atTop (nhds (fidelityExponent hX.1.isHermitian.eigenvalues R)) := by
  apply logarithmic_rate_of_exponential_bounds
  intro η hη
  filter_upwards [grid_variational_exponential_lower m n hm hmn K hK R hR0 hR X hX η hη,
    ppt_variational_exponential_upper m n (by omega) (by omega) K hK R hR
      (fun k => gridProtocol m n k (K k) (by omega) (by omega) hmn (hK k)) X hX η hη]
      with k hlo hhi
  exact ⟨hlo,hhi⟩

theorem optimum_variational_exponential_upper (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (C : ∀ k,KrausPPTProtocol (m^k) (n^k) (K k) → Prop)
    (hC : ∀ k,C k (gridProtocol m n k (K k) hm hn hmn (hK k)))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,protocolOptimum (C k) (tensorInput m n k X)≤
      Real.exp (-(k:ℝ)*(fidelityExponent hX.1.isHermitian.eigenvalues R-ε)) := by
  letI : Nonempty (Fin (m*n)) := ⟨⟨0,Nat.mul_pos hm hn⟩⟩
  apply capped_variational_eventually_exponential hX.1.isHermitian.eigenvalues
    hX.1.eigenvalues_nonneg (density_eigenvalues_sum X hX)
    (fun k => protocolOptimum (C k) (tensorInput m n k X))
    (fun k => localBeta m k (K k)) (fun k => normalizedBudget m n k (K k))
    (fun k => localBeta_pos m k (K k) hm (hK k))
    (fun k => normalizedBudget_pos m n k (K k) hm hn (hK k)) ?_ ?_
    _ _ (localBeta_log_rate m hm K hK R hR) (normalizedBudget_rate m n hm hn K hK R hR) ε hε
  · intro k
    exact protocolOptimum_le (C k) _ _ (hC k) _ (fun V _ =>
      KrausPPTProtocol.tensor_localBeta m n k (K k) (hK k) V X hX)
  · intro α hα hα2 k
    apply protocolOptimum_le (C k) _ _ (hC k)
    intro V _
    simpa only [normalizedBudget,mul_assoc] using
      KrausPPTProtocol.tensor_capped_holder m n k (K k) hm (hK k) V X hX α hα hα2

/-- The genuine state-aware suprema of the actual product-local class and
the full actual PPT class have the same complete exponent as the common
protocol. More generally this holds for every intermediate sub-class. -/
theorem optimal_fidelity_exponent (m n : ℕ) (hm : 2≤m) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ) (hR0 : 0≤R)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (C : ∀ k,KrausPPTProtocol (m^k) (n^k) (K k) → Prop)
    (hC : ∀ k,C k (gridProtocol m n k (K k) (by omega) (by omega) hmn (hK k)))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    Tendsto (fun k : ℕ => -Real.log (protocolOptimum (C k) (tensorInput m n k X))/k)
      atTop (nhds (fidelityExponent hX.1.isHermitian.eigenvalues R)) := by
  apply logarithmic_rate_of_exponential_bounds
  intro η hη
  filter_upwards [grid_variational_exponential_lower m n hm hmn K hK R hR0 hR X hX η hη,
    optimum_variational_exponential_upper m n (by omega) (by omega) hmn K hK R hR C hC X hX η hη]
      with k hlo hhi
  exact ⟨hlo.trans (protocolOptimum_ge (hK k) (C k) _ (tensorInput_density m n k X hX) _ (hC k)),hhi⟩

theorem fidelityExponent_renyi (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (p : Fin (m*n) → ℝ) (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1) (R : ℝ) :
    fidelityExponent p R=max 0 (R-Real.log m)+
      ⨆ α : {α : ℝ // α∈Set.Icc (1:ℝ) 2},
        (α.1-1)/α.1*(renyiEntropy p α.1-cappedEntropyRate m n R) := by
  letI : Nonempty (Fin (m*n)) := ⟨⟨0,Nat.mul_pos hm hn⟩⟩
  unfold fidelityExponent
  congr 1
  exact nonnegative_escort_renyi_variational_identity p hp hs _

end
end OperationalCompletion
