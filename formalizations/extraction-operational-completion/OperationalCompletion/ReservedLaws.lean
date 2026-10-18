import OperationalCompletion.ReservedGaussian
import OperationalCompletion.ReservedExponent
import OperationalCompletion.Reliability
import OperationalCompletion.SharpFidelity
import OperationalCompletion.EventualExact
open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

theorem reserved_eventually_exact (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (hRm : R<Real.log m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hRank : Real.log X.rank<Real.log m+Real.log n-2*R) :
    ∀ᶠ k : ℕ in atTop,
      (reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity (tensorInput m n k X)=1 := by
  letI : Nonempty (Fin (m*n)) := ⟨⟨0,Nat.mul_pos hm hn⟩⟩
  have hcut := (reservationSafeCutoff_tendsto m n hm hn K hK R hR).eventually_const_lt hRank
  filter_upwards [hcut,reservationCap_eventually m n hm hn K hK R hR hRm,eventually_gt_atTop 0]
    with k hcut hcap hk
  have hmass := reservedProtocol_safe_mass m n k (K k) hm hn hmn (hK k) hk hcap X hX
  have hr : Fintype.card (PositiveSupport hX.1.isHermitian.eigenvalues)=X.rank :=
    density_positiveSupport_card_eq_rank X hX.1
  have hmone := empiricalEntropyMass_eq_one_of_support hX.1.isHermitian.eigenvalues
    hX.1.eigenvalues_nonneg (density_eigenvalues_sum X hX) k hk (reservationSafeCutoff m n k (K k)) (by
      rw [hr]
      exact hcut.le)
  rw [hmone] at hmass
  exact le_antisymm
    ((reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity_bounds (hK k) _
      (tensorInput_density m n k X hX)).2 hmass

theorem reserved_reliability_limit (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (hRm : R<Real.log m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hlo : entropy hX.1.isHermitian.eigenvalues<Real.log m+Real.log n-2*R)
    (hhi : Real.log m+Real.log n-2*R<Real.log X.rank) :
    Tendsto (fun k : ℕ => -Real.log (1-
      (reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity (tensorInput m n k X))/k)
      atTop (nhds (strictDirectExponent hX.1.isHermitian.eigenvalues
        (Real.log m+Real.log n-2*R))) := by
  apply logarithmic_rate_of_exponential_bounds
  intro η hη
  filter_upwards [ppt_strict_direct_error_lower m n hm hn K hK R hR X hX hlo hhi η hη,
    reserved_strict_direct_error_upper m n hm hn hmn K hK R hR hRm X hX hlo hhi η hη]
      with k hlo hhi
  exact ⟨hlo _,hhi⟩

theorem reserved_fidelity_exponent (m n : ℕ) (hm : 2≤m) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ) (hR0 : 0≤R)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    Tendsto (fun k : ℕ => -Real.log
      ((reservedProtocol m n k (K k) (by omega) (by omega) hmn (hK k)).fidelity (tensorInput m n k X))/k)
        atTop (nhds (fidelityExponent hX.1.isHermitian.eigenvalues R)) := by
  apply logarithmic_rate_of_exponential_bounds
  intro η hη
  filter_upwards [reserved_variational_exponential_lower m n hm hmn K hK R hR0 hR X hX η hη,
    ppt_variational_exponential_upper m n (by omega) (by omega) K hK R hR
      (fun k => reservedProtocol m n k (K k) (by omega) (by omega) hmn (hK k)) X hX η hη]
      with k hlo hhi
  exact ⟨hlo,hhi⟩

end
end OperationalCompletion
