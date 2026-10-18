import OperationalCompletion.ReservationCutoff
open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

theorem reserved_subcritical_rate (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (hRm : R<Real.log m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hH : entropy hX.1.isHermitian.eigenvalues<Real.log m+Real.log n-2*R) :
    Tendsto (fun k => (reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity
      (tensorInput m n k X)) atTop (nhds 1) := by
  let p := hX.1.isHermitian.eigenvalues
  have hp : ∀ i,0≤p i := hX.1.eigenvalues_nonneg
  have hs : ∑ i,p i=1 := density_eigenvalues_sum X hX
  have hmass := empiricalEntropyMass_tendsto_one_moving p hp hs
    (fun k => reservationSafeCutoff m n k (K k)) _ (reservationSafeCutoff_tendsto m n hm hn K hK R hR) hH
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmass tendsto_const_nhds
  · filter_upwards [reservationCap_eventually m n hm hn K hK R hR hRm,eventually_gt_atTop 0] with k hcap hk
    exact reservedProtocol_safe_mass m n k (K k) hm hn hmn (hK k) hk hcap X hX
  · exact Eventually.of_forall (fun k =>
      ((reservedProtocol m n k (K k) hm hn hmn (hK k)).fidelity_bounds (hK k) _
        (tensorInput_density m n k X hX)).2)

end
end OperationalCompletion
