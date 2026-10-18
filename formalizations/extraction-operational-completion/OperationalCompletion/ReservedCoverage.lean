import OperationalCompletion.ReservationCutoff
open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

theorem reservedProtocol_test_width (m n k K d : ℕ) (hm : 0<m) (hn : 0<n)
    (hmn : m≤n) (hK : 0<K) (hk : 0<k) (hd : 0<d)
    (hdK : d≤K) (hda : d≤reservationLocal m n k m)
    (hcover : m^k<2^gridSectorCount k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    ((d:ℝ)/K)*empiricalEntropyMass hX.1.isHermitian.eigenvalues k
      (sourceCutoff (m*n) k (reservationLocal m n k m) (reservationLocal m n k n) (2*d)) ≤
        (reservedProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X) := by
  have hmin : min K (reservationLocal m n k m)<2^gridSectorCount k := by
    apply lt_of_le_of_lt _ hcover
    exact (min_le_right _ _).trans (Nat.div_le_self _ _)
  obtain ⟨j,hj,hlo,hhi⟩ := gridWidth_covers K (reservationLocal m n k m) (gridSectorCount k) d
    hd (le_min hdK hda) hmin
  have hcut := sourceCutoff_antitone (m*n) k (reservationLocal m n k m) (reservationLocal m n k n)
    (gridWidth K (reservationLocal m n k m) j) (2*d) (gridWidth_pos _ _ _) hhi.le
  have hmass := empiricalEntropyMass_mono hX.1.isHermitian.eigenvalues
    hX.1.eigenvalues_nonneg k hcut
  have hweight : (d:ℝ)/K≤(gridWidth K (reservationLocal m n k m) j:ℝ)/K :=
    div_le_div_of_nonneg_right (by exact_mod_cast hlo) (Nat.cast_nonneg K)
  exact (mul_le_mul hweight hmass
    (empiricalEntropyMass_nonneg _ hX.1.eigenvalues_nonneg _ _) (by positivity)).trans
    (reservedProtocol_prefix m n k K hm hn hmn hK hk (hd.trans_le hda) X hX j hj)

end
end OperationalCompletion
