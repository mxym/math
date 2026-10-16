import OperationalCompletion.Reservation
import OperationalCompletion.GridFamily

open scoped BigOperators ComplexOrder
open Matrix SymmetricSupport SpectralProtocol MinimaxProfile ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

def paperReservationDivisor (m n k : ℕ) : ℕ :=
  reservationDivisor (gridSectorCount k) (pureSupportRank m n k)

def reservationLocal (m n k a : ℕ) : ℕ := a^k/paperReservationDivisor m n k

def reservationMainLocal (m n k a : ℕ) : ℕ := a^k-gridSectorCount k*reservationLocal m n k a

def paperReservedPacking (m n k : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (ha : 0<reservationLocal m n k m) : ℕ :=
  reservedPacking (m^k) (n^k) (gridSectorCount k) (pureSupportRank m n k)
    (gridSectorCount_pos k) (pureSupportRank_pos m n k hm hn) (Nat.pow_le_pow_left hmn k) ha

theorem min_target_div_eq_profile (K d : ℕ) (hK : 0<K) : ((min K d:ℕ):ℝ)/K=profile d K := by
  have hKR : (0:ℝ)<K := Nat.cast_pos.mpr hK
  unfold profile
  by_cases h : K≤d
  · rw [min_eq_left h,min_eq_left ((one_le_div hKR).mpr (by exact_mod_cast h)),div_self hKR.ne']
  · have hdK : d≤K := le_of_not_ge h
    rw [min_eq_right hdK,min_eq_right ((div_le_one hKR).mpr (by exact_mod_cast hdK))]

theorem exists_reserved_geometric_protocol (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hmn : m≤n) (hK : 0<K) (hk : 0<k) (ha : 0<reservationLocal m n k m) :
    ∃ V : KrausPPTProtocol (m^k) (n^k) K,V.IsProductLocal ∧
      (∀ (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
        (j : ℕ),j<gridSectorCount k →
        ((gridWidth K (reservationLocal m n k m) j:ℝ)/K)*
          empiricalEntropyMass hX.1.isHermitian.eigenvalues k
            (sourceCutoff (m*n) k (reservationLocal m n k m) (reservationLocal m n k n)
              (gridWidth K (reservationLocal m n k m) j))≤V.fidelity (tensorInput m n k X)) ∧
      (∀ Y : Matrix (Fin (m^k)×Fin (n^k)) (Fin (m^k)×Fin (n^k)) ℂ,Y.PosSemidef →
        purePowerProjection m n k*Y*purePowerProjection m n k=Y →
          profile (paperReservedPacking m n k hm hn hmn ha) K*Y.trace.re≤V.fidelity Y) := by
  classical
  let J := gridSectorCount k
  let r := pureSupportRank m n k
  let a₀ := reservationLocal m n k m
  let b₀ := reservationLocal m n k n
  let A := reservationMainLocal m n k m
  let B := reservationMainLocal m n k n
  let c := paperReservedPacking m n k hm hn hmn ha
  have hJ : 0<J := gridSectorCount_pos k
  have hr : 0<r := pureSupportRank_pos m n k hm hn
  have hab : m^k≤n^k := Nat.pow_le_pow_left hmn k
  have hc := reservedPacking_properties (m^k) (n^k) J r hJ hr hab ha
  have ha₀c : a₀≤c := reservedSmall_le_packing (m^k) (n^k) J r hJ hr hab ha
  have ha₀b₀ : a₀≤b₀ := reservedSmall_mono (m^k) (n^k) J r hab
  let d₀ := min K c
  have hd₀ : 0<d₀ := lt_min hK hc.1
  have hr₀ : r≤(A/d₀)*(B/d₀) :=
    smaller_dimension_feasible hd₀ (min_le_right _ _) hc.2
  have hgrid0 : gridWidth K a₀ 0=min K a₀ := by
    simp [gridWidth,max_eq_right (show 1≤min K a₀ by omega)]
  have hdom : gridWidth K a₀ 0≤d₀ := by
    rw [hgrid0]
    exact min_le_min_left K ha₀c
  have hAbudget : A+J*a₀≤m^k := (reserved_dimensions_budget (m^k) J r hJ hr).le
  have hBbudget : B+J*b₀≤n^k := (reserved_dimensions_budget (n^k) J r hJ hr).le
  obtain ⟨V,hLocal,hV,hPure⟩ := reserved_universal_set_protocol m n k K J A B a₀ b₀ d₀ hm hn hK
    hd₀ (min_le_left _ _) (entropyGrid (m*n) k K a₀ b₀) (entropyGrid_mono _ _ _ _ _) rfl
    (gridWidth K a₀) (fun j _ => gridWidth_pos _ _ _)
    (fun j _ => (gridWidth_le K a₀ j hK ha).trans (min_le_left _ _))
    (gridWidth_antitone _ _) hdom hAbudget hBbudget hr₀ (by
      intro j hj
      exact sourceCutoff_budget (m*n) k a₀ b₀ _ (Nat.mul_pos hm hn) hk
        (gridWidth_pos _ _ _) ((gridWidth_le K a₀ j hK ha).trans (min_le_right _ _))
        (((gridWidth_le K a₀ j hK ha).trans (min_le_right _ _)).trans ha₀b₀))
  refine ⟨V,hLocal,?_,?_⟩
  · intro X hX j hj
    let G := fun i => ∑ w ∈ entropyGrid (m*n) k K a₀ b₀ i,iidLaw hX.1.isHermitian.eigenvalues k w
    have hG : Monotone G := by
      intro i l hil
      exact Finset.sum_le_sum_of_subset_of_nonneg (entropyGrid_mono _ _ _ _ _ hil)
        (fun w _ _ => iidLaw_nonneg _ hX.1.eigenvalues_nonneg k w)
    exact (weightedDifference_lower_prefix J j hj (fun i => (gridWidth K a₀ i:ℝ)/K) G
      (fun i => by positivity)
      (fun i l hil => div_le_div_of_nonneg_right (by exact_mod_cast gridWidth_antitone K a₀ hil)
        (Nat.cast_nonneg _)) hG (by simp [G,entropyGrid])).trans (hV X hX)
  · intro Y hY hsupport
    have h := hPure Y hY hsupport
    rwa [show d₀=min K c from rfl,min_target_div_eq_profile K c hK] at h

def reservedProtocol (m n k K : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n) (hK : 0<K) :
    KrausPPTProtocol (m^k) (n^k) K :=
  if h : 0<k ∧ 0<reservationLocal m n k m then
    (exists_reserved_geometric_protocol m n k K hm hn hmn hK h.1 h.2).choose
  else gridProtocol m n k K hm hn hmn hK

theorem reservedProtocol_isProductLocal (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hmn : m≤n) (hK : 0<K) : (reservedProtocol m n k K hm hn hmn hK).IsProductLocal := by
  unfold reservedProtocol
  split
  next h => exact (exists_reserved_geometric_protocol m n k K hm hn hmn hK h.1 h.2).choose_spec.1
  next h => exact gridProtocol_isProductLocal m n k K hm hn hmn hK

theorem reservedProtocol_guarantees (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hmn : m≤n) (hK : 0<K) (hk : 0<k) (ha : 0<reservationLocal m n k m) :
    (∀ (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
      (j : ℕ),j<gridSectorCount k →
      ((gridWidth K (reservationLocal m n k m) j:ℝ)/K)*
        empiricalEntropyMass hX.1.isHermitian.eigenvalues k
          (sourceCutoff (m*n) k (reservationLocal m n k m) (reservationLocal m n k n)
            (gridWidth K (reservationLocal m n k m) j))≤
              (reservedProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X)) ∧
    (∀ Y : Matrix (Fin (m^k)×Fin (n^k)) (Fin (m^k)×Fin (n^k)) ℂ,Y.PosSemidef →
      purePowerProjection m n k*Y*purePowerProjection m n k=Y →
        profile (paperReservedPacking m n k hm hn hmn ha) K*Y.trace.re≤
          (reservedProtocol m n k K hm hn hmn hK).fidelity Y) := by
  unfold reservedProtocol
  rw [dif_pos ⟨hk,ha⟩]
  exact (exists_reserved_geometric_protocol m n k K hm hn hmn hK hk ha).choose_spec.2

end
end OperationalCompletion
