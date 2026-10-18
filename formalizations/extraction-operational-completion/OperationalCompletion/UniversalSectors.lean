import OperationalCompletion.WeightedCDF

open scoped BigOperators ComplexOrder
open Matrix SymmetricSupport MinimaxProfile
namespace OperationalCompletion
noncomputable section

theorem universalProjection_empty (D k : ℕ) :
    UniversalOrbit.universalProjection D k ∅ = 0 := by
  ext x w
  have h := UniversalOrbit.universalProjection_column_mem D k ∅ w
  have hz : (UniversalOrbit.universalProjection D k ∅).col w = 0 := by
    simpa [UniversalOrbit.universalSpace] using h
  exact congrFun hz x

theorem tensorProjection_empty (m n k : ℕ) : tensorProjection m n k ∅ = 0 := by
  unfold tensorProjection
  rw [universalProjection_empty,map_zero]

theorem tensorProjection_nested (m n k : ℕ)
    (S T : Finset (Word (m*n) k)) (h : S ⊆ T) :
    tensorProjection m n k S * tensorProjection m n k T = tensorProjection m n k S ∧
    tensorProjection m n k T * tensorProjection m n k S = tensorProjection m n k S := by
  have hnest := UniversalOrbit.universalProjection_nested (m*n) k S T h
  constructor
  · unfold tensorProjection
    rw [← map_mul,hnest.2]
  · unfold tensorProjection
    rw [← map_mul,hnest.1]

theorem tensorProjection_commutes (m n k : ℕ) (S : Finset (Word (m*n) k))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) :
    tensorProjection m n k S * tensorInput m n k X =
      tensorInput m n k X * tensorProjection m n k S := by
  unfold tensorProjection tensorInput
  rw [← map_mul,← map_mul,UniversalOrbit.universalProjection_commutes_tensor]

/-- One actual unitary and complete pair of local Kraus channels simultaneously
realize decreasing weights on a nested family of spectrum-independent source
spaces. Only integer sector budgets are required; no Schur decomposition or
supplied spectral-mass certificate occurs in the hypotheses. -/
theorem nested_universal_set_protocol (m n k K J a₀ b₀ : ℕ) (hK : 0<K)
    (S : ℕ → Finset (Word (m*n) k)) (hS : Monotone S) (hS0 : S 0=∅)
    (d : ℕ → ℕ) (hd : ∀ j<J,0<d j) (hdk : ∀ j<J,d j≤K) (hdec : Antitone d)
    (ha : J*a₀≤m^k) (hb : J*b₀≤n^k)
    (hbudget : ∀ j<J,(S (j+1)).card*((m*n)*(m*n)+k-1).choose k ≤
      (a₀/d j)*(b₀/d j)) :
    ∃ V : KrausPPTProtocol (m^k) (n^k) K,
      V.IsProductLocal ∧
      ∀ (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1),
        weightedDifference J (fun j => (d j:ℝ)/K)
          (fun j => ∑ w ∈ S j, ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w)
          ≤ V.fidelity (tensorInput m n k X) := by
  classical
  let P := fun j => tensorProjection m n k (S j)
  have hPH : ∀ j,(P j).IsHermitian := fun j => tensorProjection_hermitian m n k (S j)
  have hPP : ∀ j,P j*P j=P j := fun j => tensorProjection_idempotent m n k (S j)
  have hnest : ∀ i j,i≤j → P i*P j=P i :=
    fun i j hij => (tensorProjection_nested m n k _ _ (hS hij)).1
  have hnest' : ∀ i j,i≤j → P j*P i=P i :=
    fun i j hij => (tensorProjection_nested m n k _ _ (hS hij)).2
  have h0 : P 0=0 := by simp [P,hS0,tensorProjection_empty]
  have hsectorH : ∀ j : Fin J,(chainSector P j).IsHermitian :=
    fun j => projectionDifference_hermitian _ _ (hPH j) (hPH (j+1))
  have hsectorP : ∀ j : Fin J,chainSector P j*chainSector P j=chainSector P j :=
    fun j => projectionDifference_idempotent _ _ (hPP j) (hPP (j+1))
      (hnest _ _ (by omega)) (hnest' _ _ (by omega))
  have hsectorOrth : ∀ i j : Fin J,i≠j → chainSector P i*chainSector P j=0 := by
    intro i j hij
    exact chainSector_orthogonal P hPH hnest i j (fun h => hij (Fin.ext h))
  have hsectorRank : ∀ j : Fin J,(chainSector P j).rank ≤ (a₀/d j)*(b₀/d j) := by
    intro j
    exact (projectionDifference_rank_le _ _ (hPP (j+1)) (hnest _ _ (by omega))).trans
      ((tensorProjection_rank_le m n k (S (j+1))).trans (hbudget j j.isLt))
  obtain ⟨U,A,B,hA,hB,hV⟩ := SpectralProtocol.finite_multisector_projection_mass_lower
    (m^k) (n^k) a₀ b₀ K J hK (fun j => d j)
    (fun j => hd j j.isLt) (fun j => hdk j j.isLt) ha hb
    (fun j => chainSector P j) hsectorH hsectorP hsectorOrth hsectorRank
  refine ⟨localProtocol U A B hA hB,localProtocol_isProductLocal U A B hA hB,?_⟩
  intro X hX
  have hcomm : (∑ j : Fin J,chainSector P j)*tensorInput m n k X =
      tensorInput m n k X*(∑ j : Fin J,chainSector P j) := by
    rw [chainSector_sum,h0,sub_zero]
    exact tensorProjection_commutes m n k (S J) X
  have hv := hV _ (tensorInput_density m n k X hX).1 hcomm
  have hmass0 : (P 0*tensorInput m n k X).trace.re=0 := by simp [h0]
  have hclass0 : (∑ w ∈ S 0,ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w)=0 := by
    rw [hS0]
    simp
  have hcmp := weightedDifference_mono J (fun j => (d j:ℝ)/K)
    (fun j => (P j*tensorInput m n k X).trace.re)
    (fun j => ∑ w ∈ S j,ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun j _ => div_le_div_of_nonneg_right (by exact_mod_cast hdec (by omega : j≤j+1))
      (Nat.cast_nonneg _)) hmass0 hclass0
    (fun j _ => tensorProjection_mass_ge m n k (S j) X hX)
  apply hcmp.trans
  rw [localProtocol_fidelity]
  convert hv using 1
  · unfold weightedDifference chainSector projectionDifference
    apply Finset.sum_congr rfl
    intro j _
    rw [sub_mul,Matrix.trace_sub,Complex.sub_re]
  · rfl

end
end OperationalCompletion
