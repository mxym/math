import OperationalCompletion.PureSector

open scoped BigOperators ComplexOrder
open Matrix SymmetricSupport SpectralProtocol MinimaxProfile
namespace OperationalCompletion
noncomputable section

def nonsymmetricTensorProjection (m n k : ℕ) (S : Finset (Word (m*n) k)) :
    Matrix (Fin (m^k)×Fin (n^k)) (Fin (m^k)×Fin (n^k)) ℂ :=
  bipartitePowerTransport m n k (nonsymmetricProjection (m*n) k S)

theorem nonsymmetricTensorProjection_hermitian (m n k : ℕ) (S : Finset (Word (m*n) k)) :
    (nonsymmetricTensorProjection m n k S).IsHermitian :=
  (nonsymmetricProjection_hermitian (m*n) k S).reindex (bipartitePowerCoordinates m n k)

theorem nonsymmetricTensorProjection_idempotent (m n k : ℕ) (S : Finset (Word (m*n) k)) :
    nonsymmetricTensorProjection m n k S*nonsymmetricTensorProjection m n k S=
      nonsymmetricTensorProjection m n k S := by
  unfold nonsymmetricTensorProjection
  rw [←map_mul,nonsymmetricProjection_idempotent]

theorem nonsymmetricTensorProjection_rank_le (m n k : ℕ) (S : Finset (Word (m*n) k)) :
    (nonsymmetricTensorProjection m n k S).rank≤S.card*((m*n)*(m*n)+k-1).choose k := by
  change (Matrix.reindex (bipartitePowerCoordinates m n k) (bipartitePowerCoordinates m n k)
    (nonsymmetricProjection (m*n) k S)).rank≤_
  rw [Matrix.rank_reindex]
  exact nonsymmetricProjection_rank_le _ _ _

theorem nonsymmetricTensorProjection_empty (m n k : ℕ) : nonsymmetricTensorProjection m n k ∅=0 := by
  unfold nonsymmetricTensorProjection nonsymmetricProjection
  simp

theorem nonsymmetricTensorProjection_nested (m n k : ℕ) (S T : Finset (Word (m*n) k)) (h : S⊆T) :
    nonsymmetricTensorProjection m n k S*nonsymmetricTensorProjection m n k T=nonsymmetricTensorProjection m n k S ∧
      nonsymmetricTensorProjection m n k T*nonsymmetricTensorProjection m n k S=nonsymmetricTensorProjection m n k S := by
  have hh := nonsymmetricProjection_nested (m*n) k S T h
  constructor <;> unfold nonsymmetricTensorProjection
  · rw [←map_mul,hh.1]
  · rw [←map_mul,hh.2]

theorem nonsymmetricTensorProjection_orthogonal_pure (m n k : ℕ) (S : Finset (Word (m*n) k)) :
    purePowerProjection m n k*nonsymmetricTensorProjection m n k S=0 ∧
      nonsymmetricTensorProjection m n k S*purePowerProjection m n k=0 := by
  have h := nonsymmetricProjection_orthogonal_symmetric (m*n) k S
  constructor <;> unfold purePowerProjection nonsymmetricTensorProjection
  · rw [←map_mul,h.1,map_zero]
  · rw [←map_mul,h.2,map_zero]

theorem purePowerProjection_commutes_tensorInput (m n k : ℕ) (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) :
    purePowerProjection m n k*tensorInput m n k X=tensorInput m n k X*purePowerProjection m n k := by
  unfold purePowerProjection tensorInput
  rw [←map_mul,←map_mul,symmetricProjector_commutes_tensorMatrix]

theorem nonsymmetricTensorProjection_commutes (m n k : ℕ) (S : Finset (Word (m*n) k))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) :
    nonsymmetricTensorProjection m n k S*tensorInput m n k X=
      tensorInput m n k X*nonsymmetricTensorProjection m n k S := by
  unfold nonsymmetricTensorProjection tensorInput
  rw [←map_mul,←map_mul,nonsymmetricProjection_commutes_tensorMatrix]

theorem purePowerProjection_posSemidef (m n k : ℕ) : (purePowerProjection m n k).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (purePowerProjection m n k)
  rwa [(purePowerProjection_hermitian m n k).eq,purePowerProjection_idempotent] at h

theorem liftedProjection_mass_ge (m n k : ℕ) (S : Finset (Word (m*n) k))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    (∑ w ∈ S,ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w)≤
      ((purePowerProjection m n k+nonsymmetricTensorProjection m n k S)*tensorInput m n k X).trace.re := by
  classical
  by_cases hS : S.Nonempty
  · have he : nonsymmetricTensorProjection m n k S=tensorProjection m n k S-purePowerProjection m n k := by
      unfold nonsymmetricTensorProjection nonsymmetricProjection tensorProjection purePowerProjection
      rw [if_pos hS,map_sub]
    rw [he,show purePowerProjection m n k+(tensorProjection m n k S-purePowerProjection m n k)=
      tensorProjection m n k S by abel]
    exact tensorProjection_mass_ge m n k S X hX
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [he,nonsymmetricTensorProjection_empty,add_zero]
    simp only [Finset.sum_empty]
    exact Extraction.positive_product_trace_re _ _ (purePowerProjection_posSemidef m n k)
      (tensorInput_density m n k X hX).1

end
end OperationalCompletion
