import MinimaxProfile.Protocol
import UniversalOrbit.Mass
import SpectralProtocol.GeneralPureGuarantee
import SpectralProtocol.MassLower

open scoped BigOperators ComplexOrder
open Matrix SymmetricSupport
namespace MinimaxProfile
noncomputable section

def tensorInput (m n k : ℕ) (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) :
    Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ :=
  SpectralProtocol.bipartitePowerTransport m n k (ExtractionSpectrum.tensorMatrix X k)

theorem tensorInput_density (m n k : ℕ) (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1) : APPT.Quantum.IsDensity (tensorInput m n k X) := by
  have h := ExtractionSpectrum.tensorMatrix_density X hX k
  refine ⟨h.1.submatrix (SpectralProtocol.bipartitePowerCoordinates m n k).symm,?_⟩
  rw [tensorInput, SpectralProtocol.bipartitePowerTransport, SpectralProtocol.reindex_trace]
  exact h.2

def tensorProjection (m n k : ℕ) (S : Finset (Word (m*n) k)) :
    Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ :=
  SpectralProtocol.bipartitePowerTransport m n k (UniversalOrbit.universalProjection (m*n) k S)

theorem tensorProjection_hermitian (m n k : ℕ) (S : Finset (Word (m*n) k)) :
    (tensorProjection m n k S).IsHermitian :=
  (UniversalOrbit.universalProjection_hermitian (m*n) k S).reindex
    (SpectralProtocol.bipartitePowerCoordinates m n k)

theorem tensorProjection_idempotent (m n k : ℕ) (S : Finset (Word (m*n) k)) :
    tensorProjection m n k S * tensorProjection m n k S = tensorProjection m n k S := by
  exact (map_mul (SpectralProtocol.bipartitePowerTransport m n k) _ _).symm.trans
    (congrArg (SpectralProtocol.bipartitePowerTransport m n k)
      (UniversalOrbit.universalProjection_idempotent (m*n) k S))

theorem tensorProjection_rank_le (m n k : ℕ) (S : Finset (Word (m*n) k)) :
    (tensorProjection m n k S).rank ≤ S.card * ((m*n)*(m*n)+k-1).choose k := by
  change (Matrix.reindex (SpectralProtocol.bipartitePowerCoordinates m n k)
    (SpectralProtocol.bipartitePowerCoordinates m n k)
    (UniversalOrbit.universalProjection (m*n) k S)).rank ≤ _
  rw [Matrix.rank_reindex]
  exact UniversalOrbit.universalProjection_rank_le (m*n) k S

theorem tensorProjection_mass_ge (m n k : ℕ) (S : Finset (Word (m*n) k))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1) :
    (∑ w ∈ S, ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w) ≤
      (tensorProjection m n k S * tensorInput m n k X).trace.re := by
  unfold tensorProjection tensorInput
  rw [← map_mul]
  change _ ≤ (Matrix.reindexAlgEquiv ℂ ℂ (SpectralProtocol.bipartitePowerCoordinates m n k)
    (UniversalOrbit.universalProjection (m*n) k S * ExtractionSpectrum.tensorMatrix X k)).trace.re
  rw [SpectralProtocol.reindex_trace]
  exact UniversalOrbit.universalProjection_mass_ge (m*n) k S X hX

theorem projection_mass_protocol (a b K : ℕ) (hK : 0 < K)
    (P : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P) (hr : P.rank ≤ (a/K)*(b/K)) :
    ∃ V : KrausPPTProtocol a b K,
      ∀ X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ, X.PosSemidef →
        (P*X).trace.re ≤ V.fidelity X := by
  obtain ⟨U,A,B,hA,hB,h⟩ := SpectralProtocol.finite_projection_mass_lower a b K hK P hP hPP hr
  refine ⟨localProtocol U A B hA hB,?_⟩
  intro X hX
  rw [localProtocol_fidelity]
  exact h X hX

/-- One fixed original-space protocol precedes every unknown density and
captures the specified word mass. Its original unitary and both complete local
channels are constructed by the proof; no spectral basis is an input resource. -/
theorem universal_set_protocol (m n k K : ℕ) (hK : 0 < K) (S : Finset (Word (m*n) k))
    (hbudget : S.card * ((m*n)*(m*n)+k-1).choose k ≤ (m^k/K)*(n^k/K)) :
    ∃ V : KrausPPTProtocol (m^k) (n^k) K,
      ∀ (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace = 1),
        (∑ w ∈ S, ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w) ≤
          V.fidelity (tensorInput m n k X) := by
  obtain ⟨V,hV⟩ := projection_mass_protocol (m^k) (n^k) K hK
    (tensorProjection m n k S) (tensorProjection_hermitian m n k S)
    (tensorProjection_idempotent m n k S) ((tensorProjection_rank_le m n k S).trans hbudget)
  refine ⟨V,?_⟩
  intro X hX
  exact (tensorProjection_mass_ge m n k S X hX).trans (hV _ (tensorInput_density m n k X hX).1)

end
end MinimaxProfile
