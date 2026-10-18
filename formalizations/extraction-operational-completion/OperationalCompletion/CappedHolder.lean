import OperationalCompletion.OptimalFidelity
import OperationalCompletion.FidelityExponent

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

def localBeta (m k K : ℕ) : ℝ := min 1 ((m:ℝ)^k/K)

theorem localBeta_pos (m k K : ℕ) (hm : 0<m) (hK : 0<K) : 0<localBeta m k K := by
  have hmR : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have hKR : (0:ℝ)<K := Nat.cast_pos.mpr hK
  exact lt_min zero_lt_one (div_pos (pow_pos hmR k) hKR)

theorem KrausPPTProtocol.tensor_localBeta (m n k K : ℕ) (hK : 0<K)
    (V : KrausPPTProtocol (m^k) (n^k) K)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    V.fidelity (tensorInput m n k X)≤localBeta m k K := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  have hlocal := ExtractionLocalCap.kraus_target_overlap_unitary_local_cap V.A V.complete
    V.ptPositive (tensorInput m n k X) (tensorInput_density m n k X hX) V.U
  apply le_min (V.fidelity_bounds hK _ (tensorInput_density m n k X hX)).2
  simpa only [KrausPPTProtocol.fidelity,overlap,Fintype.card_fin,Nat.cast_pow] using hlocal

theorem KrausPPTProtocol.tensor_capped_holder (m n k K : ℕ)
    (hm : 0<m) (hK : 0<K) (V : KrausPPTProtocol (m^k) (n^k) K)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (α : ℝ) (hα : 1<α) (hα2 : α≤2) :
    V.fidelity (tensorInput m n k X)≤localBeta m k K *
      (((partition hX.1.isHermitian.eigenvalues α)^k)^(1/α)*
        (tensorBudget m n k K/(localBeta m k K)^2)^((α-1)/α)) := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  let e := (SpectralProtocol.bipartitePowerCoordinates m n k).symm
  let p := hX.1.isHermitian.eigenvalues
  let q := iidLaw p k ∘ e
  let W := reindexUnitary e (tensorUnitary hX.1.isHermitian.eigenvectorUnitary k)
  have hqp (w) : 0≤q w := iidLaw_nonneg p hX.1.eigenvalues_nonneg k _
  have hsp : (V.U:Matrix _ _ ℂ)*tensorInput m n k X*(V.U:Matrix _ _ ℂ)ᴴ =
      ((V.U*W:Matrix.unitaryGroup _ ℂ):Matrix _ _ ℂ)*
        Matrix.diagonal (fun w => (q w:ℂ))*
          ((V.U*W:Matrix.unitaryGroup _ ℂ):Matrix _ _ ℂ)ᴴ := by
    rw [tensorInput_spectral m n k X hX.1.isHermitian]
    simp only [Submonoid.coe_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rfl
  have hM := Extraction.targetEffect_rains V.A V.complete V.ptPositive
  have hcap : (localBeta m k K • (1:Matrix (Fin (m^k)×Fin (n^k)) _ ℂ)-
      Extraction.targetEffect V.A).PosSemidef := by
    by_cases h : 1≤((m:ℝ)^k/K)
    · simpa only [localBeta,min_eq_left h,one_smul] using hM.2.1
    · have hlocal := ExtractionLocalCap.rainsEffect_local_order_cap K (Extraction.targetEffect V.A)
        (by simpa only [Fintype.card_fin] using hM)
      simpa only [localBeta,min_eq_right (le_of_not_ge h),Fintype.card_fin,Nat.cast_pow] using hlocal
  have hb : (Extraction.targetEffect V.A*Extraction.targetEffect V.A).trace.re≤
      tensorBudget m n k K := by
    simpa only [tensorBudget,Fintype.card_fin,Nat.cast_pow] using
      Extraction.rainsEffect_trace_square_le _ _ hM
  have h := diagonalized_effect_holder_bound q hqp (V.U*W) (Extraction.targetEffect V.A)
    hM.1 (localBeta m k K) (localBeta_pos m k K hm hK) hcap _ α hb hα hα2
  have hpart : partition q α=(partition p α)^k := by
    rw [partition_reindex (iidLaw p k) e α]
    exact iidLaw_partition p hX.1.eigenvalues_nonneg k α
  unfold KrausPPTProtocol.fidelity overlap
  rw [Extraction.target_overlap_eq,hsp]
  simpa only [hpart] using h

end
end OperationalCompletion
