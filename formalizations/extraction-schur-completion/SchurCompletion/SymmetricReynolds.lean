import SchurCompletion.FiniteGramSystem
import Mathlib.Data.List.FinRange

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem occupation_position_comp (D k : ℕ) (w : Word D k) (σ : Equiv.Perm (Fin k)) :
    occupation D k (w ∘ σ) = occupation D k w := by
  apply Subtype.ext
  change (((List.Vector.ofFn (w ∘ σ)).toList : List (Fin D)) : Multiset (Fin D)) =
    ((List.Vector.ofFn w).toList : Multiset (Fin D))
  simpa only [List.Vector.toList_ofFn] using Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm w)

theorem copyPermutation_mul_symmetricProjector (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    copyPermutationMatrix D k σ * symmetricProjector D k = symmetricProjector D k := by
  unfold copyPermutationMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul]
  ext w v
  change partitionProjector (occupation D k) (w ∘ σ) v =
    partitionProjector (occupation D k) w v
  simp only [partitionProjector_apply,occupation_position_comp]

theorem symmetricProjector_mul_copyPermutation (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    symmetricProjector D k * copyPermutationMatrix D k σ = symmetricProjector D k := by
  have h := congrArg Matrix.conjTranspose (copyPermutation_mul_symmetricProjector D k σ⁻¹)
  simpa only [Matrix.conjTranspose_mul,(symmetricProjector_hermitian D k).eq,
    copyPermutationMatrix_star,inv_inv] using h

def copyPermutationAverage (D k : ℕ) : Matrix (Word D k) (Word D k) ℂ :=
  (Fintype.card (Equiv.Perm (Fin k)) : ℂ)⁻¹ • ∑ σ, copyPermutationMatrix D k σ

theorem copyPermutation_mul_average (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    copyPermutationMatrix D k σ * copyPermutationAverage D k = copyPermutationAverage D k := by
  simp only [copyPermutationAverage,Matrix.mul_smul,Matrix.mul_sum,copyPermutationMatrix_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft σ) (copyPermutationMatrix D k)

theorem symmetricProjector_mul_average (D k : ℕ) :
    symmetricProjector D k * copyPermutationAverage D k = symmetricProjector D k := by
  have hn : (Fintype.card (Equiv.Perm (Fin k)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [copyPermutationAverage,Matrix.mul_smul,Matrix.mul_sum,
    symmetricProjector_mul_copyPermutation,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ,← mul_smul,inv_mul_cancel₀ hn,one_smul]

theorem symmetricProjector_average_fixed (D k : ℕ) :
    symmetricProjector D k * copyPermutationAverage D k = copyPermutationAverage D k := by
  ext w v
  change (symmetricProjector D k).mulVec (fun x => copyPermutationAverage D k x v) w = _
  have h := partitionProjector_mulVec_constant (occupation D k) (occupation_surjective D k)
    (fun x => copyPermutationAverage D k x v) (by
      intro x y hxy
      obtain ⟨σ,hσ⟩ := exists_position_permutation_of_occupation_eq x y hxy
      have h := congrFun (congrFun (copyPermutation_mul_average D k σ) x) v
      change (copyPermutationMatrix D k σ * copyPermutationAverage D k) x v = _ at h
      unfold copyPermutationMatrix at h
      rw [PEquiv.toMatrix_toPEquiv_mul] at h
      change copyPermutationAverage D k (x ∘ σ) v = copyPermutationAverage D k x v at h
      have heq : x ∘ σ = y := funext hσ
      rw [heq] at h
      exact h.symm)
  exact congrFun h w

/-- The occupation projector is exactly the finite Reynolds average of actual
 tensor-position permutations, with no orbit-stabilizer multiplicities assumed. -/
theorem symmetricProjector_eq_copyPermutationAverage (D k : ℕ) :
    symmetricProjector D k = copyPermutationAverage D k :=
  (symmetricProjector_mul_average D k).symm.trans (symmetricProjector_average_fixed D k)

theorem symmetricProjector_mem_permutationSpan (D k : ℕ) :
    symmetricProjector D k ∈ permutationSpan D k := by
  rw [symmetricProjector_eq_copyPermutationAverage,copyPermutationAverage]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ _
  exact Submodule.subset_span ⟨σ,rfl⟩

theorem symmetricProjector_trace_choose (D k : ℕ) :
    (symmetricProjector D k).trace = ((D+k-1).choose k : ℂ) := by
  rw [symmetricProjector_trace]
  congr 1
  simpa using Sym.card_sym_eq_choose (α := Fin D) k

end
end ExtractionSchur
