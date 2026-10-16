import SchurCompletion.BoundaryProjection

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

/-- Actual central cycle-character operator on the original tensor coordinates. -/
def cycleOperator (D t k : ℕ) : Matrix (Word D k) (Word D k) ℂ :=
  ∑ σ : Equiv.Perm (Fin k), (t : ℂ)^positionCycleCount k σ • copyPermutationMatrix D k σ⁻¹

def permutationFrame (D k : ℕ) :
    Matrix (Word D k) (Word D k) ℂ →ₗ[ℂ] Matrix (Word D k) (Word D k) ℂ where
  toFun A := ∑ σ : Equiv.Perm (Fin k),
    ((copyPermutationMatrix D k σ)ᴴ * A).trace • copyPermutationMatrix D k σ
  map_add' A B := by simp only [Matrix.mul_add,Matrix.trace_add,add_smul,Finset.sum_add_distrib]
  map_smul' a A := by
    simp only [Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

theorem permutationFrame_mem (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    permutationFrame D k A ∈ permutationSpan D k := by
  apply Submodule.sum_mem
  intro σ _
  exact Submodule.smul_mem (permutationSpan D k) _ (Submodule.subset_span ⟨σ,rfl⟩)

theorem permutationFrame_generator (D k : ℕ) (τ : Equiv.Perm (Fin k)) :
    permutationFrame D k (copyPermutationMatrix D k τ) =
      copyPermutationMatrix D k τ * cycleOperator D D k := by
  change (∑ σ, ((copyPermutationMatrix D k σ)ᴴ * copyPermutationMatrix D k τ).trace •
    copyPermutationMatrix D k σ) = _
  calc
    _ = ∑ η : Equiv.Perm (Fin k),
        ((copyPermutationMatrix D k (τ*η⁻¹))ᴴ * copyPermutationMatrix D k τ).trace •
          copyPermutationMatrix D k (τ*η⁻¹) := by
      exact (Equiv.sum_comp ((Equiv.inv (Equiv.Perm (Fin k))).trans (Equiv.mulLeft τ)) _).symm
    _ = _ := by
      simp only [copyPermutation_cycle_gram,_root_.mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,
        mul_one,copyPermutationMatrix_mul,cycleOperator,Matrix.mul_sum,Matrix.mul_smul]

/-- The full permutation Gram frame is right multiplication by one actual
 central matrix on the permutation algebra. No generator independence is used. -/
theorem permutationFrame_eq_mul_cycleOperator (D k : ℕ)
    (A : Matrix (Word D k) (Word D k) ℂ) (hA : A ∈ permutationSpan D k) :
    permutationFrame D k A = A * cycleOperator D D k := by
  change A ∈ Submodule.span ℂ (Set.range (copyPermutationMatrix D k)) at hA
  induction hA using Submodule.span_induction with
  | mem x hx => obtain ⟨τ,rfl⟩ := hx; exact permutationFrame_generator D k τ
  | zero => simp
  | add A B hA hB iA iB => simp only [map_add,Matrix.add_mul,iA,iB]
  | smul a A hA iA => simp only [map_smul,Matrix.smul_mul,iA]

theorem trace_adjoint_pairing (D k : ℕ)
    (A B : Matrix (Word D k) (Word D k) ℂ) :
    (Aᴴ*B).trace = star ((Bᴴ*A).trace) := by
  rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

theorem permutationFrame_pairing_nonneg_sum (D k : ℕ)
    (A : Matrix (Word D k) (Word D k) ℂ) :
    (Aᴴ * permutationFrame D k A).trace.re =
      ∑ σ : Equiv.Perm (Fin k), Complex.normSq ((copyPermutationMatrix D k σ)ᴴ*A).trace := by
  simp only [permutationFrame,LinearMap.coe_mk,AddHom.coe_mk,Matrix.mul_sum,Matrix.mul_smul,
    Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [trace_adjoint_pairing D k A (copyPermutationMatrix D k σ)]
  change ((((copyPermutationMatrix D k σ)ᴴ*A).trace *
    (starRingEnd ℂ) ((copyPermutationMatrix D k σ)ᴴ*A).trace).re) = _
  rw [Complex.mul_conj]
  rfl

/-- The internally constructed finite frame is faithful on its actual span. -/
theorem permutationFrame_eq_zero_of_mem (D k : ℕ)
    (A : Matrix (Word D k) (Word D k) ℂ) (hA : A ∈ permutationSpan D k)
    (hF : permutationFrame D k A = 0) : A = 0 := by
  have hsum : ∑ σ : Equiv.Perm (Fin k),
      Complex.normSq ((copyPermutationMatrix D k σ)ᴴ*A).trace = 0 := by
    rw [← permutationFrame_pairing_nonneg_sum,hF,Matrix.mul_zero,Matrix.trace_zero,Complex.zero_re]
  have ht (σ : Equiv.Perm (Fin k)) : ((copyPermutationMatrix D k σ)ᴴ*A).trace = 0 := by
    apply Complex.normSq_eq_zero.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp hsum
      σ (Finset.mem_univ σ)
  apply permutationSpan_pairing_ext D k A 0 hA (Submodule.zero_mem _)
  intro σ
  simpa only [copyPermutationMatrix_star,inv_inv,Matrix.mul_zero,Matrix.trace_zero]
    using ht σ⁻¹

def permutationFrameOnSpan (D k : ℕ) : permutationSpan D k →ₗ[ℂ] permutationSpan D k where
  toFun A := ⟨permutationFrame D k A,permutationFrame_mem D k A⟩
  map_add' A B := Subtype.ext (map_add _ _ _)
  map_smul' a A := Subtype.ext (map_smul _ _ _)

theorem permutationFrameOnSpan_injective (D k : ℕ) :
    Function.Injective (permutationFrameOnSpan D k) := by
  intro A B hAB
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply permutationFrame_eq_zero_of_mem D k _ (Submodule.sub_mem _ A.property B.property)
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hAB)

/-- Although the full permutation Gram matrix can be singular, this actual
 tensor-space cycle operator is always invertible. Faithfulness of the frame
 and finite-dimensional surjectivity prove the inverse internally. -/
theorem cycleOperator_self_det_ne_zero (D k : ℕ) :
    (cycleOperator D D k).det ≠ 0 := by
  have hs := LinearMap.surjective_of_injective (permutationFrameOnSpan_injective D k)
  obtain ⟨A,hA⟩ := hs ⟨1,permutationSpan_one D k⟩
  have he : permutationFrame D k A = 1 := congrArg Subtype.val hA
  rw [permutationFrame_eq_mul_cycleOperator D k A A.property] at he
  exact Matrix.det_ne_zero_of_left_inverse he

end
end ExtractionSchur
