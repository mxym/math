import SchurCompletion.FiniteBicommutant

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum

noncomputable section

theorem copyPermutationMatrix_one (D k : ℕ) :
    copyPermutationMatrix D k (1 : Equiv.Perm (Fin k)) = 1 := by
  have he : positionWordEquiv D k (1 : Equiv.Perm (Fin k)) = 1 := by ext w i; rfl
  simp only [copyPermutationMatrix, he, Matrix.permMatrix_one]

theorem copyPermutationMatrix_mul (D k : ℕ) (σ τ : Equiv.Perm (Fin k)) :
    copyPermutationMatrix D k σ * copyPermutationMatrix D k τ =
      copyPermutationMatrix D k (σ*τ) := by
  unfold copyPermutationMatrix
  rw [← Matrix.permMatrix_mul]
  congr 1

theorem copyPermutationMatrix_star (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (copyPermutationMatrix D k σ)ᴴ = copyPermutationMatrix D k σ⁻¹ := by
  unfold copyPermutationMatrix
  rw [Matrix.conjTranspose_permMatrix]
  congr 1

def permutationSpan (D k : ℕ) : Submodule ℂ (Matrix (Word D k) (Word D k) ℂ) :=
  Submodule.span ℂ (Set.range (copyPermutationMatrix D k))

theorem permutationSpan_one (D k : ℕ) : (1 : Matrix (Word D k) (Word D k) ℂ) ∈
    permutationSpan D k := Submodule.subset_span ⟨1,copyPermutationMatrix_one D k⟩

theorem permutationSpan_mul_mem (D k : ℕ)
    {A B : Matrix (Word D k) (Word D k) ℂ}
    (hA : A ∈ permutationSpan D k) (hB : B ∈ permutationSpan D k) :
    A*B ∈ permutationSpan D k := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨σ,rfl⟩ := hA
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨τ,rfl⟩ := hB
      exact Submodule.subset_span ⟨σ*τ,(copyPermutationMatrix_mul D k σ τ).symm⟩
    | zero => simpa only [Matrix.mul_zero] using (Submodule.zero_mem (permutationSpan D k))
    | add B C hB hC ihB ihC => simpa only [Matrix.mul_add] using Submodule.add_mem _ ihB ihC
    | smul c B hB ihB => simpa only [Matrix.mul_smul] using Submodule.smul_mem _ c ihB
  | zero => simpa only [Matrix.zero_mul] using (Submodule.zero_mem (permutationSpan D k))
  | add A C hA hC ihA ihC => simpa only [Matrix.add_mul] using Submodule.add_mem _ ihA ihC
  | smul c A hA ihA => simpa only [Matrix.smul_mul] using Submodule.smul_mem _ c ihA

theorem permutationSpan_star_mem (D k : ℕ)
    {A : Matrix (Word D k) (Word D k) ℂ} (hA : A ∈ permutationSpan D k) :
    Aᴴ ∈ permutationSpan D k := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨σ,rfl⟩ := hA
    exact Submodule.subset_span ⟨σ⁻¹,(copyPermutationMatrix_star D k σ).symm⟩
  | zero => simpa only [Matrix.conjTranspose_zero] using (Submodule.zero_mem (permutationSpan D k))
  | add A B hA hB ihA ihB => simpa only [Matrix.conjTranspose_add] using Submodule.add_mem _ ihA ihB
  | smul c A hA ihA => simpa only [Matrix.conjTranspose_smul] using Submodule.smul_mem _ (star c) ihA

theorem commutes_of_mem_matrix_span {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (S : Set (Matrix ι ι ℂ))
    (hS : ∀ N ∈ S, M*N=N*M) {N : Matrix ι ι ℂ} (hN : N ∈ Submodule.span ℂ S) : M*N=N*M := by
  induction hN using Submodule.span_induction with
  | mem N hN => exact hS N hN
  | zero => simp
  | add A B hA hB ihA ihB => simp only [Matrix.mul_add, Matrix.add_mul, ihA, ihB]
  | smul c A hA ihA => simp only [Matrix.mul_smul, Matrix.smul_mul, ihA]

/-- Actual unitary/permutation Schur--Weyl mutual centralizer statement on
the original D^k coordinates. It does not yet classify irreducibles by shapes. -/
theorem mem_permutationSpan_iff_commutes_unitaryTensor (D k : ℕ)
    (M : Matrix (Word D k) (Word D k) ℂ) :
    M ∈ permutationSpan D k ↔ ∀ U : OneCopyUnitary D,
      M*tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k =
        tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k * M := by
  constructor
  · intro hM U
    exact (commutes_of_mem_matrix_span (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)
      (Set.range (copyPermutationMatrix D k))
      (by rintro _ ⟨σ,rfl⟩; exact (tensorMatrix_commutes_copyPermutation D k _ σ).symm) hM).symm
  · intro hM
    apply mem_matrix_bicommutant (permutationSpan D k) (permutationSpan_one D k)
      (fun B hB C hC => permutationSpan_mul_mem D k hB hC)
      (fun B hB => permutationSpan_star_mem D k hB) M
    intro T hT
    have ht : T ∈ tensorPowerSpan D k := by
      apply (mem_tensorPowerSpan_iff_commutes D k T).mpr
      intro σ
      exact (hT _ (Submodule.subset_span ⟨σ,rfl⟩)).symm
    rw [← unitaryTensorSpan_eq_tensorPowerSpan] at ht
    exact commutes_of_mem_matrix_span M _ (by rintro _ ⟨U,rfl⟩; exact hM U) ht

theorem haarOrbitAverage_mem_permutationSpan (D k : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) : haarOrbitAverage D k X ∈ permutationSpan D k := by
  apply (mem_permutationSpan_iff_commutes_unitaryTensor D k _).mpr
  intro U
  exact (haarOrbitAverage_commutes D k X U).symm

theorem haarOrbitAverage_central (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (A : Matrix (Word D k) (Word D k) ℂ) (hA : A ∈ tensorPowerSpan D k) :
    haarOrbitAverage D k X * A = A * haarOrbitAverage D k X := by
  rw [← unitaryTensorSpan_eq_tensorPowerSpan] at hA
  exact commutes_of_mem_matrix_span _ _
    (by rintro _ ⟨U,rfl⟩; exact (haarOrbitAverage_commutes D k X U).symm) hA

end
end ExtractionSchur
