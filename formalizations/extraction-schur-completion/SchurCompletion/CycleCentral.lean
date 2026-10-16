import SchurCompletion.CyclePositive
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem cycleCharacter_conjugate (t k : ℕ) (σ τ : Equiv.Perm (Fin k)) :
    (t : ℂ)^positionCycleCount k (τ⁻¹*σ*τ) = (t : ℂ)^positionCycleCount k σ := by
  rw [← copyPermutation_trace_cycleCount,← copyPermutationMatrix_mul,← copyPermutationMatrix_mul,
    Matrix.trace_mul_cycle]
  simp only [copyPermutationMatrix_mul,mul_inv_cancel,one_mul,copyPermutation_trace_cycleCount]

theorem cycleOperator_mem_permutationSpan (D t k : ℕ) :
    cycleOperator D t k ∈ permutationSpan D k := by
  apply Submodule.sum_mem
  intro σ _
  exact Submodule.smul_mem (permutationSpan D k) _ (Submodule.subset_span ⟨σ⁻¹,rfl⟩)

theorem copyPermutation_mul_cycleOperator (D t k : ℕ) (τ : Equiv.Perm (Fin k)) :
    copyPermutationMatrix D k τ * cycleOperator D t k =
      cycleOperator D t k * copyPermutationMatrix D k τ := by
  calc
    _ = ∑ σ : Equiv.Perm (Fin k), (t : ℂ)^positionCycleCount k σ •
        copyPermutationMatrix D k (τ*σ⁻¹) := by
      simp only [cycleOperator,Matrix.mul_sum,Matrix.mul_smul,copyPermutationMatrix_mul]
    _ = ∑ η : Equiv.Perm (Fin k), (t : ℂ)^positionCycleCount k (τ⁻¹*η*τ) •
        copyPermutationMatrix D k (τ*(τ⁻¹*η*τ)⁻¹) := by
      exact (Equiv.sum_comp ((Equiv.mulLeft τ⁻¹).trans (Equiv.mulRight τ)) _).symm
    _ = _ := by
      have hg (η : Equiv.Perm (Fin k)) : τ*(τ⁻¹*η*τ)⁻¹ = η⁻¹*τ := by group
      simp only [cycleCharacter_conjugate,hg,cycleOperator,Matrix.sum_mul,Matrix.smul_mul,
        copyPermutationMatrix_mul]

/-- Every actual cycle-character matrix is central in the genuine permutation
 algebra and belongs to the genuine tensor-power centralizer. -/
theorem cycleOperator_central (D t k : ℕ)
    (A : Matrix (Word D k) (Word D k) ℂ) (hA : A ∈ permutationSpan D k) :
    cycleOperator D t k * A = A * cycleOperator D t k := by
  apply commutes_of_mem_matrix_span _ _ _ hA
  rintro _ ⟨σ,rfl⟩
  exact (copyPermutation_mul_cycleOperator D t k σ).symm

theorem cycleOperator_mem_tensorPowerSpan (D t k : ℕ) :
    cycleOperator D t k ∈ tensorPowerSpan D k := by
  apply (mem_tensorPowerSpan_iff_commutes D k _).mpr
  intro σ
  exact copyPermutation_mul_cycleOperator D t k σ

theorem cycleOperator_commute (D t u k : ℕ) :
    Commute (cycleOperator D t k) (cycleOperator D u k) :=
  cycleOperator_central D t k _ (cycleOperator_mem_permutationSpan D u k)

/-- A genuine joint spectral decomposition of all cycle-character operators
 on the original complex tensor space. Classification by Young contents is a
 further theorem; neither eigenvalues nor block dimensions are supplied here. -/
theorem cycleOperators_joint_eigenspaces_span (D k : ℕ) :
    (⨆ χ : ℕ → ℂ, ⨅ t : ℕ,
      Module.End.eigenspace ((cycleOperator D t k).toEuclideanLin) (χ t)) = ⊤ := by
  apply LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute
  · intro t
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (cycleOperator_posSemidef D t k).isHermitian
  · intro t u _
    change Matrix.toEuclideanLin (cycleOperator D t k) *
        Matrix.toEuclideanLin (cycleOperator D u k) =
      Matrix.toEuclideanLin (cycleOperator D u k) * Matrix.toEuclideanLin (cycleOperator D t k)
    change (Matrix.toEuclideanLin (cycleOperator D t k)).comp
        (Matrix.toEuclideanLin (cycleOperator D u k)) =
      (Matrix.toEuclideanLin (cycleOperator D u k)).comp
        (Matrix.toEuclideanLin (cycleOperator D t k))
    simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal,← Matrix.toLin_mul]
    exact congrArg (fun A => Matrix.toLin (EuclideanSpace.basisFun (Word D k) ℂ).toBasis
      (EuclideanSpace.basisFun (Word D k) ℂ).toBasis A) (cycleOperator_commute D t u k)

end
end ExtractionSchur
