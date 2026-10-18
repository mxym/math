import SchurCompletion.JucysFactorization

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem prependMatrix_add (D k : ℕ) (A B : Matrix (Word D k) (Word D k) ℂ) :
    prependMatrix D k (A+B) = prependMatrix D k A + prependMatrix D k B :=
  (prependMatrixRingHom D k).map_add A B

theorem prependMatrix_conjTranspose (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    (prependMatrix D k A)ᴴ = prependMatrix D k Aᴴ := by
  ext w v
  by_cases h : w 0 = v 0 <;>
    simp [prependMatrix,Matrix.conjTranspose_apply,h,eq_comm]

def extendedPermutationSpan (D k : ℕ) :
    Submodule ℂ (Matrix (Word D (k+1)) (Word D (k+1)) ℂ) :=
  Submodule.span ℂ (Set.range (fun σ => copyPermutationMatrix D (k+1) (extendPositionPerm k σ)))

theorem prependMatrix_mem_extendedSpan (D k : ℕ)
    (A : Matrix (Word D k) (Word D k) ℂ) (hA : A ∈ permutationSpan D k) :
    prependMatrix D k A ∈ extendedPermutationSpan D k := by
  change A ∈ Submodule.span ℂ (Set.range (copyPermutationMatrix D k)) at hA
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ,rfl⟩ := hx
    rw [← copyPermutation_extend]
    exact Submodule.subset_span ⟨σ,rfl⟩
  | zero =>
    change (prependMatrixRingHom D k) 0 ∈ _
    rw [map_zero]
    exact Submodule.zero_mem _
  | add A B hA hB iA iB => rw [prependMatrix_add]; exact Submodule.add_mem _ iA iB
  | smul c A hA iA => rw [prependMatrix_smul]; exact Submodule.smul_mem _ _ iA

theorem extendedPermutationSpan_le (D k : ℕ) :
    extendedPermutationSpan D k ≤ permutationSpan D (k+1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨σ,rfl⟩
  exact Submodule.subset_span ⟨extendPositionPerm k σ,rfl⟩

theorem firstJucysMurphy_hermitian (D k : ℕ) :
    (firstJucysMurphy D k).IsHermitian := by
  change (firstJucysMurphy D k)ᴴ = firstJucysMurphy D k
  simp only [firstJucysMurphy,Matrix.conjTranspose_sum,copyPermutationMatrix_star,Equiv.swap_inv]

theorem firstJucysMurphy_mem (D k : ℕ) : firstJucysMurphy D k ∈ permutationSpan D (k+1) := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.subset_span ⟨Equiv.swap 0 i.succ,rfl⟩

theorem extendedPermutation_mul_firstJucysMurphy (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    copyPermutationMatrix D (k+1) (extendPositionPerm k σ) * firstJucysMurphy D k =
      firstJucysMurphy D k * copyPermutationMatrix D (k+1) (extendPositionPerm k σ) := by
  have hg (i : Fin k) : extendPositionPerm k σ * Equiv.swap 0 i.succ =
      Equiv.swap 0 (σ i).succ * extendPositionPerm k σ := by
    rw [Equiv.mul_swap_eq_swap_mul]
    simp only [extendPositionPerm,Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.decomposeFin_symm_apply_succ,Equiv.swap_self,Equiv.refl_apply]
  calc
    _ = ∑ i : Fin k, copyPermutationMatrix D (k+1) (Equiv.swap 0 (σ i).succ) *
        copyPermutationMatrix D (k+1) (extendPositionPerm k σ) := by
      simp only [firstJucysMurphy,Matrix.mul_sum,copyPermutationMatrix_mul,hg]
    _ = ∑ i : Fin k, copyPermutationMatrix D (k+1) (Equiv.swap 0 i.succ) *
        copyPermutationMatrix D (k+1) (extendPositionPerm k σ) :=
      Equiv.sum_comp σ (fun i : Fin k => copyPermutationMatrix D (k+1) (Equiv.swap 0 i.succ) *
        copyPermutationMatrix D (k+1) (extendPositionPerm k σ))
    _ = _ := by simp only [firstJucysMurphy,Matrix.sum_mul]

theorem firstJucysMurphy_commutes_prepend (D k : ℕ)
    (A : Matrix (Word D k) (Word D k) ℂ) (hA : A ∈ permutationSpan D k) :
    firstJucysMurphy D k * prependMatrix D k A = prependMatrix D k A * firstJucysMurphy D k := by
  apply commutes_of_mem_matrix_span _ _ _ (prependMatrix_mem_extendedSpan D k A hA)
  rintro _ ⟨σ,rfl⟩
  exact (extendedPermutation_mul_firstJucysMurphy D k σ).symm

theorem jucysOperators_mem (D k : ℕ) :
    ∀ j : Fin k, jucysOperators D k j ∈ permutationSpan D k := by
  induction k with
  | zero => intro j; exact j.elim0
  | succ k ih =>
    intro j
    induction j using Fin.cases with
    | zero => exact firstJucysMurphy_mem D k
    | succ j => exact extendedPermutationSpan_le D k (prependMatrix_mem_extendedSpan D k _ (ih j))

theorem jucysOperators_hermitian (D k : ℕ) :
    ∀ j : Fin k, (jucysOperators D k j).IsHermitian := by
  induction k with
  | zero => intro j; exact j.elim0
  | succ k ih =>
    intro j
    induction j using Fin.cases with
    | zero => exact firstJucysMurphy_hermitian D k
    | succ j =>
      change (prependMatrix D k (jucysOperators D k j))ᴴ = _
      rw [prependMatrix_conjTranspose,(ih j).eq]
      rfl

/-- The genuine tensor-space Jucys--Murphy family consists of commuting
 Hermitian matrices. No tableau representation is a hypothesis. -/
theorem jucysOperators_commute (D k : ℕ) :
    ∀ i j : Fin k, Commute (jucysOperators D k i) (jucysOperators D k j) := by
  induction k with
  | zero => intro i; exact i.elim0
  | succ k ih =>
    intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact Commute.refl _
      | succ j => exact firstJucysMurphy_commutes_prepend D k _ (jucysOperators_mem D k j)
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (firstJucysMurphy_commutes_prepend D k _ (jucysOperators_mem D k i)).symm
      | succ j =>
        change prependMatrix D k (jucysOperators D k i) * prependMatrix D k (jucysOperators D k j) =
          prependMatrix D k (jucysOperators D k j) * prependMatrix D k (jucysOperators D k i)
        rw [← prependMatrix_mul,← prependMatrix_mul]
        exact congrArg (prependMatrix D k) (ih i j)

theorem jucysOperators_joint_eigenspaces_span (D k : ℕ) :
    (⨆ c : Fin k → ℂ, ⨅ j : Fin k,
      Module.End.eigenspace ((jucysOperators D k j).toEuclideanLin) (c j)) = ⊤ := by
  apply LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute
  · intro j
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (jucysOperators_hermitian D k j)
  · intro i j _
    change (Matrix.toEuclideanLin (jucysOperators D k i)).comp
        (Matrix.toEuclideanLin (jucysOperators D k j)) =
      (Matrix.toEuclideanLin (jucysOperators D k j)).comp
        (Matrix.toEuclideanLin (jucysOperators D k i))
    simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal,← Matrix.toLin_mul]
    exact congrArg (fun A => Matrix.toLin (EuclideanSpace.basisFun (Word D k) ℂ).toBasis
      (EuclideanSpace.basisFun (Word D k) ℂ).toBasis A) (jucysOperators_commute D k i j)

end
end ExtractionSchur
