import SchurCompletion.CycleInsertion

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

def extendPositionPerm (k : ℕ) (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k+1)) :=
  Equiv.Perm.decomposeFin.symm (0,σ)

theorem decomposeFin_swap_extend (k : ℕ) (p : Fin (k+1)) (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm.decomposeFin.symm (p,σ) = Equiv.swap 0 p * extendPositionPerm k σ := by
  ext j
  induction j using Fin.cases with
  | zero => simp only [Equiv.Perm.decomposeFin_symm_apply_zero,Equiv.Perm.mul_apply,
      extendPositionPerm,Equiv.swap_apply_left]
  | succ j =>
    simp only [Equiv.Perm.decomposeFin_symm_apply_succ,Equiv.Perm.mul_apply,
      extendPositionPerm,Equiv.swap_self,Equiv.refl_apply]

/-- Identity on the first letter and the given actual matrix on the remaining
 tensor positions, expressed directly on the original computational words. -/
def prependMatrix (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    Matrix (Word D (k+1)) (Word D (k+1)) ℂ :=
  fun w v => if w 0 = v 0 then A (fun j => w j.succ) (fun j => v j.succ) else 0

theorem position_comp_extend_eq_iff (D k : ℕ) (σ : Equiv.Perm (Fin k))
    (w v : Word D (k+1)) :
    w ∘ extendPositionPerm k σ = v ↔ w 0 = v 0 ∧
      (fun j => w (σ j).succ) = (fun j => v j.succ) := by
  constructor
  · intro h
    constructor
    · simpa only [extendPositionPerm,Function.comp_apply,
        Equiv.Perm.decomposeFin_symm_apply_zero] using congrFun h 0
    · apply funext
      intro j
      simpa only [extendPositionPerm,Function.comp_apply,
        Equiv.Perm.decomposeFin_symm_apply_succ,Equiv.swap_self,Equiv.refl_apply]
          using congrFun h j.succ
  · rintro ⟨h0,hs⟩
    apply funext
    intro j
    induction j using Fin.cases with
    | zero => simpa only [extendPositionPerm,Function.comp_apply,
        Equiv.Perm.decomposeFin_symm_apply_zero] using h0
    | succ j => simpa only [extendPositionPerm,Function.comp_apply,
        Equiv.Perm.decomposeFin_symm_apply_succ,Equiv.swap_self,Equiv.refl_apply]
          using congrFun hs j

theorem copyPermutation_extend (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    copyPermutationMatrix D (k+1) (extendPositionPerm k σ) =
      prependMatrix D k (copyPermutationMatrix D k σ) := by
  ext w v
  simp only [copyPermutationMatrix_apply,prependMatrix,position_comp_extend_eq_iff]
  change (if w 0 = v 0 ∧ (fun j => w (σ j).succ) = (fun j => v j.succ) then (1 : ℂ) else 0) = _
  split_ifs <;> simp_all [Function.comp_def]

def extendedCycleOperator (D t k : ℕ) :
    Matrix (Word D (k+1)) (Word D (k+1)) ℂ :=
  ∑ σ : Equiv.Perm (Fin k), (t : ℂ)^positionCycleCount k σ •
    copyPermutationMatrix D (k+1) (extendPositionPerm k σ)

theorem extendedCycleOperator_eq_prepend (D t k : ℕ) :
    extendedCycleOperator D t k = prependMatrix D k (cycleOperator D t k) := by
  rw [cycleOperator_eq_direct_sum]
  ext w v
  simp only [extendedCycleOperator,copyPermutation_extend,Matrix.sum_apply,Matrix.smul_apply,
    prependMatrix,smul_eq_mul]
  split_ifs <;> simp

/-- The next genuine Jucys--Murphy operator: transpositions of the new first
 tensor position with each of the remaining positions. -/
def firstJucysMurphy (D k : ℕ) : Matrix (Word D (k+1)) (Word D (k+1)) ℂ :=
  ∑ i : Fin k, copyPermutationMatrix D (k+1) (Equiv.swap 0 i.succ)

/-- Exact tensor-coordinate Jucys--Murphy recursion for every cycle-character
 operator. This is derived by genuine finite permutation insertion. -/
theorem cycleOperator_jucys_recursion (D t k : ℕ) :
    cycleOperator D t (k+1) =
      ((t : ℂ) • (1 : Matrix (Word D (k+1)) (Word D (k+1)) ℂ) + firstJucysMurphy D k) *
        prependMatrix D k (cycleOperator D t k) := by
  rw [← extendedCycleOperator_eq_prepend,cycleOperator_eq_direct_sum]
  calc
    _ = ∑ p : Fin (k+1), ∑ σ : Equiv.Perm (Fin k),
        (t : ℂ)^positionCycleCount (k+1) (Equiv.Perm.decomposeFin.symm (p,σ)) •
          copyPermutationMatrix D (k+1) (Equiv.Perm.decomposeFin.symm (p,σ)) := by
      have h := Equiv.sum_comp (Equiv.Perm.decomposeFin.symm)
        (fun σ => (t : ℂ)^positionCycleCount (k+1) σ • copyPermutationMatrix D (k+1) σ)
      simpa only [Fintype.sum_prod_type] using h.symm
    _ = _ := by
      rw [Fin.sum_univ_succ]
      simp_rw [cycleCharacter_insert_zero,cycleCharacter_insert_succ]
      rw [Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul]
      have h0 (σ : Equiv.Perm (Fin k)) :
          Equiv.Perm.decomposeFin.symm (0,σ) = extendPositionPerm k σ := rfl
      simp only [h0,decomposeFin_swap_extend,copyPermutationMatrix_mul,extendedCycleOperator,
        firstJucysMurphy,Matrix.sum_mul,Matrix.mul_sum,Matrix.mul_smul,mul_smul,Finset.smul_sum]
      congr 1
      exact Finset.sum_comm

end
end ExtractionSchur
