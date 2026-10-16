import SchurCompletion.JucysRecursion

open scoped BigOperators ComplexOrder Kronecker
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

def wordHeadTailEquiv (D k : ℕ) : Word D (k+1) ≃ Fin D × Word D k where
  toFun w := (w 0,fun j => w j.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv w := by apply funext; intro j; induction j using Fin.cases <;> rfl
  right_inv _ := rfl

theorem prependMatrix_eq_kronecker (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    prependMatrix D k A = ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ A).submatrix
      (wordHeadTailEquiv D k) (wordHeadTailEquiv D k) := by
  ext w v
  simp only [prependMatrix,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,
    wordHeadTailEquiv,Matrix.one_apply,ite_mul,one_mul,zero_mul]
  rfl

theorem prependMatrix_mul (D k : ℕ) (A B : Matrix (Word D k) (Word D k) ℂ) :
    prependMatrix D k (A*B) = prependMatrix D k A * prependMatrix D k B := by
  simp only [prependMatrix_eq_kronecker,Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul]

theorem prependMatrix_one (D k : ℕ) :
    prependMatrix D k (1 : Matrix (Word D k) (Word D k) ℂ) = 1 := by
  rw [prependMatrix_eq_kronecker,Matrix.one_kronecker_one,Matrix.submatrix_one_equiv]

def prependMatrixRingHom (D k : ℕ) :
    Matrix (Word D k) (Word D k) ℂ →+* Matrix (Word D (k+1)) (Word D (k+1)) ℂ where
  toFun := prependMatrix D k
  map_zero' := by ext w v; simp [prependMatrix]
  map_one' := prependMatrix_one D k
  map_add' A B := by
    ext w v
    by_cases h : w 0 = v 0 <;> simp [prependMatrix,h]
  map_mul' := prependMatrix_mul D k

theorem prependMatrix_smul (D k : ℕ) (c : ℂ) (A : Matrix (Word D k) (Word D k) ℂ) :
    prependMatrix D k (c • A) = c • prependMatrix D k A := by
  ext w v
  simp only [prependMatrix,Matrix.smul_apply,smul_eq_mul]
  split_ifs <;> simp

def jucysOperators (D : ℕ) : (k : ℕ) → Fin k → Matrix (Word D k) (Word D k) ℂ
  | 0 => fun j => j.elim0
  | k+1 => Fin.cases (firstJucysMurphy D k) (fun j => prependMatrix D k (jucysOperators D k j))

theorem cycleOperator_zero (D t : ℕ) : cycleOperator D t 0 = 1 := by
  have hc (σ : Equiv.Perm (Fin 0)) : positionCycleCount 0 σ = 0 := Fintype.card_eq_zero
  simp only [cycleOperator,hc,pow_zero,one_smul,Fintype.sum_unique]
  have he : (default : Equiv.Perm (Fin 0)) = 1 := Subsingleton.elim _ _
  rw [he,inv_one,copyPermutationMatrix_one]

/-- Actual finite noncommutative content-polynomial factorization. No tableau
 labels or integer eigenvalues are assumed in this construction. -/
theorem cycleOperator_jucys_factorization (D t k : ℕ) :
    cycleOperator D t k =
      (List.ofFn (fun j : Fin k => (t : ℂ) • (1 : Matrix (Word D k) (Word D k) ℂ) +
        jucysOperators D k j)).prod := by
  induction k with
  | zero => simpa only [List.ofFn_zero,List.prod_nil] using cycleOperator_zero D t
  | succ k ih =>
    rw [cycleOperator_jucys_recursion,ih,List.ofFn_succ,List.prod_cons]
    congr 1
    have h := map_list_prod (prependMatrixRingHom D k)
      (List.ofFn (fun j : Fin k => (t : ℂ) • (1 : Matrix (Word D k) (Word D k) ℂ) +
        jucysOperators D k j))
    rw [List.map_ofFn] at h
    symm
    convert h.symm using 1
    congr 1
    apply congrArg List.ofFn
    apply funext
    intro j
    change (t : ℂ) • (1 : Matrix (Word D (k+1)) (Word D (k+1)) ℂ) +
      prependMatrix D k (jucysOperators D k j) =
        prependMatrix D k ((t : ℂ) • (1 : Matrix (Word D k) (Word D k) ℂ) + jucysOperators D k j)
    have ha := (prependMatrixRingHom D k).map_add
      ((t : ℂ) • (1 : Matrix (Word D k) (Word D k) ℂ)) (jucysOperators D k j)
    change prependMatrix D k (_+_) = _ at ha
    rw [ha]
    change (t : ℂ) • (1 : Matrix (Word D (k+1)) (Word D (k+1)) ℂ) +
      prependMatrix D k (jucysOperators D k j) =
        prependMatrix D k ((t : ℂ) • (1 : Matrix (Word D k) (Word D k) ℂ)) +
          prependMatrix D k (jucysOperators D k j)
    rw [prependMatrix_smul,prependMatrix_one]
    rfl

end
end ExtractionSchur
