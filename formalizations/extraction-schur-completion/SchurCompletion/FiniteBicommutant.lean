import SchurCompletion.UnitaryTensorSpan
import Mathlib.LinearAlgebra.Matrix.Kronecker

open scoped BigOperators ComplexOrder Kronecker
open Matrix

namespace ExtractionSchur

open ExtractionRankSupport

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixVectorEquiv : Matrix ι ι ℂ ≃ₗ[ℂ] ((ι×ι) → ℂ) where
  toFun M x := M x.1 x.2
  invFun v i j := v (i,j)
  left_inv M := rfl
  right_inv v := by ext p; cases p; rfl
  map_add' M N := rfl
  map_smul' c M := rfl

def leftAmplification (A : Matrix ι ι ℂ) : Matrix (ι×ι) (ι×ι) ℂ := A ⊗ₖ 1

theorem leftAmplification_mulVec (A M : Matrix ι ι ℂ) :
    leftAmplification A *ᵥ matrixVectorEquiv M = matrixVectorEquiv (A*M) := by
  ext x
  rcases x with ⟨i,j⟩
  change (∑ x : ι×ι, (A i x.1 * (1 : Matrix ι ι ℂ) j x.2) * M x.1 x.2) = (A*M) i j
  rw [Fintype.sum_prod_type]
  simp [Matrix.one_apply, Matrix.mul_apply]

theorem leftAmplification_conjTranspose (A : Matrix ι ι ℂ) :
    (leftAmplification A)ᴴ = leftAmplification Aᴴ := by
  ext x y
  rcases x with ⟨i,p⟩
  rcases y with ⟨j,q⟩
  change star (A j i * (1 : Matrix ι ι ℂ) q p) = star (A j i) * (1 : Matrix ι ι ℂ) p q
  by_cases hpq : p = q <;> simp [Matrix.one_apply, hpq, eq_comm]

def matrixBlock (Q : Matrix (ι×ι) (ι×ι) ℂ) (p q : ι) : Matrix ι ι ℂ :=
  fun i j => Q (i,p) (j,q)

theorem amplification_mul_apply (A : Matrix ι ι ℂ) (Q : Matrix (ι×ι) (ι×ι) ℂ)
    (i j p q : ι) :
    (leftAmplification A * Q) (i,p) (j,q) = (A * matrixBlock Q p q) i j := by
  change (∑ x : ι×ι, (A i x.1 * (1 : Matrix ι ι ℂ) p x.2) * Q x (j,q)) =
    ∑ x, A i x * Q (x,p) (j,q)
  rw [Fintype.sum_prod_type]
  simp [Matrix.one_apply]

theorem mul_amplification_apply (A : Matrix ι ι ℂ) (Q : Matrix (ι×ι) (ι×ι) ℂ)
    (i j p q : ι) :
    (Q * leftAmplification A) (i,p) (j,q) = (matrixBlock Q p q * A) i j := by
  change (∑ x : ι×ι, Q (i,p) x * (A x.1 j * (1 : Matrix ι ι ℂ) x.2 q)) =
    ∑ x, Q (i,p) (x,q) * A x j
  rw [Fintype.sum_prod_type]
  simp [Matrix.one_apply]

theorem hermitian_projector_commutes_of_invariant
    {η : Type*} [Fintype η] [DecidableEq η]
    (Q T : Matrix η η ℂ) (hQ : Q.IsHermitian)
    (hFix : ∀ v ∈ LinearMap.range Q.mulVecLin, Q *ᵥ v = v)
    (hT : ∀ v ∈ LinearMap.range Q.mulVecLin, T *ᵥ v ∈ LinearMap.range Q.mulVecLin)
    (hTstar : ∀ v ∈ LinearMap.range Q.mulVecLin, Tᴴ *ᵥ v ∈ LinearMap.range Q.mulVecLin) :
    Q*T = T*Q := by
  have hcompress (A : Matrix η η ℂ)
      (hA : ∀ v ∈ LinearMap.range Q.mulVecLin, A *ᵥ v ∈ LinearMap.range Q.mulVecLin) :
      Q*A*Q = A*Q := by
    rw [Matrix.mul_assoc]
    apply matrix_mul_eq_of_fixes_columns
    intro w
    have hcol : (A*Q).col w = A *ᵥ Q.col w := rfl
    rw [hcol]
    apply hFix
    apply hA
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨w,rfl⟩
  have hstar := congrArg Matrix.conjTranspose (hcompress Tᴴ hTstar)
  have hr : Q*T*Q = Q*T := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQ.eq,
      ← Matrix.mul_assoc] using hstar
  exact hr.symm.trans (hcompress T hT)

/-- The finite-dimensional bicommutant theorem for an actual complex matrix
subspace closed under identity, multiplication and adjoint. The orthogonal
projection and the necessary amplification are constructed internally. -/
theorem mem_matrix_bicommutant (A : Submodule ℂ (Matrix ι ι ℂ))
    (hOne : (1 : Matrix ι ι ℂ) ∈ A)
    (hMul : ∀ B ∈ A, ∀ C ∈ A, B*C ∈ A)
    (hStar : ∀ B ∈ A, Bᴴ ∈ A)
    (M : Matrix ι ι ℂ)
    (hM : ∀ T : Matrix ι ι ℂ, (∀ B ∈ A, T*B=B*T) → M*T=T*M) : M ∈ A := by
  classical
  let S := A.map matrixVectorEquiv.toLinearMap
  obtain ⟨Q,hQ,hQQ,hQR,hRank,hFix⟩ := MatrixSubspace.exists_subspace_projection S
  have hinv (B : Matrix ι ι ℂ) (hB : B ∈ A) :
      ∀ v ∈ LinearMap.range Q.mulVecLin,
        leftAmplification B *ᵥ v ∈ LinearMap.range Q.mulVecLin := by
    intro v hv
    rw [hQR] at hv ⊢
    obtain ⟨C,hC,rfl⟩ := hv
    exact ⟨B*C,hMul B hB C hC,(leftAmplification_mulVec B C).symm⟩
  have hQB (B : Matrix ι ι ℂ) (hB : B ∈ A) :
      Q * leftAmplification B = leftAmplification B * Q := by
    apply hermitian_projector_commutes_of_invariant Q _ hQ
    · intro v hv
      exact hFix v (hQR ▸ hv)
    · exact hinv B hB
    · rw [leftAmplification_conjTranspose]
      exact hinv Bᴴ (hStar B hB)
  have hBlock (p q : ι) (B : Matrix ι ι ℂ) (hB : B ∈ A) :
      matrixBlock Q p q * B = B * matrixBlock Q p q := by
    ext i j
    have h := congrArg (fun N : Matrix (ι×ι) (ι×ι) ℂ => N (i,p) (j,q)) (hQB B hB)
    simpa only [amplification_mul_apply, mul_amplification_apply] using h
  have hMQ : leftAmplification M * Q = Q * leftAmplification M := by
    ext x y
    rcases x with ⟨i,p⟩
    rcases y with ⟨j,q⟩
    rw [amplification_mul_apply, mul_amplification_apply]
    exact congrArg (fun N : Matrix ι ι ℂ => N i j) (hM _ (hBlock p q))
  have hI : matrixVectorEquiv (1 : Matrix ι ι ℂ) ∈ S := ⟨1,hOne,rfl⟩
  have hQI := hFix _ hI
  have hQM : Q *ᵥ matrixVectorEquiv M = matrixVectorEquiv M := by
    have h := congrArg (fun N => N *ᵥ matrixVectorEquiv (1 : Matrix ι ι ℂ)) hMQ
    rw [← Matrix.mulVec_mulVec, hQI, leftAmplification_mulVec, Matrix.mul_one] at h
    rw [← Matrix.mulVec_mulVec, leftAmplification_mulVec, Matrix.mul_one] at h
    exact h.symm
  have hm : matrixVectorEquiv M ∈ S := by
    rw [← hQR]
    exact ⟨matrixVectorEquiv M,hQM⟩
  obtain ⟨N,hN,hNM⟩ := hm
  have heq : N = M := matrixVectorEquiv.injective hNM
  exact heq ▸ hN

end
end ExtractionSchur
