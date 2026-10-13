import HydrologyTree.RootModalData
import Mathlib.LinearAlgebra.Vandermonde

/-! Actual Kalman matrices, not assumed rank interfaces. Their factorization
is proved from the same physical modal coordinate witness used for the ODE. -/
open Matrix
noncomputable section
namespace HydrologyTree

variable {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}

def rootKrylovMatrix (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.of fun i j => (A^j.val *ᵥ(Pi.single 0 1)) i

def rootObservationMatrix (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ := Matrix.of fun i j => (A^i.val) 0 j

lemma rootModal_synthesis_row (M : RootModalData A) (i : Fin (n+1)) :
    M.synthesis 0 i=M.amplitudes i := by
  simpa [Pi.single_apply] using M.root_output (Pi.single i 1)

/-- Every actual matrix power, with no simple-spectrum hypothesis. -/
theorem rootModal_matrix_power (M : RootModalData A) (k : ℕ) :
    A^k=M.synthesis*Matrix.diagonal (fun i => (-M.rates i)^k)*M.analysis := by
  induction k with
  | zero => simpa using M.synth_analysis.symm
  | succ k ih =>
    rw [pow_succ',ih]
    calc
      _ = (A*M.synthesis)*Matrix.diagonal (fun i => (-M.rates i)^k)*M.analysis := by simp only [Matrix.mul_assoc]
      _ = M.synthesis*(Matrix.diagonal (fun i => -M.rates i)*
          Matrix.diagonal (fun i => (-M.rates i)^k))*M.analysis := by
            rw [M.intertwine]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.diagonal_mul_diagonal]; simp only [pow_succ']

lemma rootModal_krylov_column (M : RootModalData A) (k : ℕ) :
    A^k *ᵥ(Pi.single 0 1)=M.synthesis*ᵥ(fun i => M.amplitudes i*(-M.rates i)^k) := by
  rw [rootModal_matrix_power M k,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,M.input_analysis]
  congr 1
  ext i
  simp [Matrix.mulVec,dotProduct,Matrix.diagonal_apply,mul_comm]

/-- Actual controllability matrix factorization. -/
theorem rootKrylovMatrix_factorization (M : RootModalData A) :
    rootKrylovMatrix A=M.synthesis*Matrix.diagonal M.amplitudes*
      Matrix.vandermonde (fun i => -M.rates i) := by
  ext i j
  change (A^j.val *ᵥPi.single 0 1) i = _
  rw [rootModal_krylov_column M j.val,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.mulVec,dotProduct,Matrix.vandermonde_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Actual observability matrix factorization, in the original state coordinates. -/
theorem rootObservationMatrix_factorization (M : RootModalData A) :
    rootObservationMatrix A=(Matrix.vandermonde (fun i => -M.rates i))ᵀ*
      Matrix.diagonal M.amplitudes*M.analysis := by
  ext i j
  change (A^i.val) 0 j = _
  rw [rootModal_matrix_power M i.val,Matrix.mul_apply,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,Matrix.vandermonde_apply,rootModal_synthesis_row M]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The actual Kalman determinants are nonzero when all full modes are present. -/
theorem rootModal_kalman_nonsingular (M : RootModalData A)
    (hr : Function.Injective M.rates) (hk : ∀ i, M.amplitudes i ≠ 0) :
    (rootKrylovMatrix A).det ≠ 0 ∧ (rootObservationMatrix A).det ≠ 0 := by
  have hST := congrArg Matrix.det M.synth_analysis
  rw [Matrix.det_mul,Matrix.det_one] at hST
  have hS : M.synthesis.det ≠ 0 := left_ne_zero_of_mul (hST ▸ one_ne_zero)
  have hT : M.analysis.det ≠ 0 := right_ne_zero_of_mul (hST ▸ one_ne_zero)
  have hv : (Matrix.vandermonde (fun i => -M.rates i)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr (neg_injective.comp hr)
  have hkdet : (Matrix.diagonal M.amplitudes).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hk i)
  rw [rootKrylovMatrix_factorization M,rootObservationMatrix_factorization M,
    Matrix.det_mul,Matrix.det_mul,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  exact ⟨mul_ne_zero (mul_ne_zero hS hkdet) hv,mul_ne_zero (mul_ne_zero hv hkdet) hT⟩

end HydrologyTree
