import MatrixBridge
open scoped ComplexConjugate

namespace ComplexPencilFull
open ComplexPencilMain
open ComplexPencilLink

noncomputable section

def matRowSq (A : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) : ℝ :=
  ∑ j : Fin 3, Complex.normSq (A i j)

theorem normSq_eq_sq (z : ℂ) :
    Complex.normSq z=ComplexPencilLink.sq z := by
  simp [Complex.normSq_apply,ComplexPencilLink.sq,pow_two]

theorem matRowSq_rows0 (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    matRowSq (rowsMatrix a0 a1 a2 b0 b1 b2 c0 c1 c2) 0 =
       rowSq a0 a1 a2 := by
  simp [matRowSq,rowsMatrix,Fin.sum_univ_succ,
        normSq_eq_sq,rowSq] <;> ring

theorem matRowSq_rows1 (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    matRowSq (rowsMatrix a0 a1 a2 b0 b1 b2 c0 c1 c2) 1 =
       rowSq b0 b1 b2 := by
  simp [matRowSq,rowsMatrix,Fin.sum_univ_succ,
        normSq_eq_sq,rowSq] <;> ring

theorem matRowSq_rows2 (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    matRowSq (rowsMatrix a0 a1 a2 b0 b1 b2 c0 c1 c2) 2 =
       rowSq c0 c1 c2 := by
  simp [matRowSq,rowsMatrix,Fin.sum_univ_succ,
        normSq_eq_sq,rowSq] <;> ring

theorem rowsMatrix_surjective (A : Matrix (Fin 3) (Fin 3) ℂ) :
    rowsMatrix (A 0 0) (A 0 1) (A 0 2)
     (A 1 0) (A 1 1) (A 1 2)
     (A 2 0) (A 2 1) (A 2 2) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rowsMatrix]

def matrixSquaredIneq (lam : ℂ) (B : ℝ) : Prop :=
   ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
      Complex.normSq (A.permanent + lam*A.det) ≤
      B*(matRowSq A 0)*(matRowSq A 1)*(matRowSq A 2)

theorem matrix_squared_norm_iff (lam : ℂ) (B : ℝ) :
    matrixSquaredIneq lam B ↔ normBoundSq lam ≤ B := by
  constructor
  · intro h
    apply universalSquaredBound_le lam B
    intro a0 a1 a2 b0 b1 b2 c0 c1 c2
    have hs := h (rowsMatrix a0 a1 a2 b0 b1 b2 c0 c1 c2)
    simpa only [det_row_expansion,permanent_row_expansion,
       normSq_eq_sq,matRowSq_rows0,matRowSq_rows1,
       matRowSq_rows2] using hs
  · intro h A
    have hall := universalSquaredBound_of_ge lam B h
    have hr := hall (A 0 0) (A 0 1) (A 0 2)
                   (A 1 0) (A 1 1) (A 1 2)
                   (A 2 0) (A 2 1) (A 2 2)
    have he := rowsMatrix_surjective A
    rw [← he]
    simpa only [det_row_expansion,permanent_row_expansion,
       normSq_eq_sq,matRowSq_rows0,matRowSq_rows1,
       matRowSq_rows2] using hr

#print axioms ComplexPencilFull.matrix_squared_norm_iff

end
end ComplexPencilFull
