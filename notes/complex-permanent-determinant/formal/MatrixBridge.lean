import ExactNorm
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace ComplexPencilFull

def rowsMatrix (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![a0, a1, a2; b0,b1,b2; c0,c1,c2]

theorem det_row_expansion (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    (rowsMatrix a0 a1 a2 b0 b1 b2 c0 c1 c2).det =
       ComplexPencilMain.determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  simp [rowsMatrix, Matrix.det_fin_three,
    ComplexPencilMain.determinant3]
  ring

theorem permanent_row_expansion (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    (rowsMatrix a0 a1 a2 b0 b1 b2 c0 c1 c2).permanent =
       ComplexPencilMain.permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  classical
  let p01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let p02 : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  let p12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have hf : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, p01, p02, p12, p01 * p12, p12 * p01} := by
    decide
  unfold Matrix.permanent
  rw [hf]
  have h1 : (1 : Equiv.Perm (Fin 3)) ∉
      ({p01,p02,p12,p01*p12,p12*p01} : Finset _) := by decide
  have h2 : p01 ∉ ({p02,p12,p01*p12,p12*p01} : Finset _) := by decide
  have h3 : p02 ∉ ({p12,p01*p12,p12*p01} : Finset _) := by decide
  have h4 : p12 ∉ ({p01*p12,p12*p01} : Finset _) := by decide
  have h5 : p01*p12 ∉ ({p12*p01} : Finset _) := by decide
  rw [Finset.sum_insert h1, Finset.sum_insert h2,
      Finset.sum_insert h3, Finset.sum_insert h4,
      Finset.sum_insert h5, Finset.sum_singleton]
  have e010 : (Equiv.swap (0:Fin 3) 1) 0=1 := by decide
  have e011 : (Equiv.swap (0:Fin 3) 1) 1=0 := by decide
  have e012 : (Equiv.swap (0:Fin 3) 1) 2=2 := by decide
  have e020 : (Equiv.swap (0:Fin 3) 2) 0=2 := by decide
  have e021 : (Equiv.swap (0:Fin 3) 2) 1=1 := by decide
  have e022 : (Equiv.swap (0:Fin 3) 2) 2=0 := by decide
  have e120 : (Equiv.swap (1:Fin 3) 2) 0=0 := by decide
  have e121 : (Equiv.swap (1:Fin 3) 2) 1=2 := by decide
  have e122 : (Equiv.swap (1:Fin 3) 2) 2=1 := by decide
  simp [rowsMatrix,p01,p02,p12,Fin.prod_univ_succ,
    Equiv.Perm.mul_def,e010,e011,e012,e020,e021,e022,e120,e121,e122,
    ComplexPencilMain.permanent3] <;> ring

end ComplexPencilFull
