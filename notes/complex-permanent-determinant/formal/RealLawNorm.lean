import RealLaw
import MatrixTheorem
import Mathlib.Analysis.Complex.Basic

namespace ComplexPencilReal
open ComplexPencilFull

noncomputable section

def law (t : ℝ) (A : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
 (1/6:ℂ)*(A.permanent + ((6*t:ℝ):ℂ)*A.det)

def normalizedRowSq (A : Matrix (Fin 3) (Fin 3) ℂ)
    (i : Fin 3) : ℝ := matRowSq A i / 3

def LawBound (t B : ℝ) : Prop :=
   ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
    Complex.normSq (law t A) ≤
      B*normalizedRowSq A 0*normalizedRowSq A 1*
        normalizedRowSq A 2

theorem law_normSq_eq (t : ℝ) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    Complex.normSq (law t A) =
        Complex.normSq (A.permanent+((6*t:ℝ):ℂ)*A.det)/36 := by
  unfold law
  rw [Complex.normSq_mul]
  norm_num [Complex.normSq_ofReal]
  ring

theorem law_bound_iff_matrix (t B : ℝ) :
    LawBound t B ↔ matrixSquaredIneq ((6*t:ℝ):ℂ) ((4/3)*B) := by
  constructor
  · intro h A
    have hh:=h A
    rw [law_normSq_eq] at hh
    unfold normalizedRowSq at hh
    nlinarith
  · intro h A
    have hh:=h A
    rw [law_normSq_eq]
    unfold normalizedRowSq
    nlinarith

theorem law_bound_exact (t B : ℝ) :
    LawBound t B ↔
       max (1:ℝ) ((3/4)*(1+|6*t|)^2) ≤ B := by
  rw [law_bound_iff_matrix,matrix_squared_norm_iff,
      normBoundSq_real]
  constructor
  · intro hh
    apply max_le
    · have hbase : (4/3:ℝ)≤(4/3)*B :=
        le_trans (le_max_left _ _) hh
      nlinarith
    · have hright : (1+|6*t|)^2 ≤ (4/3)*B :=
        le_trans (le_max_right _ _) hh
      nlinarith
  · intro hh
    apply max_le
    · have hx : (1:ℝ)≤B:=le_trans (le_max_left _ _) hh
      nlinarith
    · have hx : (3/4)*(1+|6*t|)^2≤B :=
        le_trans (le_max_right _ _) hh
      nlinarith

#print axioms ComplexPencilReal.law_bound_exact

end
end ComplexPencilReal
