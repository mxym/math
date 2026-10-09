import CholletPSD
import RootStrongClosure
import PermanentDiagonalStability
import Mathlib.Logic.Equiv.Option

/-! Discharge the pivot assumptions in the exact permanent closure library
from proved PSD inequalities. No Lieb inequality is assumed. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V α β : Type*} [Fintype V] [DecidableEq V]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
noncomputable section

theorem strongChollet_diagonalBump_psd
    (A : Matrix V V ℝ) (hA : A.PosSemidef) (v : V) (t : ℝ) (ht : 0 ≤ t)
    (hstrong : (squareMatrix A).permanent ≤ A.permanent * ∏ i,A i i)
    (hminor : (squareMatrix (principalExcept A v)).permanent ≤
      (principalExcept A v).permanent * ∏ i,principalExcept A v i i) :
    (squareMatrix (diagonalBump A v t)).permanent ≤
      (diagonalBump A v t).permanent * ∏ i,diagonalBump A v t i i := by
  apply strongChollet_diagonalBump_of_pivot A v t ht (fun _ => hA.diag_nonneg) hstrong hminor
  exact permanent_psd_singleton A hA v

theorem permanent_psd_option_pivot (A : Matrix (Option α) (Option α) ℝ)
    (hA : A.PosSemidef) :
    A none none * (Matrix.permanent (fun i j : α => A (some i) (some j))) ≤
      A.permanent := by
  let e : α ≃ {i : Option α // i ≠ none} :=
    Equiv.optionSubtype none ⟨Equiv.refl _,rfl⟩
  have hp := permanent_reindex_equiv (principalExcept A none) e
  change Matrix.permanent (fun i j : α => A (some i) (some j)) =
    Matrix.permanent (principalExcept A none) at hp
  rw [hp]
  exact permanent_psd_singleton A hA none

theorem rootStrong_of_psd (A : Matrix (Option α) (Option α) ℝ)
    (hA : A.PosSemidef)
    (hwhole : (squareMatrix A).permanent ≤ A.permanent * ∏ i,A i i)
    (hdeleted : (Matrix.permanent (fun i j : α => A (some i) (some j) *
      A (some i) (some j))) ≤
      (Matrix.permanent (fun i j : α => A (some i) (some j))) *
        ∏ i : α,A (some i) (some i)) : RootStrong A where
  diag_nonneg := fun _ => hA.diag_nonneg
  whole := hwhole
  deleted := hdeleted
  pivot := permanent_psd_option_pivot A hA
  deleted_nonneg := permanent_psd_nonneg _ (hA.submatrix some)

theorem rootStrong_onePointSum_psd
    (A : Matrix (Option α) (Option α) ℝ) (B : Matrix (Option β) (Option β) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hwholeA : (squareMatrix A).permanent ≤ A.permanent * ∏ i,A i i)
    (hwholeB : (squareMatrix B).permanent ≤ B.permanent * ∏ i,B i i)
    (hdeletedA : (Matrix.permanent (fun i j : α => A (some i) (some j) *
      A (some i) (some j))) ≤
      (Matrix.permanent (fun i j : α => A (some i) (some j))) *
        ∏ i : α,A (some i) (some i))
    (hdeletedB : (Matrix.permanent (fun i j : β => B (some i) (some j) *
      B (some i) (some j))) ≤
      (Matrix.permanent (fun i j : β => B (some i) (some j))) *
        ∏ i : β,B (some i) (some i)) :
    RootStrong (onePointSumMatrix A B) :=
  RootStrong.onePointSum A B (rootStrong_of_psd A hA hwholeA hdeletedA)
    (rootStrong_of_psd B hB hwholeB hdeletedB)

end
end Chollet
