import Mxym.RademacherEquality
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The horizontal cofactor relation and independent-sign cancellation used
in entry005 v3, Section 6, and v4, equation (3.1). -/
namespace Mxym.Determinant
open scoped BigOperators Classical
open Mxym.Rademacher

noncomputable def lift {d : ℕ} (x : Matrix (Fin d) (Fin (d + 1)) ℝ)
    (a : Fin (d + 1) → ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => Fin.cases (a j) (fun k => x k j) i

noncomputable def cofactor {d : ℕ} (x : Matrix (Fin d) (Fin (d + 1)) ℝ)
    (j : Fin (d + 1)) : ℝ :=
  (-1) ^ (j : ℕ) * (x.submatrix id j.succAbove).det

 theorem lift_expansion {d : ℕ} (x : Matrix (Fin d) (Fin (d + 1)) ℝ)
    (a : Fin (d + 1) → ℝ) :
    (lift x a).det = ∑ j, a j * cofactor x j := by
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  have hm : (lift x a).submatrix Fin.succ j.succAbove = x.submatrix id j.succAbove := by
    ext i k
    simp [lift, Matrix.submatrix_apply]
  rw [hm]
  simp [lift, cofactor]
  ring

 theorem horizontal_cofactor_relation {d : ℕ} (x : Matrix (Fin d) (Fin (d + 1)) ℝ)
    (i : Fin d) : ∑ j, cofactor x j * x i j = 0 := by
  have hz : (lift x (x i)).det = 0 := by
    apply Matrix.det_zero_of_row_eq (Ne.symm (Fin.succ_ne_zero i))
    funext j
    simp [lift]
  rw [lift_expansion] at hz
  simpa only [mul_comm] using hz

 theorem sign_cancellation {d : ℕ} (x : Matrix (Fin d) (Fin (d + 1)) ℝ)
    (ε : Fin (d + 1) → Bool) :
    |(lift (fun i j => sign (ε j) * x i j) (fun _ => 1)).det| =
      |signedSum (cofactor x) ε| := by
  let S := lift (fun i j => sign (ε j) * x i j) (fun _ => 1)
  have hm : S * Matrix.diagonal (fun j => sign (ε j)) = lift x (fun j => sign (ε j)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [S, lift]
    · cases h : ε j <;> simp [S, lift, h, sign]
  have hp : |∏ j : Fin (d + 1), sign (ε j)| = 1 := by
    rw [Finset.abs_prod]
    simp
  have hdet := congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => |M.det|) hm
  rw [Matrix.det_mul, Matrix.det_diagonal, abs_mul, hp, mul_one, lift_expansion] at hdet
  exact hdet

 theorem sign_average_eq {d : ℕ} (x : Matrix (Fin d) (Fin (d + 1)) ℝ) :
    (∑ ε : Fin (d + 1) → Bool,
      |(lift (fun i j => sign (ε j) * x i j) (fun _ => 1)).det|) /
      Fintype.card (Fin (d + 1) → Bool) = mean (cofactor x) := by
  simp_rw [sign_cancellation]
  rfl

 theorem balanced_sign_average_bound {d : ℕ} (x : Matrix (Fin d) (Fin (d + 1)) ℝ)
    (hbal : ∀ i, |cofactor x i| ≤ (∑ j, |cofactor x j|) / 2) :
    (∑ ε : Fin (d + 1) → Bool,
      |(lift (fun i j => sign (ε j) * x i j) (fun _ => 1)).det|) /
      Fintype.card (Fin (d + 1) → Bool) ≤ (∑ j, |cofactor x j|) / 2 := by
  rw [sign_average_eq]
  exact balanced_bound (cofactor x) hbal

 theorem balanced_sign_average_equality_iff {d : ℕ} (x : Matrix (Fin d) (Fin (d + 1)) ℝ)
    (hbal : ∀ i, |cofactor x i| ≤ (∑ j, |cofactor x j|) / 2) :
    ((∑ ε : Fin (d + 1) → Bool,
      |(lift (fun i j => sign (ε j) * x i j) (fun _ => 1)).det|) /
      Fintype.card (Fin (d + 1) → Bool) = (∑ j, |cofactor x j|) / 2) ↔
      Fintype.card {i // cofactor x i ≠ 0} ≤ 3 ∨
        ∃ i, |cofactor x i| = (∑ j, |cofactor x j|) / 2 := by
  rw [sign_average_eq]
  exact balanced_equality_iff (cofactor x) hbal

end Mxym.Determinant
