import PermanentOnePointSquare
import BlockClosureAlgebra
import PermanentDirectSumStability

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Matrix-level strong Chollet closure under one-vertex coalescence,
assuming genuine permanent-pivot bounds and strong inequalities for
both blocks and their principal root deletions.

No positivity or permanent block inequality is silently asserted for PSD
matrices: the only still-unformalized ingredients are *visible premises*.
The final inequality is for the true Mathlib permanent, at arbitrary size. -/
theorem strongChollet_onePointSum_of_pivot
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ)
    (hdiagA : ∀ i, 0 ≤ A i i)
    (hdiagB : ∀ i, 0 ≤ B i i)
    (hA : Matrix.permanent (fun i j => A i j * A i j) ≤
      Matrix.permanent A * (∏ i, A i i))
    (hB : Matrix.permanent (fun i j => B i j * B i j) ≤
      Matrix.permanent B * (∏ i, B i i))
    (hA0 : Matrix.permanent (fun i j : α =>
          A (some i) (some j) * A (some i) (some j)) ≤
      Matrix.permanent (fun i j : α => A (some i) (some j)) *
        (∏ i : α, A (some i) (some i)))
    (hB0 : Matrix.permanent (fun i j : β =>
          B (some i) (some j) * B (some i) (some j)) ≤
      Matrix.permanent (fun i j : β => B (some i) (some j)) *
        (∏ i : β, B (some i) (some i)))
    (hR1 : 0 ≤ Matrix.permanent (fun i j : α => A (some i) (some j)))
    (hR2 : 0 ≤ Matrix.permanent (fun i j : β => B (some i) (some j)))
    (hpivotA : A none none *
        Matrix.permanent (fun i j : α => A (some i) (some j)) ≤
      Matrix.permanent A)
    (hpivotB : B none none *
        Matrix.permanent (fun i j : β => B (some i) (some j)) ≤
      Matrix.permanent B) :
    Matrix.permanent
        (fun i j => onePointSumMatrix A B i j * onePointSumMatrix A B i j) ≤
      Matrix.permanent (onePointSumMatrix A B) *
        (∏ i, onePointSumMatrix A B i i) := by
  classical
  let a1 := A none none
  let a2 := B none none
  let h1 : ℝ := ∏ i : α, A (some i) (some i)
  let h2 : ℝ := ∏ i : β, B (some i) (some i)
  let P1 := Matrix.permanent A
  let P2 := Matrix.permanent B
  let R1 := Matrix.permanent (fun i j : α => A (some i) (some j))
  let R2 := Matrix.permanent (fun i j : β => B (some i) (some j))
  let Q1 := Matrix.permanent (fun i j => A i j * A i j)
  let Q2 := Matrix.permanent (fun i j => B i j * B i j)
  let T1 := Matrix.permanent (fun i j : α =>
    A (some i) (some j) * A (some i) (some j))
  let T2 := Matrix.permanent (fun i j : β =>
    B (some i) (some j) * B (some i) (some j))
  have ha1 : 0 ≤ a1 := hdiagA none
  have ha2 : 0 ≤ a2 := hdiagB none
  have hh1 : 0 ≤ h1 := by
    dsimp [h1]
    apply Finset.prod_nonneg
    intro i _
    exact hdiagA (some i)
  have hh2 : 0 ≤ h2 := by
    dsimp [h2]
    apply Finset.prod_nonneg
    intro i _
    exact hdiagB (some i)
  have hprodA : (∏ i : Option α, A i i) = a1*h1 := by
    rw [Fintype.prod_option]
  have hprodB : (∏ i : Option β, B i i) = a2*h2 := by
    rw [Fintype.prod_option]
  have hstrong1 : Q1 ≤ a1*h1*P1 := by
    calc
      Q1 ≤ P1 * (∏ i : Option α, A i i) := hA
      _ = a1*h1*P1 := by rw [hprodA]; ring
  have hstrong2 : Q2 ≤ a2*h2*P2 := by
    calc
      Q2 ≤ P2 * (∏ i : Option β, B i i) := hB
      _ = a2*h2*P2 := by rw [hprodB]; ring
  have hm1 : T1 ≤ h1*R1 := by
    calc
      T1 ≤ R1*h1 := hA0
      _ = _ := by ring
  have hm2 : T2 ≤ h2*R2 := by
    calc
      T2 ≤ R2*h2 := hB0
      _ = _ := by ring
  have hP1 : 0 ≤ P1 := le_trans (mul_nonneg ha1 hR1) hpivotA
  have hQ2 : 0 ≤ Q2 := permanent_entrywiseSquare_nonneg B
  have hT2 : 0 ≤ T2 :=
    permanent_entrywiseSquare_nonneg
      (fun i j : β => B (some i) (some j))
  have hs : Q1*T2 + T1*Q2 + 2*a1*a2*T1*T2 ≤
      h1*h2*(a1+a2)*(P1*R2+R1*P2) :=
    one_point_sum_algebra a1 a2 h1 h2 P1 P2 R1 R2 Q1 Q2 T1 T2
      ha1 ha2 hh1 hh2 hP1 hR1 hR2 hQ2 hT2
      hstrong1 hstrong2 hm1 hm2 hpivotA hpivotB
  have hprodC :
      (∏ i : Option (α ⊕ β), onePointSumMatrix A B i i) =
        (a1+a2)*(h1*h2) := by
    rw [Fintype.prod_option, Fintype.prod_sum_type]
    change (a1+a2)*(h1*h2) = _
    rfl
  have hperC : Matrix.permanent (onePointSumMatrix A B) =
      P1*R2 + R1*P2 := permanent_onePointSumMatrix A B
  have hperSqC :
      Matrix.permanent (fun i j =>
        onePointSumMatrix A B i j * onePointSumMatrix A B i j) =
      Q1*T2 + T1*Q2 + 2*a1*a2*T1*T2 := by
    dsimp [Q1,Q2,T1,T2,a1,a2]
    rw [permanent_onePointSumMatrix_square]
    ring
  calc
    Matrix.permanent (fun i j =>
        onePointSumMatrix A B i j * onePointSumMatrix A B i j) =
        Q1*T2 + T1*Q2 + 2*a1*a2*T1*T2 := hperSqC
    _ ≤ h1*h2*(a1+a2)*(P1*R2+R1*P2) := hs
    _ = Matrix.permanent (onePointSumMatrix A B) *
        (∏ i, onePointSumMatrix A B i i) := by
          rw [hprodC,hperC]
          ring

end Chollet

#print axioms Chollet.strongChollet_onePointSum_of_pivot
