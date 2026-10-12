import PermanentOnePointSquare
import BlockClosureAlgebra
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace Chollet

variable {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]

private theorem squarePermanent_nonneg
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    (M : Matrix γ γ ℝ) :
    0 ≤ Matrix.permanent (fun i j => M i j * M i j) := by
  classical
  unfold Matrix.permanent
  apply Finset.sum_nonneg
  intro σ _
  apply Finset.prod_nonneg
  intro i _
  simpa [pow_two] using sq_nonneg (M (σ i) i)

/-- Full matrix-level strong Chollet preservation under a one-vertex
coalescence, with all singleton pivot/minor positivity hypotheses visible.
This is a theorem about actual arbitrary-size Matrix.permanent, not a
scalar surrogate. No PSD or Lieb bound is tacitly assumed. -/
theorem strongChollet_onePointSum_of_pivots
    (A : Matrix (Option α) (Option α) ℝ)
    (B : Matrix (Option β) (Option β) ℝ)
    (hA : Matrix.permanent (fun i j => A i j * A i j) ≤
      Matrix.permanent A * (∏ i : Option α, A i i))
    (hB : Matrix.permanent (fun i j => B i j * B i j) ≤
      Matrix.permanent B * (∏ i : Option β, B i i))
    (hA_minor : Matrix.permanent
        (fun i j : α => A (some i) (some j) * A (some i) (some j)) ≤
      Matrix.permanent (fun i j : α => A (some i) (some j)) *
        (∏ i : α, A (some i) (some i)))
    (hB_minor : Matrix.permanent
        (fun i j : β => B (some i) (some j) * B (some i) (some j)) ≤
      Matrix.permanent (fun i j : β => B (some i) (some j)) *
        (∏ i : β, B (some i) (some i)))
    (hpivotA :
      A none none * Matrix.permanent (fun i j : α => A (some i) (some j)) ≤
        Matrix.permanent A)
    (hpivotB :
      B none none * Matrix.permanent (fun i j : β => B (some i) (some j)) ≤
        Matrix.permanent B)
    (hRA : 0 ≤ Matrix.permanent (fun i j : α => A (some i) (some j)))
    (hRB : 0 ≤ Matrix.permanent (fun i j : β => B (some i) (some j)))
    (hdiagA : ∀ i : Option α, 0 ≤ A i i)
    (hdiagB : ∀ i : Option β, 0 ≤ B i i) :
    Matrix.permanent (fun i j =>
        onePointSumMatrix A B i j * onePointSumMatrix A B i j) ≤
      Matrix.permanent (onePointSumMatrix A B) *
        (∏ i : Option (α ⊕ β), onePointSumMatrix A B i i) := by
  classical
  let a1 : ℝ := A none none
  let a2 : ℝ := B none none
  let h1 : ℝ := ∏ i : α, A (some i) (some i)
  let h2 : ℝ := ∏ i : β, B (some i) (some i)
  let P1 : ℝ := Matrix.permanent A
  let P2 : ℝ := Matrix.permanent B
  let R1 : ℝ := Matrix.permanent (fun i j : α => A (some i) (some j))
  let R2 : ℝ := Matrix.permanent (fun i j : β => B (some i) (some j))
  let Q1 : ℝ := Matrix.permanent (fun i j => A i j * A i j)
  let Q2 : ℝ := Matrix.permanent (fun i j => B i j * B i j)
  let T1 : ℝ := Matrix.permanent
    (fun i j : α => A (some i) (some j) * A (some i) (some j))
  let T2 : ℝ := Matrix.permanent
    (fun i j : β => B (some i) (some j) * B (some i) (some j))
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
  have hp1 : a1*R1 ≤ P1 := hpivotA
  have hp2 : a2*R2 ≤ P2 := hpivotB
  have hP1 : 0 ≤ P1 := (mul_nonneg ha1 hRA).trans hp1
  have hstrong1 : Q1 ≤ a1*h1*P1 := by
    calc
      Q1 ≤ P1 * (∏ i : Option α, A i i) := hA
      _ = a1*h1*P1 := by rw [hprodA]; ring
  have hstrong2 : Q2 ≤ a2*h2*P2 := by
    calc
      Q2 ≤ P2 * (∏ i : Option β, B i i) := hB
      _ = a2*h2*P2 := by rw [hprodB]; ring
  have hminor1 : T1 ≤ h1*R1 := by
    calc
      T1 ≤ R1*h1 := hA_minor
      _ = h1*R1 := mul_comm _ _
  have hminor2 : T2 ≤ h2*R2 := by
    calc
      T2 ≤ R2*h2 := hB_minor
      _ = h2*R2 := mul_comm _ _
  have hQ2 : 0 ≤ Q2 := squarePermanent_nonneg B
  have hT2 : 0 ≤ T2 :=
    squarePermanent_nonneg (fun i j : β => B (some i) (some j))

  have hglueProd :
      (∏ i : Option (α ⊕ β), onePointSumMatrix A B i i) =
        (a1+a2)*(h1*h2) := by
    rw [Fintype.prod_option, Fintype.prod_sum_type]
    rfl
  have hgluePer :
      Matrix.permanent (onePointSumMatrix A B) =
        P1*R2 + R1*P2 :=
    permanent_onePointSumMatrix A B
  have hglueSq :
      Matrix.permanent (fun i j =>
        onePointSumMatrix A B i j * onePointSumMatrix A B i j) =
        Q1*T2 + T1*Q2 + 2*a1*a2*(T1*T2) :=
    permanent_onePointSumMatrix_square A B
  have hscalar :=
    one_point_sum_algebra a1 a2 h1 h2 P1 P2 R1 R2 Q1 Q2 T1 T2
      ha1 ha2 hh1 hh2 hP1 hRA hRB hQ2 hT2
      hstrong1 hstrong2 hminor1 hminor2 hp1 hp2
  calc
    Matrix.permanent (fun i j =>
        onePointSumMatrix A B i j * onePointSumMatrix A B i j) =
      Q1*T2 + T1*Q2 + 2*a1*a2*(T1*T2) := hglueSq
    _ = Q1*T2 + T1*Q2 + 2*a1*a2*T1*T2 := by ring
    _ ≤ h1*h2*(a1+a2)*(P1*R2+R1*P2) := hscalar
    _ = Matrix.permanent (onePointSumMatrix A B) *
        (∏ i : Option (α ⊕ β), onePointSumMatrix A B i i) := by
      rw [hgluePer, hglueProd]
      ring

end Chollet

#print axioms Chollet.strongChollet_onePointSum_of_pivots
