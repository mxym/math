import PermutationTV

namespace ComplexPencilDistribution

open ComplexPencilTensor
open ComplexPencilReal
open ComplexPencilFull

noncomputable section

/-- The expectation of the product of the three rows evaluated at
the (possibly signed) six-permutation weights. -/
def expectedProduct (p : Fin 6 → ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  ∑ j : Fin 6, ((p j : ℝ) : ℂ) *
       A 0 (first j) * A 1 (second j) * A 2 (third j)

def expectationBound (p : Fin 6 → ℝ) : Prop :=
  ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
    Complex.normSq (expectedProduct p A) ≤
      (ComplexPencilReal.normalizedRowSq A 0) *
      (ComplexPencilReal.normalizedRowSq A 1) *
      (ComplexPencilReal.normalizedRowSq A 2)

/-- Distributional moments are literally the same as the normalized
Mathlib matrix permanent–determinant pencil, for all nine complex
entries and every real parity parameter. -/
theorem expectedProduct_law_rows
    (t : ℝ) (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    expectedProduct (weight t)
      (rowsMatrix a0 a1 a2 b0 b1 b2 c0 c1 c2) =
    ComplexPencilReal.law t
      (rowsMatrix a0 a1 a2 b0 b1 b2 c0 c1 c2) := by
  unfold expectedProduct ComplexPencilReal.law
  rw [ComplexPencilFull.permanent_row_expansion,
      ComplexPencilFull.det_row_expansion]
  simp [weight, first, second, third, Fin.sum_univ_succ,
    rowsMatrix, ComplexPencilMain.permanent3,
    ComplexPencilMain.determinant3]
  push_cast
  ring

theorem expectedProduct_law (t : ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℂ) :
    expectedProduct (weight t) A = ComplexPencilReal.law t A := by
  conv_lhs => rw [←ComplexPencilFull.rowsMatrix_surjective A]
  conv_rhs => rw [←ComplexPencilFull.rowsMatrix_surjective A]
  exact expectedProduct_law_rows t
    (A 0 0) (A 0 1) (A 0 2)
    (A 1 0) (A 1 1) (A 1 2)
    (A 2 0) (A 2 1) (A 2 2)

theorem expectationBound_weight_iff (t : ℝ) :
    expectationBound (weight t) ↔ ComplexPencilReal.LawBound t 1 := by
  unfold expectationBound ComplexPencilReal.LawBound
  simp only [expectedProduct_law, one_mul]

#print axioms ComplexPencilDistribution.expectationBound_weight_iff

end
end ComplexPencilDistribution
