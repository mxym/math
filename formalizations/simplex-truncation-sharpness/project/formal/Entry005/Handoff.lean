import Entry005.Targets
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
Exact statement for the second Lean worker. This is an UNPROVED goal definition,
not a theorem, axiom or hidden premise of the proved projection-cap chain.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Entry005

/-- Columns are the lifted vertices (1,p_j); row zero is the affine coordinate.
Both simplices use the same row convention. -/
def augmentedVertices {d : ℕ} (p : Fin (d + 1) → Space d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => Fin.cases 1 (fun k : Fin d => p j k) i

/-- Rows index enclosing vertices; columns index inscribed vertices.
This is a concrete matrix constructed from genuine simplex points. -/
def simplexBarycentricMatrix {d : ℕ} (P S : Affine.Simplex ℝ (Space d) d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  (augmentedVertices P.points)⁻¹ * augmentedVertices S.points

/-- Complete interface target, with inclusion as its only extra geometric input.
No stochasticity, determinant-volume correspondence or volume positivity is
assumed: each is an output to be proved by the implementing worker. -/
def simplexMatrixVolumeInterfaceGoal : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ P S : Affine.Simplex ℝ (Space d) d,
    simplexSet S ⊆ simplexSet P →
      (augmentedVertices P.points).det ≠ 0 ∧
      volume (simplexSet P) ≠ ⊤ ∧ volume (simplexSet S) ≠ ⊤ ∧
      0 < (volume (simplexSet P)).toReal ∧
      (∀ i j, 0 ≤ simplexBarycentricMatrix P S i j) ∧
      (∀ j, ∑ i, simplexBarycentricMatrix P S i j = 1) ∧
      (∀ j, ∑ i, (simplexBarycentricMatrix P S i j) • P.points i = S.points j) ∧
      |(simplexBarycentricMatrix P S).det| =
        (volume (simplexSet S)).toReal / (volume (simplexSet P)).toReal

end Entry005
