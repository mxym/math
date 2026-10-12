import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Actual finite-dimensional linear forced ODEs and global uniqueness.
No transfer-function or solution-existence hypothesis is used in the uniqueness proof. -/
open Matrix
noncomputable section
namespace HydrologyTree

variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixOperator (A : Matrix I I ℝ) : (I → ℝ) →L[ℝ] (I → ℝ) :=
  LinearMap.toContinuousLinearMap A.mulVecLin

@[simp] lemma matrixOperator_apply (A : Matrix I I ℝ) (z : I → ℝ) :
    matrixOperator A z = A *ᵥ z := rfl

/-- The actual classical state equation, at every real time. -/
def IsForcedMatrixSolution (A : Matrix I I ℝ) (b : I → ℝ)
    (u : ℝ → ℝ) (z : ℝ → I → ℝ) : Prop :=
  ∀ s : ℝ, HasDerivAt z (A *ᵥ z s + u s • b) s

/-- Global uniqueness for the actual forced matrix ODE with any common forcing.
No sign, stability or diagonalizability restriction is imposed on A. -/
theorem forcedMatrixSolution_unique (A : Matrix I I ℝ) (b : I → ℝ)
    (u : ℝ → ℝ) (z y : ℝ → I → ℝ) (a : ℝ)
    (hz : IsForcedMatrixSolution A b u z) (hy : IsForcedMatrixSolution A b u y)
    (ha : z a = y a) : z=y := by
  apply ODE_solution_unique_univ (s := fun _ => Set.univ)
    (K := ‖matrixOperator A‖₊) (t₀ := a)
    (v := fun s v => matrixOperator A v + u s • b)
  · intro s p hp q hq
    simpa only [edist_add_right] using (matrixOperator A).lipschitzWith p q
  · intro s
    exact ⟨hz s,Set.mem_univ _⟩
  · intro s
    exact ⟨hy s,Set.mem_univ _⟩
  · exact ha

end HydrologyTree
