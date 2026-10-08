import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Permanent

namespace Chollet

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual principal submatrix of the library's graph Laplacian. -/
def laplacianPrincipal (S : Finset V) :
    Matrix {v : V // v ∈ S} {v : V // v ∈ S} ℝ :=
  fun v w => (G.lapMatrix ℝ) v.val w.val

/-- Degree product is taken in the original graph, not its induced subgraph. -/
def originalDegreeProduct (S : Finset V) : ℝ :=
  ∏ v : {v : V // v ∈ S}, (G.degree v.val : ℝ)

/-- Complete strong Chollet target, including empty principal submatrix. -/
def StrongChollet : Prop :=
  ∀ S : Finset V,
    Matrix.permanent (fun v w =>
        laplacianPrincipal G S v w * laplacianPrincipal G S v w)
      ≤ Matrix.permanent (laplacianPrincipal G S) *
        originalDegreeProduct G S

end Chollet
