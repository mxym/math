import Entry005.Targets
import Entry005.EntryAffineInvariance

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

def truncationVertex {d : ℕ} (i : Fin d) : Space d :=
  EuclideanSpace.basisFun (Fin d) ℝ i

def truncationVertices {d : ℕ} (t : ℝ) : Fin d ⊕ Fin d → Space d
  | Sum.inl i => truncationVertex i
  | Sum.inr i => t • truncationVertex i

def truncationSimplexPoints {d : ℕ} (t : ℝ) (i : Fin d) : Fin (d + 1) → Space d :=
  Fin.cons (t • truncationVertex i) truncationVertex

def truncationBetaZero {d : ℕ} (t : ℝ) (x : Space d) : ℝ :=
  (1 - ∑ i, x i) / (1 - t)

def truncationBeta {d : ℕ} (t : ℝ) (i : Fin d) (x : Space d) : Fin (d + 1) → ℝ :=
  Fin.cons (truncationBetaZero t x)
    (fun j => x j - t * (if j = i then 1 else 0) * truncationBetaZero t x)

end Entry005
