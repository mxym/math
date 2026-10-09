import AssessmentImports
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Hadamard
import OAI.Combinatorics.PerfectMatching.Polytope

/-! Interface assessment only. The all-graph Chollet proposition below is stated,
but not asserted as a theorem. The actual compiled results are the existing
perfect-matching polytope theorem and genuine Laplacian principal-submatrix facts. -/

namespace CholletAssessment
open Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def principalLaplacian (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Matrix S S ℝ :=
  (G.lapMatrix ℝ).submatrix Subtype.val Subtype.val

theorem principalLaplacian_posSemidef (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : (principalLaplacian G S).PosSemidef := by
  exact (G.posSemidef_lapMatrix (R := ℝ)).submatrix Subtype.val

theorem principalLaplacian_diag (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : S) : principalLaplacian G S v v = (G.degree v.val : ℝ) := by
  simp [principalLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix]

/-- Exact target: diagonal degrees are those in G, not those in the induced graph. -/
def StrongCholletForGraph (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset V,
    Matrix.permanent ((principalLaplacian G S).hadamard (principalLaplacian G S)) ≤
      Matrix.permanent (principalLaplacian G S) * ∏ v : S, (G.degree v.val : ℝ)

/-- This is an unproved target proposition, not a new axiom or certification. -/
def AllSimpleGraphStrongChollet : Prop :=
  ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], StrongCholletForGraph G

/-- Missing library input, recorded as a proposition only. -/
def RealLiebBlockBound : Prop :=
  ∀ n m : ℕ, ∀ A : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ,
    A.PosSemidef →
      (A.submatrix Sum.inl Sum.inl).permanent * (A.submatrix Sum.inr Sum.inr).permanent ≤
        A.permanent

open OAI.MatchingEntropy

theorem edmonds_perfect_matching_polytope {E : Type*} [Fintype E] [DecidableEq E]
    (G : LooplessGraph V E) (heven : Even (Fintype.card V)) :
    G.polytope = G.constraintPolytope :=
  G.polytope_eq_constraints heven

/-- A feasible point yields an actual finite probability law on genuine perfect matchings. -/
theorem edmonds_perfect_matching_distribution {E : Type*} [Fintype E] [DecidableEq E]
    (G : LooplessGraph V E) (heven : Even (Fintype.card V)) (x : E → ℝ)
    (hx : x ∈ G.constraintPolytope) :
    ∃ p : G.Matching → ℝ, (∀ M, 0 ≤ p M) ∧ (∑ M, p M = 1) ∧ G.mean p = x := by
  have hp : x ∈ G.polytope := by rwa [G.polytope_eq_constraints heven]
  obtain ⟨p, hp, heq⟩ := (G.mem_polytope_iff x).mp hp
  exact ⟨p, hp.1, hp.2, heq⟩

end CholletAssessment
