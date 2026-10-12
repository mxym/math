import CycleMatchingBounds
import CycleGraphMatrix
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic.Linarith

namespace Chollet

/-- The only two unformalized combinatorial cycle-cover identities needed
to turn the proved all-n scalar recurrence into a genuine all-odd-cycle
matrix theorem. The mathematical premises remain explicit hypotheses. -/
theorem cycleGraph_full_strong_of_permanent_formulas (n : ℕ)
    (hperm :
      Matrix.permanent ((SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ) + 2 =
        (cycleMatchingWeight 2 (n+3) : ℝ))
    (hsquare :
      Matrix.permanent (fun i j : Fin (n+3) =>
        (SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ i j *
        (SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ i j) =
          (cycleMatchingWeight 4 (n+3) : ℝ) + 2) :
    Matrix.permanent (fun i j : Fin (n+3) =>
        (SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ i j *
        (SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ i j) ≤
      Matrix.permanent ((SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ) *
        (∏ i : Fin (n+3),
          ((SimpleGraph.cycleGraph (n+3)).degree i : ℝ)) := by
  classical
  have hpow : 2^(n+4) = 2 * (2:ℕ)^(n+3) := by
    rw [show n+4=(n+3)+1 by omega, pow_succ]
    omega
  have hnat : cycleMatchingWeight 4 (n+3) + 2*2^(n+3)+2 ≤
      2^(n+3)*cycleMatchingWeight 2 (n+3) := by
    have h := cycleMatchingWeight_strict_gap n
    rw [hpow] at h
    exact h
  have hreal :
      (cycleMatchingWeight 4 (n+3) : ℝ) +
        2*(2:ℝ)^(n+3)+2 ≤
          (2:ℝ)^(n+3)*(cycleMatchingWeight 2 (n+3) : ℝ) := by
    exact_mod_cast hnat
  have hdegree :
      (∏ i : Fin (n+3),
         ((SimpleGraph.cycleGraph (n+3)).degree i : ℝ)) =
      (2:ℝ)^(n+3) := by
    have hd (i : Fin (n+3)) :
        (SimpleGraph.cycleGraph (n+3)).degree i = 2 :=
      cycleGraph_degree_all_two n i
    simp [hd]
  have hreal' := hreal
  rw [← hperm] at hreal'
  have hbound :
      (cycleMatchingWeight 4 (n+3) : ℝ) + 2 ≤
        (2:ℝ)^(n+3) *
          Matrix.permanent ((SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ) := by
    nlinarith [hreal']
  calc
    Matrix.permanent (fun i j : Fin (n+3) =>
        (SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ i j *
        (SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ i j) =
      (cycleMatchingWeight 4 (n+3) : ℝ) + 2 := hsquare
    _ ≤ (2:ℝ)^(n+3) *
          Matrix.permanent ((SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ) :=
      hbound
    _ = Matrix.permanent ((SimpleGraph.cycleGraph (n+3)).lapMatrix ℝ) *
        (∏ i : Fin (n+3),
          ((SimpleGraph.cycleGraph (n+3)).degree i : ℝ)) := by
      rw [hdegree]
      ring

end Chollet

#print axioms Chollet.cycleGraph_full_strong_of_permanent_formulas
