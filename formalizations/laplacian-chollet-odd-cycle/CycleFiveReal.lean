import CycleFiveInt
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic.NormNum

namespace Chollet

/-- Permanent commutes with canonical integer-to-real casting for arbitrary
finite matrices; this proof checks the genuine permutation sum. -/
theorem permanent_int_cast_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) :
    Matrix.permanent (fun i j => (A i j : ℝ)) =
      ((Matrix.permanent A : ℤ) : ℝ) := by
  classical
  simp [Matrix.permanent]

/-- The official Laplacian constructions commute with integer-to-real cast. -/
theorem laplacian_int_cast_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj]
    (i j : ι) :
    ((G.lapMatrix ℤ) i j : ℝ) = (G.lapMatrix ℝ) i j := by
  classical
  by_cases hij : i = j
  · subst j
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
  · simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix, hij]


/-- The complete real permanent of the genuine Mathlib five-cycle Laplacian
is computed from the separately certified integer permanent without a
floating-point approximation. -/
theorem cycleFive_real_permanent :
    Matrix.permanent ((SimpleGraph.cycleGraph 5).lapMatrix ℝ) = (80:ℝ) := by
  let G := SimpleGraph.cycleGraph 5
  have hcast :
      (fun i j : Fin 5 => ((G.lapMatrix ℤ) i j : ℝ)) =
      G.lapMatrix ℝ := by
    ext i j
    exact laplacian_int_cast_real G i j
  calc
    Matrix.permanent (G.lapMatrix ℝ) =
      Matrix.permanent (fun i j : Fin 5 => ((G.lapMatrix ℤ) i j : ℝ)) :=
      congrArg Matrix.permanent hcast.symm
    _ = ((Matrix.permanent (intCycleL 5) : ℤ) : ℝ) := by
      exact permanent_int_cast_real (intCycleL 5)
    _ = (80:ℝ) := by rw [cycleFive_int_permanent]; norm_num

theorem cycleFive_real_square_permanent :
    Matrix.permanent (fun i j : Fin 5 =>
        (SimpleGraph.cycleGraph 5).lapMatrix ℝ i j *
        (SimpleGraph.cycleGraph 5).lapMatrix ℝ i j) =
      (1366:ℝ) := by
  let G := SimpleGraph.cycleGraph 5
  let Q : Matrix (Fin 5) (Fin 5) ℤ :=
    fun i j => intCycleL 5 i j * intCycleL 5 i j
  have hcast :
      (fun i j : Fin 5 => (Q i j : ℝ)) =
        (fun i j : Fin 5 =>
          G.lapMatrix ℝ i j * G.lapMatrix ℝ i j) := by
    ext i j
    simp only [Q, Int.cast_mul]
    change ((G.lapMatrix ℤ) i j : ℝ) * ((G.lapMatrix ℤ) i j : ℝ) =
      (G.lapMatrix ℝ) i j * (G.lapMatrix ℝ) i j
    rw [laplacian_int_cast_real G i j]
  calc
    Matrix.permanent
        (fun i j : Fin 5 => G.lapMatrix ℝ i j * G.lapMatrix ℝ i j) =
      Matrix.permanent (fun i j : Fin 5 => (Q i j : ℝ)) :=
      congrArg Matrix.permanent hcast.symm
    _ = ((Matrix.permanent Q : ℤ) : ℝ) := permanent_int_cast_real Q
    _ = (1366:ℝ) := by
      change (((Matrix.permanent (fun i j : Fin 5 =>
        intCycleL 5 i j * intCycleL 5 i j) : ℤ) : ℝ) = (1366:ℝ))
      rw [cycleFive_int_hadamard_permanent]
      norm_num

/-- A genuine non-bipartite graph instance, without replacing its Laplacian
by an unrelated scalar model. -/
theorem cycleFive_real_full_chollet :
    Matrix.permanent (fun i j : Fin 5 =>
        (SimpleGraph.cycleGraph 5).lapMatrix ℝ i j *
        (SimpleGraph.cycleGraph 5).lapMatrix ℝ i j) ≤
      Matrix.permanent ((SimpleGraph.cycleGraph 5).lapMatrix ℝ) *
        (∏ i : Fin 5, ((SimpleGraph.cycleGraph 5).degree i : ℝ)) := by
  have hd :
      (∏ i : Fin 5, ((SimpleGraph.cycleGraph 5).degree i : ℝ)) =
      (32:ℝ) := by
    have hdeg : ∀ i : Fin 5, (SimpleGraph.cycleGraph 5).degree i = 2 :=
      fun i => cycleGraph_degree_all_two 2 i
    simp only [hdeg]
    norm_num
  rw [cycleFive_real_square_permanent, cycleFive_real_permanent, hd]
  norm_num

end Chollet

#print axioms Chollet.cycleFive_real_full_chollet
