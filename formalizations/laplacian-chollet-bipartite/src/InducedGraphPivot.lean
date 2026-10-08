import MatrixSignPivotGeneral
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Chollet

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem pivotLap_submatrix_entry (i j : V) :
    (G.lapMatrix ℝ) i j =
      if i = j then (G.degree i : ℝ)
      else if G.Adj i j then -1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
  · simp only [SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply, if_neg hij]
    by_cases hadj : G.Adj i j <;> simp [hadj]

/-- Any principal submatrix of the *actual* Mathlib Laplacian, supported
on a bipartite induced vertex set of an otherwise ARBITRARY finite graph,
satisfies the singleton permanent-pivot inequality at any chosen vertex.
The degree is that of the ORIGINAL ambient graph. -/
theorem laplacian_principal_pivot_of_inducedBipartite
    (S : Finset V)
    (hS : (G.induce (S : Set V)).IsBipartite)
    (v : {x : V // x ∈ S}) :
    (G.lapMatrix ℝ) v.val v.val *
      Matrix.permanent (principalExcept
        (fun i j : {x : V // x ∈ S} =>
          (G.lapMatrix ℝ) i.val j.val) v) ≤
      Matrix.permanent
        (fun i j : {x : V // x ∈ S} =>
          (G.lapMatrix ℝ) i.val j.val) := by
  classical
  obtain ⟨left,right,hpart⟩ := hS.exists_isBipartiteWith
  let sign : {x : V // x ∈ S} → ℝ :=
    fun i => if i ∈ left then 1 else -1
  have hs : ∀ i, (sign i)^2 = 1 := by
    intro i
    by_cases hi : i ∈ left <;> simp [sign, hi]
  have hsadj : ∀ i j : {x : V // x ∈ S},
      G.Adj i.val j.val → sign i * sign j = -1 := by
    intro i j hij
    have hInduced : (G.induce (S : Set V)).Adj i j := hij
    rcases hpart.mem_of_adj hInduced with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · have hnj : j ∉ left := hpart.disjoint.subset_compl_left hj
      simp [sign, hi, hnj]
    · have hni : i ∉ left := hpart.disjoint.subset_compl_left hi
      simp [sign, hni, hj]
  let A : Matrix {x : V // x ∈ S} {x : V // x ∈ S} ℝ :=
    fun i j => (G.lapMatrix ℝ) i.val j.val
  have hn : ∀ i j, 0 ≤ signedSwitch A sign i j := by
    intro i j
    change 0 ≤ sign i * (G.lapMatrix ℝ) i.val j.val * sign j
    rw [pivotLap_submatrix_entry]
    by_cases hij : i.val = j.val
    · have heq : i = j := Subtype.ext hij
      subst j
      simp only [ite_true]
      have hdeg : 0 ≤ (G.degree i.val : ℝ) := Nat.cast_nonneg _
      have heqsign :
          sign i * (G.degree i.val : ℝ) * sign i =
            (G.degree i.val : ℝ) := by
        calc
          _ = (sign i)^2 * (G.degree i.val : ℝ) := by ring
          _ = _ := by rw [hs i]; ring
      rw [heqsign]
      exact hdeg
    · simp only [if_neg hij]
      by_cases hadj : G.Adj i.val j.val
      · simp only [if_pos hadj]
        have h := hsadj i j hadj
        nlinarith
      · simp [hadj]
  exact permanent_pivot_of_signSwitch_nonnegative A v sign hs hn

end Chollet

#print axioms Chollet.laplacian_principal_pivot_of_inducedBipartite
