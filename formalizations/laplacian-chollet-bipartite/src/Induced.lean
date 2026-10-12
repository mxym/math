import Signed
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Chollet

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem lapMatrix_entry (i j : V) :
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

private theorem lapMatrix_pair_bound (i j : V) :
    ((G.lapMatrix ℝ) i j)^2 ≤
      (G.lapMatrix ℝ) i i * (G.lapMatrix ℝ) j j := by
  have hi : (G.lapMatrix ℝ) i i = (G.degree i : ℝ) := by
    rw [lapMatrix_entry]; simp
  have hj : (G.lapMatrix ℝ) j j = (G.degree j : ℝ) := by
    rw [lapMatrix_entry]; simp
  rw [hi, hj]
  rw [lapMatrix_entry]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    rw [pow_two]
  · simp only [hij, ↓reduceIte]
    by_cases hadj : G.Adj i j
    · simp only [hadj, ↓reduceIte]
      have hpi : 0 < G.degree i := hadj.degree_pos_left
      have hpj : 0 < G.degree j := hadj.symm.degree_pos_left
      have hpi' : (1 : ℝ) ≤ (G.degree i : ℝ) := by
        exact_mod_cast hpi
      have hpj' : (1 : ℝ) ≤ (G.degree j : ℝ) := by
        exact_mod_cast hpj
      nlinarith [mul_nonneg (sub_nonneg.mpr hpi') (sub_nonneg.mpr hpj')]
    · simp only [hadj, ↓reduceIte]
      simpa using mul_nonneg
        (show (0:ℝ) ≤ (G.degree i : ℝ) from Nat.cast_nonneg _)
        (show (0:ℝ) ≤ (G.degree j : ℝ) from Nat.cast_nonneg _)


/-- Strong Chollet for a principal submatrix of an arbitrary finite graph whenever
the graph induced ON THAT SUBSET is bipartite. No bipartiteness of the ambient
graph is required, and diagonal entries keep their original G-degrees. -/
theorem strong_chollet_principal_of_induced_bipartite (S : Finset V)
    (hS : (G.induce (S : Set V)).IsBipartite) :
    Matrix.permanent
        (fun i j : {v : V // v ∈ S} =>
          (G.lapMatrix ℝ) i.val j.val * (G.lapMatrix ℝ) i.val j.val)
      ≤ Matrix.permanent
          (fun i j : {v : V // v ∈ S} => (G.lapMatrix ℝ) i.val j.val) *
        (∏ i : {v : V // v ∈ S}, (G.degree i.val : ℝ)) := by
  classical
  obtain ⟨left,right,hpart⟩ := hS.exists_isBipartiteWith
  let sign : {v : V // v ∈ S} → ℝ :=
    fun i => if i ∈ left then 1 else -1
  have hs : ∀ i, (sign i)^2 = 1 := by
    intro i
    by_cases hi : i ∈ left <;> simp [sign,hi]
  have hsadj : ∀ i j : {v : V // v ∈ S},
      G.Adj i.val j.val → sign i * sign j = -1 := by
    intro i j hij
    have hInduced : (G.induce (S : Set V)).Adj i j := hij
    rcases hpart.mem_of_adj hInduced with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · have hnj : j ∉ left := hpart.disjoint.subset_compl_left hj
      simp [sign,hi,hnj]
    · have hni : i ∉ left := hpart.disjoint.subset_compl_left hi
      simp [sign,hni,hj]
  let A : Matrix {v : V // v ∈ S} {v : V // v ∈ S} ℝ :=
    fun i j => (G.lapMatrix ℝ) i.val j.val
  have hn : ∀ i j, 0 ≤ signedSwitch A sign i j := by
    intro i j
    change 0 ≤ sign i * (G.lapMatrix ℝ) i.val j.val * sign j
    rw [lapMatrix_entry G i.val j.val]
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
  have hminor : ∀ i j, (A i j)^2 ≤ A i i * A j j :=
    fun i j => lapMatrix_pair_bound G i.val j.val
  have h := sign_switch_permanent_hadamard_bound A sign hs hn hminor
  have hdiag :
      (∏ i : {v : V // v ∈ S}, (G.lapMatrix ℝ) i.val i.val) =
        ∏ i : {v : V // v ∈ S}, (G.degree i.val : ℝ) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [lapMatrix_entry]
    simp
  change (Matrix.permanent (fun i j => A i j * A i j)) ≤
    Matrix.permanent A * (∏ i : {v : V // v ∈ S}, (G.degree i.val : ℝ))
  simpa only [A,hdiag] using h

end Chollet

#print axioms Chollet.strong_chollet_principal_of_induced_bipartite
