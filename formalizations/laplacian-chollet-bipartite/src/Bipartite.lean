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

private theorem lapMatrix_switch_nonneg (s : V → ℝ)
    (hs : ∀ i, (s i)^2 = 1)
    (hsadj : ∀ i j, G.Adj i j → s i * s j = -1)
    (i j : V) :
    0 ≤ signedSwitch (G.lapMatrix ℝ) s i j := by
  change 0 ≤ s i * (G.lapMatrix ℝ) i j * s j
  rw [lapMatrix_entry]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hdeg : 0 ≤ (G.degree i : ℝ) := Nat.cast_nonneg _
    have heq : s i * (G.degree i : ℝ) * s i = (G.degree i : ℝ) := by
      calc
        _ = (s i)^2 * (G.degree i : ℝ) := by ring
        _ = _ := by rw [hs i]; ring
    rw [heq]
    exact hdeg
  · simp only [if_neg hij]
    by_cases hadj : G.Adj i j
    · simp only [if_pos hadj]
      have h := hsadj i j hadj
      nlinarith
    · simp [hadj]

theorem laplacian_sign_switch_strong (s : V → ℝ)
    (hs : ∀ i, (s i)^2 = 1)
    (hsadj : ∀ i j, G.Adj i j → s i * s j = -1) :
    ∀ S : Finset V,
      Matrix.permanent
        (fun i j : {v : V // v ∈ S} =>
           (G.lapMatrix ℝ) i.val j.val *
           (G.lapMatrix ℝ) i.val j.val)
      ≤
      Matrix.permanent
        (fun i j : {v : V // v ∈ S} => (G.lapMatrix ℝ) i.val j.val) *
        (∏ i : {v : V // v ∈ S}, (G.degree i.val : ℝ)) := by
  classical
  intro S
  let A : Matrix {v : V // v ∈ S} {v : V // v ∈ S} ℝ :=
    fun i j => (G.lapMatrix ℝ) i.val j.val
  let t : {v : V // v ∈ S} → ℝ := fun i => s i.val
  have ht : ∀ i, (t i)^2 = 1 := fun i => hs i.val
  have hnonneg : ∀ i j, 0 ≤ signedSwitch A t i j := by
    intro i j
    exact lapMatrix_switch_nonneg G s hs hsadj i.val j.val
  have hminor : ∀ i j, (A i j)^2 ≤ A i i * A j j :=
    fun i j => lapMatrix_pair_bound G i.val j.val
  have h := sign_switch_permanent_hadamard_bound A t ht hnonneg hminor
  have hdiag : (∏ i : {v : V // v ∈ S}, (G.lapMatrix ℝ) i.val i.val) =
      ∏ i : {v : V // v ∈ S}, (G.degree i.val : ℝ) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [lapMatrix_entry]
    simp
  change (Matrix.permanent (fun i j => A i j * A i j)) ≤
    Matrix.permanent A * (∏ i : {v : V // v ∈ S}, (G.degree i.val : ℝ))
  simpa only [A, hdiag] using h


/-- The genuine graph-level strong Chollet inequality for every finite bipartite
simple graph, uniformly for all principal submatrices. -/
theorem strong_chollet_of_bipartite (hG : G.IsBipartite) :
    ∀ S : Finset V,
      Matrix.permanent
        (fun i j : {v : V // v ∈ S} =>
           (G.lapMatrix ℝ) i.val j.val *
           (G.lapMatrix ℝ) i.val j.val)
      ≤
      Matrix.permanent
        (fun i j : {v : V // v ∈ S} => (G.lapMatrix ℝ) i.val j.val) *
        (∏ i : {v : V // v ∈ S}, (G.degree i.val : ℝ)) := by
  classical
  obtain ⟨left, right, hpart⟩ := hG.exists_isBipartiteWith
  let sign : V → ℝ := fun v => if v ∈ left then 1 else -1
  have hs : ∀ v, (sign v)^2 = 1 := by
    intro v
    by_cases hv : v ∈ left <;> simp [sign, hv]
  have hsadj : ∀ i j, G.Adj i j → sign i * sign j = -1 := by
    intro i j hij
    rcases hpart.mem_of_adj hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hnj : j ∉ left := hpart.disjoint.subset_compl_left hj
      simp [sign, hi, hnj]
    · have hni : i ∉ left := hpart.disjoint.subset_compl_left hi
      simp [sign, hni, hj]
  exact laplacian_sign_switch_strong G sign hs hsadj

end Chollet
