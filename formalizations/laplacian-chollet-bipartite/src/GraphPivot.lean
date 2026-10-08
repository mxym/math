import SignSwitchPivot
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Chollet

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (G : SimpleGraph (Option α)) [DecidableRel G.Adj]

private theorem pivotLap_entry (i j : Option α) :
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

private theorem bipartite_lap_switch_nonneg (s : Option α → ℝ)
    (hs : ∀ i, (s i)^2 = 1)
    (hsadj : ∀ i j, G.Adj i j → s i * s j = -1)
    (i j : Option α) :
    0 ≤ signedSwitch (G.lapMatrix ℝ) s i j := by
  change 0 ≤ s i * (G.lapMatrix ℝ) i j * s j
  rw [pivotLap_entry]
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

/-- Genuine bipartite graph Laplacians satisfy the singleton Lieb-style
permanent lower bound directly, with no PSD block-permanent theorem. -/
theorem bipartite_laplacian_rootPivot (hG : G.IsBipartite) :
    (G.degree none : ℝ) *
      Matrix.permanent (fun i j : α =>
        (G.lapMatrix ℝ) (some i) (some j)) ≤
      Matrix.permanent (G.lapMatrix ℝ) := by
  classical
  obtain ⟨left,right,hpart⟩ := hG.exists_isBipartiteWith
  let sign : Option α → ℝ := fun i => if i ∈ left then 1 else -1
  have hs : ∀ i, (sign i)^2 = 1 := by
    intro i
    by_cases hi : i ∈ left <;> simp [sign,hi]
  have hsadj : ∀ i j, G.Adj i j → sign i * sign j = -1 := by
    intro i j hij
    rcases hpart.mem_of_adj hij with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · have hnj : j ∉ left := hpart.disjoint.subset_compl_left hj
      simp [sign, hi, hnj]
    · have hni : i ∉ left := hpart.disjoint.subset_compl_left hi
      simp [sign, hni, hj]
  have hn : ∀ i j, 0 ≤ signedSwitch (G.lapMatrix ℝ) sign i j := by
    intro i j
    exact bipartite_lap_switch_nonneg G sign hs hsadj i j
  have hp := permanent_optionPivot_of_signSwitch_nonnegative
      (G.lapMatrix ℝ) sign hs hn
  have hdiag : (G.lapMatrix ℝ) none none = (G.degree none : ℝ) := by
    rw [pivotLap_entry]
    simp
  simpa only [hdiag] using hp

end Chollet

#print axioms Chollet.bipartite_laplacian_rootPivot
