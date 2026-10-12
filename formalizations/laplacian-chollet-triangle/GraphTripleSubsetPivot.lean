import GraphTriplePivot
import PermanentPivotReindex
import InducedGraphPivot
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

namespace Chollet

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 5000000

/-- The singleton permanent pivot inequality, for ANY chosen vertex of
ANY 3-element principal Laplacian block inside an arbitrarily large
finite graph. The matrix is the genuine Mathlib Laplacian, with original
ambient degrees, even if the induced triple is a nonbipartite triangle. -/
theorem laplacian_principal_pivot_card_three
    (S : Finset V) (hcard : S.card = 3)
    (root : {v : V // v ∈ S}) :
    (G.lapMatrix ℝ) root.val root.val *
      Matrix.permanent (principalExcept
        (fun i j : {v : V // v ∈ S} =>
          (G.lapMatrix ℝ) i.val j.val) root) ≤
      Matrix.permanent (fun i j : {v : V // v ∈ S} =>
        (G.lapMatrix ℝ) i.val j.val) := by
  classical
  let I := {v : V // v ∈ S}
  let e0 : Fin 3 ≃ I := Fintype.equivOfCardEq (by
    change 3 = Fintype.card {v : V // v ∈ S}
    rw [Fintype.card_coe]
    exact hcard.symm)
  let k : Fin 3 := e0.symm root
  let ρ : Fin 3 ≃ Fin 3 := Equiv.swap 0 k
  let e : Fin 3 ≃ I := ρ.trans e0
  have he : e 0 = root := by
    change e0 (Equiv.swap (0 : Fin 3) k 0) = root
    rw [Equiv.swap_apply_left]
    exact e0.apply_symm_apply root
  let u : V := (e 0).val
  let v : V := (e 1).val
  let w : V := (e 2).val
  have huv : u ≠ v := by
    intro h
    have heq : (0 : Fin 3) = 1 := e.injective (Subtype.ext h)
    norm_num at heq
  have huw : u ≠ w := by
    intro h
    have heq : (0 : Fin 3) = 2 := e.injective (Subtype.ext h)
    norm_num at heq
  have hvw : v ≠ w := by
    intro h
    have heq : (1 : Fin 3) = 2 := e.injective (Subtype.ext h)
    norm_num at heq
  let A : Matrix I I ℝ :=
    fun i j => (G.lapMatrix ℝ) i.val j.val
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j => A (e i) (e j)
  have hM : M = orderedTripleMatrix G u v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hroot : e.symm root = 0 := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact he.symm
  have hPivotM :
      M 0 0 * Matrix.permanent (principalExcept M (0 : Fin 3)) ≤
        Matrix.permanent M := by
    rw [hM]
    exact orderedTripleMatrix_zero_pivot G u v w huv huw hvw
  have hPivotA :
      (fun i j : I => M (e.symm i) (e.symm j)) root root *
        Matrix.permanent
          (principalExcept (fun i j : I => M (e.symm i) (e.symm j))
            root) ≤
      Matrix.permanent (fun i j : I => M (e.symm i) (e.symm j)) :=
    permanent_rootPivot_reindex M e.symm root (by
      rw [hroot]
      exact hPivotM)
  have hMA : (fun i j : I => M (e.symm i) (e.symm j)) = A := by
    ext i j
    dsimp [M,A]
    simp
  rw [hMA] at hPivotA
  exact hPivotA


/-- ALL original-degree principal Laplacian blocks of cardinality at most
three, inside an arbitrary finite simple graph, satisfy the singleton
permanent-pivot bound at EACH chosen vertex. No bipartiteness assumption
on the ambient graph. -/
theorem laplacian_principal_pivot_card_le_three
    (S : Finset V) (hcard : S.card ≤ 3)
    (root : {v : V // v ∈ S}) :
    (G.lapMatrix ℝ) root.val root.val *
      Matrix.permanent (principalExcept
        (fun i j : {v : V // v ∈ S} =>
          (G.lapMatrix ℝ) i.val j.val) root) ≤
      Matrix.permanent (fun i j : {v : V // v ∈ S} =>
        (G.lapMatrix ℝ) i.val j.val) := by
  classical
  by_cases hsmall : S.card ≤ 2
  · have hsub : Fintype.card {v : V // v ∈ S} ≤ 2 := by
      simpa [Fintype.card_coe] using hsmall
    have hbip : (G.induce (S : Set V)).IsBipartite :=
      SimpleGraph.Colorable.mono hsub
        ((G.induce (S : Set V)).colorable_of_fintype)
    exact laplacian_principal_pivot_of_inducedBipartite G S hbip root
  · have hthree : S.card = 3 := by omega
    exact laplacian_principal_pivot_card_three G S hthree root

end Chollet

#print axioms Chollet.laplacian_principal_pivot_card_three
#print axioms Chollet.laplacian_principal_pivot_card_le_three
