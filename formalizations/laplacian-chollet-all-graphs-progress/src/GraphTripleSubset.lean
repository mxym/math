import GraphTriple
import Reindex
import Target
import Induced

namespace Chollet

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The exact graph strong-Chollet principal inequality holds for EVERY
three-element vertex subset of an arbitrary finite ambient graph. -/
theorem strong_chollet_principal_card_three (S : Finset V)
    (hcard : S.card = 3) :
    Matrix.permanent
        (fun i j : {v : V // v ∈ S} =>
          (G.lapMatrix ℝ) i.val j.val * (G.lapMatrix ℝ) i.val j.val)
      ≤ Matrix.permanent
          (fun i j : {v : V // v ∈ S} => (G.lapMatrix ℝ) i.val j.val) *
        (∏ i : {v : V // v ∈ S}, (G.degree i.val : ℝ)) := by
  classical
  let e : Fin 3 ≃ {v : V // v ∈ S} :=
    Fintype.equivOfCardEq (by simp [Fintype.card_coe, hcard])
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

  let A : Matrix {v : V // v ∈ S} {v : V // v ∈ S} ℝ :=
    fun i j => (G.lapMatrix ℝ) i.val j.val
  have hA : (fun i j : Fin 3 => A (e i) (e j)) =
      orderedTripleMatrix G u v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hper :
      Matrix.permanent (fun i j : Fin 3 => A (e i) (e j)) =
      Matrix.permanent A := permanent_reindex_equiv A e
  have hsquare :
      Matrix.permanent (fun i j : Fin 3 =>
          A (e i) (e j) * A (e i) (e j)) =
      Matrix.permanent (fun i j => A i j * A i j) :=
    permanent_reindex_equiv (fun i j => A i j * A i j) e
  have hprod :
      (∏ i : Fin 3, (G.degree (e i).val : ℝ)) =
      (∏ i : {v : V // v ∈ S}, (G.degree i.val : ℝ)) :=
    Equiv.prod_comp e (fun i => (G.degree i.val : ℝ))
  have hthree :
      (∏ i : Fin 3, (G.degree (e i).val : ℝ)) =
        (G.degree u : ℝ) * (G.degree v : ℝ) * (G.degree w : ℝ) := by
    simp [Fin.prod_univ_succ, u, v, w, mul_assoc]
  have h := orderedTripleMatrix_strong G u v w huv huw hvw
  rw [← hA] at h
  rw [← hthree] at h
  rw [hsquare, hper, hprod] at h
  change Matrix.permanent (fun i j => A i j * A i j) ≤
    Matrix.permanent A * (∏ i : {v : V // v ∈ S}, (G.degree i.val : ℝ))
  exact h


/-- Uniform local theorem in ARBITRARY finite simple graphs: every
principal Laplacian with at most three vertices satisfies strong Chollet. -/
theorem strong_chollet_principal_card_le_three (S : Finset V)
    (hcard : S.card ≤ 3) :
    Matrix.permanent
        (fun i j : {v : V // v ∈ S} =>
          (G.lapMatrix ℝ) i.val j.val * (G.lapMatrix ℝ) i.val j.val)
      ≤ Matrix.permanent
          (fun i j : {v : V // v ∈ S} => (G.lapMatrix ℝ) i.val j.val) *
        (∏ i : {v : V // v ∈ S}, (G.degree i.val : ℝ)) := by
  by_cases hsmall : S.card ≤ 2
  · have hsub : Fintype.card {v : V // v ∈ S} ≤ 2 := by
      simpa [Fintype.card_coe] using hsmall
    have hbip : (G.induce (S : Set V)).IsBipartite :=
      SimpleGraph.Colorable.mono hsub
        ((G.induce (S : Set V)).colorable_of_fintype)
    exact strong_chollet_principal_of_induced_bipartite G S hbip
  · have hthree : S.card = 3 := by omega
    exact strong_chollet_principal_card_three G S hthree

end Chollet

#print axioms Chollet.strong_chollet_principal_card_three
#print axioms Chollet.strong_chollet_principal_card_le_three
