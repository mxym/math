import HydrologyTree.OrderedTreeGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Every independently presented finite rooted simple tree admits an exact
root-preserving parent presentation. No numbering hypothesis is assumed. -/
noncomputable section
namespace HydrologyTree

structure RootedTreePresentation {V : Type*} (n : ℕ) (G : SimpleGraph V) (o : V) where
  tree : OrderedTree n
  vertices : Fin (n+1) ≃ V
  root_eq : vertices 0=o
  adj_iff : ∀ i j, (orderedTreeGraph tree).Adj i j ↔ G.Adj (vertices i) (vertices j)

lemma finite_tree_nonroot_leaf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (o : V) (hcard : 1 < Fintype.card V) :
    ∃ l : V, l ≠ o ∧ G.degree l=1 := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨u,v,hne,hu,hv⟩ := hG.exists_ne_and_degree_eq_one
  by_cases h : u=o
  · refine ⟨v,?_,hv⟩
    intro he
    exact hne (h.trans he.symm)
  · exact ⟨u,h,hu⟩

/-- Structural existence for every size, including the singleton. -/
theorem finite_rooted_tree_presentation (n : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (o : V) (hG : G.IsTree) (hN : Fintype.card V=n+1) :
    Nonempty (RootedTreePresentation n G o) := by
  classical
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      letI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      let e : Fin 1 ≃ V :=
        { toFun := fun _ => o
          invFun := fun _ => 0
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _ }
      let t : OrderedTree 0 := ⟨Fin.elim0,fun i => Fin.elim0 i⟩
      refine ⟨⟨t,e,rfl,?_⟩⟩
      intro i j
      have hij : i=j := by apply Fin.ext; omega
      subst j
      simp
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      obtain ⟨l,hlo,hldeg⟩ := finite_tree_nonroot_leaf G hG o (by omega)
      let W := {v : V // v ≠ l}
      let H : SimpleGraph W := G.induce {v | v ≠ l}
      let root : W := ⟨o,Ne.symm hlo⟩
      have hW : Fintype.card W=k+1 := by
        have hh := Fintype.card_congr (deleteVertexEquiv l)
        have hunit : Fintype.card Unit=1 := by simp
        rw [Fintype.card_sum,hunit,hN] at hh
        change Fintype.card W+1=k+1+1 at hh
        omega
      have hH : H.IsTree := by
        refine ⟨?_,hG.isAcyclic.induce _⟩
        simpa only [H,Set.compl_singleton_eq] using
          hG.connected.induce_compl_singleton_of_degree_eq_one hldeg
      obtain ⟨p0⟩ := ih k (Nat.lt_succ_self k) H root hH hW
      obtain ⟨v,hv,hvuniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hldeg
      have hvl : v ≠ l := by
        intro h
        subst v
        exact G.irrefl hv
      let vp : W := ⟨v,hvl⟩
      let q : Fin (k+1) := p0.vertices.symm vp
      let t := appendLeafTree p0.tree q
      let e := appendLeafEnumeration l p0.vertices
      have hroot : e 0=o := by
        change appendLeafEnumeration l p0.vertices (0 : Fin (k+1)).castSucc=o
        rw [appendLeafEnumeration_old]
        exact congrArg Subtype.val p0.root_eq
      have hleaf (i : Fin (k+1)) : G.Adj (p0.vertices i).val l ↔ i=q := by
        constructor
        · intro hi
          apply p0.vertices.injective
          rw [Equiv.apply_symm_apply]
          apply Subtype.ext
          exact hvuniq _ hi.symm
        · intro hi
          subst i
          change G.Adj (p0.vertices (p0.vertices.symm vp)).val l
          rw [Equiv.apply_symm_apply]
          exact hv.symm
      refine ⟨⟨t,e,hroot,?_⟩⟩
      intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simp
        · simp only [t,e,appendLeafEnumeration_last,appendLeafEnumeration_old]
          change (orderedTreeGraph (appendLeafTree p0.tree q)).Adj (Fin.last (k+1)) j.castSucc ↔
            G.Adj l (p0.vertices j).val
          constructor
          · intro h
            exact ((hleaf j).mpr ((orderedTreeGraph_append_last p0.tree q j).mp h.symm)).symm
          · intro h
            exact ((orderedTreeGraph_append_last p0.tree q j).mpr ((hleaf j).mp h.symm)).symm
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · simp only [t,e,appendLeafEnumeration_last,appendLeafEnumeration_old]
          change (orderedTreeGraph (appendLeafTree p0.tree q)).Adj i.castSucc (Fin.last (k+1)) ↔
            G.Adj (p0.vertices i).val l
          exact (orderedTreeGraph_append_last p0.tree q i).trans (hleaf i).symm
        · simp only [t,e,appendLeafEnumeration_last,appendLeafEnumeration_old]
          change (orderedTreeGraph (appendLeafTree p0.tree q)).Adj i.castSucc j.castSucc ↔
            G.Adj (p0.vertices i).val (p0.vertices j).val
          rw [orderedTreeGraph_append_old]
          exact p0.adj_iff i j

/-- A presentation constructed only from the original graph and designated root. -/
def finiteGraphPresentation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (o : V) :
    RootedTreePresentation (Fintype.card V-1) G o := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨o⟩
  exact Classical.choice (finite_rooted_tree_presentation (Fintype.card V-1) G o hG (by omega))

end HydrologyTree
