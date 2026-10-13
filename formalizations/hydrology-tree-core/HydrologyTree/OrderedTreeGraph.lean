import HydrologyTree.PhysicalBridge
import HydrologyTree.LeafRecursion
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Actual simple graph and exact last-leaf attachment of a parent tree. -/
noncomputable section
namespace HydrologyTree

def orderedTreeGraph {n : ℕ} (t : OrderedTree n) : SimpleGraph (Fin (n+1)) where
  Adj u v := ∃ e : Fin n,
    (u=t.parent e ∧ v=e.succ) ∨ (v=t.parent e ∧ u=e.succ)
  symm := by
    constructor
    rintro u v ⟨e,h⟩
    exact ⟨e,h.symm⟩
  loopless := by
    constructor
    rintro u ⟨e,h⟩
    rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
      exact parent_ne_child t e (h1.symm.trans h2)

def appendLeafTree {n : ℕ} (t : OrderedTree n) (p : Fin (n+1)) : OrderedTree (n+1) where
  parent := Fin.lastCases p.castSucc (fun e : Fin n => (t.parent e).castSucc)
  parent_le := by
    intro e
    refine Fin.lastCases ?_ (fun j => ?_) e
    · simpa using Nat.le_of_lt_succ p.isLt
    · simpa using t.parent_le j

@[simp] lemma appendLeaf_parent_old {n : ℕ} (t : OrderedTree n) (p : Fin (n+1)) (e : Fin n) :
    (appendLeafTree t p).parent e.castSucc=(t.parent e).castSucc := by simp [appendLeafTree]

@[simp] lemma appendLeaf_parent_last {n : ℕ} (t : OrderedTree n) (p : Fin (n+1)) :
    (appendLeafTree t p).parent (Fin.last n)=p.castSucc := by simp [appendLeafTree]

lemma graph_edge_child_castSucc {n : ℕ} (e : Fin n) : e.castSucc.succ=e.succ.castSucc := rfl
lemma graph_edge_child_last (n : ℕ) : (Fin.last n).succ=Fin.last (n+1) := rfl

theorem orderedTreeGraph_append_old {n : ℕ} (t : OrderedTree n) (p u v : Fin (n+1)) :
    (orderedTreeGraph (appendLeafTree t p)).Adj u.castSucc v.castSucc ↔
      (orderedTreeGraph t).Adj u v := by
  constructor
  · rintro ⟨e,he⟩
    revert he
    refine Fin.lastCases ?_ (fun j => ?_) e
    · intro he
      simp only [appendLeaf_parent_last,graph_edge_child_last] at he
      rcases he with ⟨_,h⟩ | ⟨_,h⟩
      · exact False.elim (Fin.castSucc_ne_last v h)
      · exact False.elim (Fin.castSucc_ne_last u h)
    · intro he
      refine ⟨j,?_⟩
      simpa only [appendLeaf_parent_old,graph_edge_child_castSucc,Fin.castSucc_inj] using he
  · rintro ⟨e,he⟩
    refine ⟨e.castSucc,?_⟩
    simpa only [appendLeaf_parent_old,graph_edge_child_castSucc,Fin.castSucc_inj] using he

theorem orderedTreeGraph_append_last {n : ℕ} (t : OrderedTree n) (p u : Fin (n+1)) :
    (orderedTreeGraph (appendLeafTree t p)).Adj u.castSucc (Fin.last (n+1)) ↔ u=p := by
  constructor
  · rintro ⟨e,he⟩
    revert he
    refine Fin.lastCases ?_ (fun j => ?_) e
    · intro he
      simp only [appendLeaf_parent_last,graph_edge_child_last] at he
      rcases he with ⟨h,_⟩ | ⟨h,_⟩
      · exact Fin.castSucc_injective _ h
      · exact False.elim (Fin.castSucc_ne_last p h.symm)
    · intro he
      simp only [appendLeaf_parent_old,graph_edge_child_castSucc] at he
      rcases he with ⟨_,h⟩ | ⟨h,_⟩
      · exact False.elim (Fin.castSucc_ne_last j.succ h.symm)
      · exact False.elim (Fin.castSucc_ne_last (t.parent j) h.symm)
  · intro h
    subst u
    exact ⟨Fin.last n,Or.inl ⟨by simp,graph_edge_child_last n |>.symm⟩⟩

def appendLeafEnumeration {V : Type*} [DecidableEq V] {n : ℕ} (l : V)
    (e : Fin (n+1) ≃ {v : V // v ≠ l}) : Fin (n+2) ≃ V where
  toFun := Fin.lastCases l (fun i => (e i).val)
  invFun v := if h : v=l then Fin.last (n+1) else (e.symm ⟨v,h⟩).castSucc
  left_inv i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [(e j).property]
  right_inv v := by
    by_cases h : v=l
    · subst v
      simp
    · simp [h]

@[simp] lemma appendLeafEnumeration_old {V : Type*} [DecidableEq V] {n : ℕ}
    (l : V) (e : Fin (n+1) ≃ {v : V // v ≠ l}) (i : Fin (n+1)) :
    appendLeafEnumeration l e i.castSucc=(e i).val := by simp [appendLeafEnumeration]

@[simp] lemma appendLeafEnumeration_last {V : Type*} [DecidableEq V] {n : ℕ}
    (l : V) (e : Fin (n+1) ≃ {v : V // v ≠ l}) :
    appendLeafEnumeration l e (Fin.last (n+1))=l := by simp [appendLeafEnumeration]

end HydrologyTree
