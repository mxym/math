import HydrologyTree.GraphLeakCut
import HydrologyTree.ChildMatrix
import HydrologyTree.ArrowCharacteristic
import HydrologyTree.GraphModelInjectivity

/-! Arbitrary real matrices supported on an actual tree, without any conservation
or sign premise. Principal children inherit the exact graph support. This permits
reverse realization arguments without assuming positivity of the competitor. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

abbrev TreeMatrix (n : ℕ) := Matrix (Fin (n+1)) (Fin (n+1)) ℝ

def HasTreeMatrixSupport {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n) : Prop :=
  ∀ u v, u ≠ v → ¬(orderedTreeGraph t).Adj u v → A u v=0

lemma orderedGraph_adj_parent_iff {n : ℕ} (t : OrderedTree n) (u v : Fin (n+1)) :
    (orderedTreeGraph t).Adj u v ↔
      (v ≠ 0 ∧ parentVertex t v=u) ∨ (u ≠ 0 ∧ parentVertex t u=v) := by
  constructor
  · rintro ⟨e,⟨hp,hc⟩ | ⟨hp,hc⟩⟩
    · subst v
      exact Or.inl ⟨Fin.succ_ne_zero e,hp.symm⟩
    · subst u
      exact Or.inr ⟨Fin.succ_ne_zero e,hp.symm⟩
  · rintro (⟨hv,hp⟩ | ⟨hu,hp⟩)
    · refine ⟨v.pred hv,Or.inl ⟨?_,(Fin.succ_pred v hv).symm⟩⟩
      have he : parentVertex t v=t.parent (v.pred hv) := by
        conv_lhs => rw [← Fin.succ_pred v hv]
        rfl
      exact hp.symm.trans he
    · refine ⟨u.pred hu,Or.inr ⟨?_,(Fin.succ_pred u hu).symm⟩⟩
      have he : parentVertex t u=t.parent (u.pred hu) := by
        conv_lhs => rw [← Fin.succ_pred u hu]
        rfl
      exact hp.symm.trans he

lemma childGraph_adj_iff {n : ℕ} (t : OrderedTree n) (c : RootChild t)
    (i j : Fin (childEdgeCount t c+1)) :
    (orderedTreeGraph t).Adj (childEnumeration t c i).val (childEnumeration t c j).val ↔
      (orderedTreeGraph (childTree t c)).Adj i j := by
  rw [orderedGraph_adj_parent_iff,orderedGraph_adj_parent_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ((childParent_eq_iff t c i j).mp h.2)
    · exact Or.inr ((childParent_eq_iff t c j i).mp h.2)
  · rintro (h | h)
    · exact Or.inl ⟨branchVertex_ne_zero t c _,(childParent_eq_iff t c i j).mpr h⟩
    · exact Or.inr ⟨branchVertex_ne_zero t c _,(childParent_eq_iff t c j i).mpr h⟩

def supportedChildMatrix {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n) (c : RootChild t) :
    TreeMatrix (childEdgeCount t c) :=
  A.submatrix (fun i => (childEnumeration t c i).val) (fun i => (childEnumeration t c i).val)

lemma supportedChild_support {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) (c : RootChild t) :
    HasTreeMatrixSupport (childTree t c) (supportedChildMatrix t A c) := by
  intro i j hij hn
  apply hA
  · exact fun h => hij (childEnumeration_injective t c h)
  · exact fun h => hn ((childGraph_adj_iff t c i j).mp h)

lemma supportedMatrix_cross_branch {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) (c d : RootChild t) (hcd : c ≠ d)
    (i : Fin (childEdgeCount t c+1)) (j : Fin (childEdgeCount t d+1)) :
    A (childEnumeration t c i).val (childEnumeration t d j).val=0 := by
  have hb : rootBranchVertex t (childEnumeration t c i).val ≠
      rootBranchVertex t (childEnumeration t d j).val := by
    rw [(childEnumeration t c i).property,(childEnumeration t d j).property]
    exact fun h => hcd (Subtype.ext h)
  apply hA
  · exact fun h => hb (congrArg (rootBranchVertex t) h)
  · intro h
    exact hb (orderedGraph_nonroot_same_branch t _ _
      (branchVertex_ne_zero t c _) (branchVertex_ne_zero t d _) h)

lemma supportedMatrix_root_row {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) (c : RootChild t) (i : Fin (childEdgeCount t c+1)) :
    A 0 (childEnumeration t c i).val=if i=0 then A 0 c.val else 0 := by
  by_cases hi : i=0
  · subst i
    simp [childEnumeration_zero,branchRootVertex]
  · rw [if_neg hi]
    apply hA
    · exact Ne.symm (branchVertex_ne_zero t c _)
    · intro h
      have hh := orderedGraph_root_adj t _ h
      have he := rootBranchVertex_child t _ hh.1 hh.2
      rw [(childEnumeration t c i).property] at he
      have hv : (childEnumeration t c i).val=(childEnumeration t c 0).val := by
        simpa [childEnumeration_zero,branchRootVertex] using he.symm
      exact hi (childEnumeration_injective t c hv)

lemma supportedMatrix_root_column {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) (c : RootChild t) (i : Fin (childEdgeCount t c+1)) :
    A (childEnumeration t c i).val 0=if i=0 then A c.val 0 else 0 := by
  have ht : HasTreeMatrixSupport t A.transpose := by
    intro u v huv hn
    exact hA v u (Ne.symm huv) (fun h => hn h.symm)
  exact supportedMatrix_root_row t A.transpose ht c i

/-- Exact arrow decomposition of any actual tree-supported matrix, in the
canonical smaller-child numbering. Conservation is not a hypothesis. -/
theorem supportedMatrix_arrow {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (hA : HasTreeMatrixSupport t A) :
    A.submatrix (numberedRootEquiv t) (numberedRootEquiv t)=
      arrowMatrix (A 0 0) (supportedChildMatrix t A) (fun _ => 0)
        (fun c => A 0 c.val) (fun c => A c.val 0) := by
  ext u v
  rcases u with u | ⟨c,u⟩ <;> rcases v with v | ⟨d,v⟩
  · cases u; cases v; rfl
  · cases u
    change A 0 (childEnumeration t d v).val=if v=0 then A 0 d.val else 0
    exact supportedMatrix_root_row t A hA d v
  · cases v
    change A (childEnumeration t c u).val 0=if u=0 then A c.val 0 else 0
    exact supportedMatrix_root_column t A hA c u
  · by_cases h : c=d
    · subst d
      change A (childEnumeration t c u).val (childEnumeration t c v).val=
        Matrix.blockDiagonal' (supportedChildMatrix t A) ⟨c,u⟩ ⟨c,v⟩
      rw [Matrix.blockDiagonal'_apply_eq]
      rfl
    · change A (childEnumeration t c u).val (childEnumeration t d v).val=
        Matrix.blockDiagonal' (supportedChildMatrix t A) ⟨c,u⟩ ⟨d,v⟩
      rw [Matrix.blockDiagonal'_apply_ne (supportedChildMatrix t A) u v h]
      exact supportedMatrix_cross_branch t A hA c d h u v

/-- Actual physical matrices are members of the broader support class. -/
theorem compartmentMatrix_tree_support {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    HasTreeMatrixSupport t (compartmentMatrix t x) := by
  intro u v huv hn
  rw [compartment_offdiag_formula t x u v huv]
  apply Finset.sum_eq_zero
  intro e _
  have h1 : ¬(t.parent e=u ∧ e.succ=v) := by
    rintro ⟨h1,h2⟩
    exact hn ⟨e,Or.inl ⟨h1.symm,h2.symm⟩⟩
  have h2 : ¬(e.succ=u ∧ t.parent e=v) := by
    rintro ⟨h1,h2⟩
    exact hn ⟨e,Or.inr ⟨h2.symm,h1.symm⟩⟩
  simp [h1,h2]

/-- The generic principal child agrees with the established physical child
matrix, with its original exit-to-parent diagonal unchanged. -/
lemma supportedChild_physical {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t) :
    supportedChildMatrix t (compartmentMatrix t x) c=compartmentMatrix (childTree t c) (childRates t c x) := by
  exact physicalBranch_eq_childTree t c x

end HydrologyTree
