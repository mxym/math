import HydrologyTree.ChildTree
import HydrologyTree.MatrixEntries

/-! Rate extraction preserves the actual exit-to-parent rate as the child's
single leak. All constructions are defined for every real rate vector. -/
noncomputable section
namespace HydrologyTree

/-- Pull back inward rates (including the new root leak) and internal outward rates. -/
def childRates {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n) :
    TreeRates (childEdgeCount t c) :=
  (fun i => x.1 (childEnumeration t c i).val,
    fun i => outwardByVertex x.2 (childEnumeration t c i.succ).val)

@[simp] theorem childRates_leak {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n) :
    (childRates t c x).1 0 = x.1 c.val := by
  simp [childRates, branchRootVertex]

lemma childEnumeration_injective {n : ℕ} (t : OrderedTree n) (c : RootChild t) :
    Function.Injective (fun i => (childEnumeration t c i).val) := by
  intro i j h
  exact (childEnumeration t c).injective (Subtype.ext h)

lemma childParent_eq_iff {n : ℕ} (t : OrderedTree n) (c : RootChild t)
    (i j : Fin (childEdgeCount t c + 1)) :
    parentVertex t (childEnumeration t c j).val = (childEnumeration t c i).val ↔
      j ≠ 0 ∧ parentVertex (childTree t c) j = i := by
  refine Fin.cases ?_ (fun e => ?_) j
  · rw [childEnumeration_zero]
    have h : parentVertex t (branchRootVertex t c).val = 0 := c.property.2
    rw [h]
    simp only [ne_eq, not_true_eq_false, false_and, iff_false]
    exact Ne.symm (branchVertex_ne_zero t c (childEnumeration t c i))
  · rw [← childTree_parent_transport t c e]
    constructor
    · intro h
      exact ⟨Fin.succ_ne_zero e, childEnumeration_injective t c h⟩
    · intro h
      exact congrArg (fun k => (childEnumeration t c k).val) h.2

lemma childRates_outward {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n)
    (i : Fin (childEdgeCount t c + 1)) (hi : i ≠ 0) :
    outwardByVertex (childRates t c x).2 i = outwardByVertex x.2 (childEnumeration t c i).val := by
  revert hi
  refine Fin.cases ?_ (fun e _ => ?_) i
  · intro h; exact False.elim (h rfl)
  · rfl

/-- Every off-diagonal entry of a child generator equals its original principal-block entry. -/
theorem childMatrix_offdiag {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n)
    (i j : Fin (childEdgeCount t c+1)) (hij : i ≠ j) :
    compartmentMatrix (childTree t c) (childRates t c x) i j =
      compartmentMatrix t x (childEnumeration t c i).val (childEnumeration t c j).val := by
  have hne : (childEnumeration t c i).val ≠ (childEnumeration t c j).val :=
    fun h => hij (childEnumeration_injective t c h)
  rw [compartment_offdiag_parent_formula _ _ _ _ hij,
    compartment_offdiag_parent_formula _ _ _ _ hne]
  have hi := branchVertex_ne_zero t c (childEnumeration t c i)
  have hj := branchVertex_ne_zero t c (childEnumeration t c j)
  simp only [ite_eq_right hi, ite_eq_right hj, childParent_eq_iff]
  by_cases h0 : i = 0 <;> by_cases h1 : j = 0
  all_goals simp only [h0, h1, ne_eq, not_true_eq_false, false_and,
    not_false_eq_true, true_and, ite_true, ite_false]
  all_goals try rfl
  all_goals rw [childRates_outward t c x _ h0]
  all_goals rfl

end HydrologyTree
