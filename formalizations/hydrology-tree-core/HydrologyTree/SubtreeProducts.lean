import HydrologyTree.AllTreeJacobian

/-! Flatten exact recursive factors onto the ORIGINAL finite vertex and edge
sets. Subtrees are the previously constructed actual principal child models. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- The number of vertices of the actual rooted principal subtree at vertex v. -/
def subtreeVertexCount {n : ℕ} (t : OrderedTree n) (v : Fin (n+1)) : ℕ :=
  match (numberedRootEquiv t).symm v with
  | .inl _ => n+1
  | .inr ⟨c,i⟩ => subtreeVertexCount (childTree t c) i
termination_by n
decreasing_by exact childEdgeCount_lt t c

@[simp] lemma subtreeVertexCount_root {n : ℕ} (t : OrderedTree n) :
    subtreeVertexCount t 0 = n+1 := by
  change subtreeVertexCount t (numberedRootEquiv t (.inl ())) = _
  rw [subtreeVertexCount,Equiv.symm_apply_apply]

@[simp] lemma subtreeVertexCount_child {n : ℕ} (t : OrderedTree n)
    (c : RootChild t) (i : Fin (childEdgeCount t c+1)) :
    subtreeVertexCount t (childEnumeration t c i).val = subtreeVertexCount (childTree t c) i := by
  change subtreeVertexCount t (numberedRootEquiv t (.inr ⟨c,i⟩)) = _
  rw [subtreeVertexCount,Equiv.symm_apply_apply]

lemma subtreeVertexCount_pos {n : ℕ} (t : OrderedTree n) (v : Fin (n+1)) :
    0 < subtreeVertexCount t v := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨u,rfl⟩ := (numberedRootEquiv t).surjective v
    rcases u with u | ⟨c,i⟩
    · cases u
      rw [numberedRootEquiv_zero,subtreeVertexCount_root]
      omega
    · rw [numberedRootEquiv_child,subtreeVertexCount_child]
      exact ih (childEdgeCount t c) (childEdgeCount_lt t c) (childTree t c) i

/-- Actual local quantity at the original vertex, via the proved child-principal transport. -/
def subtreeNodeValue {α : Type*}
    (f : {m : ℕ} → OrderedTree m → TreeRates m → α)
    {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (v : Fin (n+1)) : α :=
  match (numberedRootEquiv t).symm v with
  | .inl _ => f t x
  | .inr ⟨c,i⟩ => subtreeNodeValue f (childTree t c) (childRates t c x) i
termination_by n
decreasing_by exact childEdgeCount_lt t c

@[simp] lemma subtreeNodeValue_root {α : Type*}
    (f : {m : ℕ} → OrderedTree m → TreeRates m → α)
    {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : subtreeNodeValue f t x 0 = f t x := by
  change subtreeNodeValue f t x (numberedRootEquiv t (.inl ())) = _
  rw [subtreeNodeValue,Equiv.symm_apply_apply]

@[simp] lemma subtreeNodeValue_child {α : Type*}
    (f : {m : ℕ} → OrderedTree m → TreeRates m → α)
    {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t)
    (i : Fin (childEdgeCount t c+1)) :
    subtreeNodeValue f t x (childEnumeration t c i).val =
      subtreeNodeValue f (childTree t c) (childRates t c x) i := by
  change subtreeNodeValue f t x (numberedRootEquiv t (.inr ⟨c,i⟩)) = _
  rw [subtreeNodeValue,Equiv.symm_apply_apply]

lemma original_node_product_recursion {α : Type*} [CommMonoid α]
    (f : {m : ℕ} → OrderedTree m → TreeRates m → α)
    {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (∏ v : Fin (n+1), subtreeNodeValue f t x v) = f t x *
      ∏ c : RootChild t, ∏ i : Fin (childEdgeCount t c+1),
        subtreeNodeValue f (childTree t c) (childRates t c x) i := by
  rw [← (numberedRootEquiv t).prod_comp (fun v => subtreeNodeValue f t x v),Fintype.prod_sum_type]
  simp only [Fintype.prod_unique,Fintype.prod_sigma,numberedRootEquiv_zero,
    numberedRootEquiv_child,subtreeNodeValue_root,subtreeNodeValue_child]
  have hd : (default : Unit) = () := Subsingleton.elim _ _
  rw [hd,numberedRootEquiv_zero,subtreeNodeValue_root]

/-- The exact rate monomial, indexed by every original directed edge pair. -/
def originalTreeRateMonomial {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ :=
  ∏ e : Fin n, x.1 e.succ ^ subtreeVertexCount t e.succ *
    x.2 e ^ (subtreeVertexCount t e.succ-1)

lemma originalTreeRateMonomial_recursion {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    originalTreeRateMonomial t x = treeRootRateFactor t x *
      ∏ c : RootChild t, originalTreeRateMonomial (childTree t c) (childRates t c x) := by
  rw [originalTreeRateMonomial,← (numberedEdgeEquiv t).prod_comp,Fintype.prod_sigma,
    treeRootRateFactor,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c _
  have hs (i : Fin (childEdgeCount t c+1)) :
      (numberedEdgeEquiv t ⟨c,i⟩).succ = (childEnumeration t c i).val :=
    numberedEdgeIndex_succ t ⟨c,i⟩
  simp only [hs,outward_at_numbered_child]
  change (∏ i : Fin (childEdgeCount t c+1),
      x.1 (childEnumeration t c i).val ^ subtreeVertexCount t (childEnumeration t c i).val *
      outwardByVertex x.2 (childEnumeration t c i).val ^
        (subtreeVertexCount t (childEnumeration t c i).val-1)) = _
  simp only [subtreeVertexCount_child,Fin.prod_univ_succ,childEnumeration_zero,
    subtreeVertexCount_root,Nat.add_sub_cancel]
  congr 1

/-- Squared actual sibling-resultant factors at every original vertex. -/
def originalTreeSiblingProduct {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ :=
  ∏ v : Fin (n+1), subtreeNodeValue (fun {m} (s : OrderedTree m) y => treeSiblingResultant s y ^ 2) t x v

lemma originalTreeSiblingProduct_recursion {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    originalTreeSiblingProduct t x = treeSiblingResultant t x ^ 2 *
      ∏ c : RootChild t, originalTreeSiblingProduct (childTree t c) (childRates t c x) := by
  exact original_node_product_recursion _ t x

/-- The recursive factor is exactly the original-vertex rate/subtree formula. -/
theorem allTreeJacobianWeight_eq_original_products {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    allTreeJacobianWeight t x = originalTreeRateMonomial t x * originalTreeSiblingProduct t x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [allTreeJacobianWeight,originalTreeRateMonomial_recursion,originalTreeSiblingProduct_recursion]
    have he : (∏ c : RootChild t, allTreeJacobianWeight (childTree t c) (childRates t c x)) =
        (∏ c : RootChild t, originalTreeRateMonomial (childTree t c) (childRates t c x)) *
          (∏ c : RootChild t, originalTreeSiblingProduct (childTree t c) (childRates t c x)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun c _ => ih (childEdgeCount t c) (childEdgeCount_lt t c)
        (childTree t c) (childRates t c x))
    rw [he]
    ring

/-- Full all-size all-real-rate formula in ORIGINAL edge and vertex indices.
The fixed sign has been proved, including every zero-rate/repeated-root boundary. -/
theorem full_tree_standard_jacobian {n : ℕ} (t : OrderedTree n) :
    ∃ ε : ℝ, (ε=1 ∨ ε= -1) ∧ ∀ x : TreeRates n,
      treeCanonicalJacobian t x = ε * originalTreeRateMonomial t x * originalTreeSiblingProduct t x := by
  refine ⟨treeProofOrientation t,treeProofOrientation_sign t,?_⟩
  intro x
  rw [all_tree_canonical_jacobian,allTreeJacobianWeight_eq_original_products]
  ring

end HydrologyTree
