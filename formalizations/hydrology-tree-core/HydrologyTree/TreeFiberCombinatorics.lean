import HydrologyTree.PositiveFiberTypes
import HydrologyTree.SubtreeProducts

/-! Exact tree allocation counts on the original labelled vertex set. These
finite counts are linked to actual positive parameter fibers in the next module. -/
noncomputable section
namespace HydrologyTree

/-- Recursive labelled-allocation count; it does not yet stand for an actual
parameter fiber until the exhaustive fiber theorem is applied. -/
def treeFiberDegree {n : ℕ} (t : OrderedTree n) : ℕ :=
  Fintype.card (TreePoleAllocation t) * ∏ c : RootChild t, treeFiberDegree (childTree t c)
termination_by n
decreasing_by exact childEdgeCount_lt t c

/-- Product of actual subtree vertex counts over all ORIGINAL nonroot vertices. -/
def treeHookProduct {n : ℕ} (t : OrderedTree n) : ℕ :=
  ∏ e : Fin n, subtreeVertexCount t e.succ

lemma treeHookProduct_pos {n : ℕ} (t : OrderedTree n) : 0 < treeHookProduct t :=
  Finset.prod_pos (fun e _ => subtreeVertexCount_pos t e.succ)

lemma treeHookProduct_recursion {n : ℕ} (t : OrderedTree n) :
    treeHookProduct t = ∏ c : RootChild t,
      (childEdgeCount t c+1)*treeHookProduct (childTree t c) := by
  rw [treeHookProduct,← (numberedEdgeEquiv t).prod_comp,Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro c _
  have hs (i : Fin (childEdgeCount t c+1)) :
      (numberedEdgeEquiv t ⟨c,i⟩).succ = (childEnumeration t c i).val :=
    numberedEdgeIndex_succ t ⟨c,i⟩
  simp only [hs,subtreeVertexCount_child,Fin.prod_univ_succ,subtreeVertexCount_root]
  rfl

/-- Exact factorial identity, including the singleton tree. In particular it
proves the integrality of the eventual quotient instead of assuming it. -/
theorem treeFiberDegree_mul_hook {n : ℕ} (t : OrderedTree n) :
    treeFiberDegree t * treeHookProduct t = n.factorial := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [treeFiberDegree,treeHookProduct_recursion,mul_assoc,← Finset.prod_mul_distrib]
    have hf (c : RootChild t) : treeFiberDegree (childTree t c) *
        ((childEdgeCount t c+1)*treeHookProduct (childTree t c)) =
        (childEdgeCount t c+1).factorial := by
      calc
        _ = (childEdgeCount t c+1) *
          (treeFiberDegree (childTree t c)*treeHookProduct (childTree t c)) := by ring
        _ = (childEdgeCount t c+1)*(childEdgeCount t c).factorial := by
          rw [ih _ (childEdgeCount_lt t c)]
        _ = (childEdgeCount t c+1).factorial := (Nat.factorial_succ _).symm
    simp only [hf]
    exact sizedAllocation_card_factorial (numberedEdgeEquiv t)

/-- All-size hook-length expression on the original tree, not a recursive
symbolic count and not a table of small cases. -/
theorem treeFiberDegree_eq_factorial_quotient {n : ℕ} (t : OrderedTree n) :
    treeFiberDegree t = n.factorial / (∏ e : Fin n, subtreeVertexCount t e.succ) := by
  change treeFiberDegree t = n.factorial / treeHookProduct t
  rw [← treeFiberDegree_mul_hook t]
  exact (Nat.mul_div_cancel _ (treeHookProduct_pos t)).symm

lemma treeFiberDegree_pos {n : ℕ} (t : OrderedTree n) : 0 < treeFiberDegree t := by
  have h := Nat.factorial_pos n
  rw [← treeFiberDegree_mul_hook t] at h
  apply Nat.pos_of_ne_zero
  intro hz
  simpa [hz] using h

end HydrologyTree
