import HydrologyTree.MatrixSiblingWeight
import HydrologyTree.SubtreeProducts
import HydrologyTree.GraphPositiveWeight

/-! Actual gauge-invariant edge weights flattened onto original edge coordinates.
The exponents are original observed-root subtree sizes, not arbitrary recursion labels. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

theorem matrixEdgeWeight_offdiag_congr {n : ℕ} (t : OrderedTree n) (A B : TreeMatrix n)
    (hAB : ∀ i j, i ≠ j → A i j=B i j) : matrixEdgeWeight t A=matrixEdgeWeight t B := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [matrixEdgeWeight]
    conv_rhs => rw [matrixEdgeWeight]
    apply Finset.prod_congr rfl
    intro c _
    rw [hAB 0 c.val (Ne.symm c.property.1),hAB c.val 0 c.property.1]
    congr 1
    apply ih _ (childEdgeCount_lt t c)
    intro i j hij
    exact hAB _ _ (fun h => hij (childEnumeration_injective t c h))

def edgePowerMonomial {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ :=
  ∏ e : Fin n,(x.1 e.succ*x.2 e)^(subtreeVertexCount t e.succ-1)

lemma edgePowerMonomial_recursion {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    edgePowerMonomial t x = ∏ c : RootChild t,
      (x.1 c.val*outwardByVertex x.2 c.val)^childEdgeCount t c *
        edgePowerMonomial (childTree t c) (childRates t c x) := by
  rw [edgePowerMonomial,← (numberedEdgeEquiv t).prod_comp,Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro c _
  have hs (i : Fin (childEdgeCount t c+1)) :
      (numberedEdgeEquiv t ⟨c,i⟩).succ=(childEnumeration t c i).val := numberedEdgeIndex_succ t ⟨c,i⟩
  simp only [hs,outward_at_numbered_child]
  change (∏ i : Fin (childEdgeCount t c+1),
    (x.1 (childEnumeration t c i).val*outwardByVertex x.2 (childEnumeration t c i).val)^
      (subtreeVertexCount t (childEnumeration t c i).val-1)) = _
  simp only [subtreeVertexCount_child,Fin.prod_univ_succ,childEnumeration_zero,
    subtreeVertexCount_root,Nat.add_sub_cancel]
  rfl

theorem matrixEdgeWeight_physical {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    matrixEdgeWeight t (compartmentMatrix t x)=edgePowerMonomial t x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [matrixEdgeWeight,edgePowerMonomial_recursion]
    apply Finset.prod_congr rfl
    intro c _
    rw [root_inward_child,root_outward_child,principalChildOver_real,supportedChild_physical,
      ih _ (childEdgeCount_lt t c)]

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma graphMatrix_offdiag_leak_independent (o ell : V) (y : GraphRates G) (i j : V) (hij : i ≠ j) :
    graphCompartmentMatrix G ell y i j=graphCompartmentMatrix G o y i j := by
  have hz (v : V) : Matrix.single v v (1 : ℝ) i j=0 := by
    apply Matrix.single_apply_of_ne
    rintro ⟨hi,hj⟩
    exact hij (hi.symm.trans hj)
  simp only [graphCompartmentMatrix,Matrix.sub_apply,Matrix.smul_apply,hz,smul_zero,sub_zero]

/-- Leak location changes no edge-product exponent or physical edge coordinate. -/
theorem graphObserved_edgeWeight {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (ell : V) (y : GraphRates G) :
    matrixEdgeWeight p.tree (graphObservedMatrix p ell y)=
      edgePowerMonomial p.tree ((graphRateEquiv p).symm y) := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv p).surjective y
  rw [LinearEquiv.symm_apply_apply,← matrixEdgeWeight_physical]
  have he := graphCompartmentMatrix_transport p x
  rw [← he]
  apply matrixEdgeWeight_offdiag_congr
  intro i j hij
  exact graphMatrix_offdiag_leak_independent o ell _ _ _ (fun h => hij (p.vertices.injective h))

end HydrologyTree
