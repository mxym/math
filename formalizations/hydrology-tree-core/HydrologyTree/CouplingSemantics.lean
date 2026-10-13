import HydrologyTree.RateCoordinates
import HydrologyTree.RootCoupling

/-! Identification of root-coupling coordinates with the original physical rates
and root diagonal; child-leak evaluation is an actual linear projection. -/
open Module Matrix
noncomputable section
namespace HydrologyTree

lemma childEnumeration_root_iff {n : ℕ} (t : OrderedTree n) (c : RootChild t)
    (i : Fin (childEdgeCount t c+1)) : (childEnumeration t c i).val = c.val ↔ i = 0 := by
  constructor
  · intro h
    apply (childEnumeration t c).injective
    rw [childEnumeration_zero]
    exact Subtype.ext h
  · intro h
    subst i
    simp [branchRootVertex]

lemma childEnumeration_parent_zero_iff {n : ℕ} (t : OrderedTree n) (c : RootChild t)
    (i : Fin (childEdgeCount t c+1)) : parentVertex t (childEnumeration t c i).val = 0 ↔ i = 0 := by
  constructor
  · intro hp
    have h := rootBranchVertex_child t _ (branchVertex_ne_zero t c (childEnumeration t c i)) hp
    have he := (childEnumeration t c i).property.symm.trans h
    exact (childEnumeration_root_iff t c i).mp he.symm
  · intro h
    subst i
    rw [childEnumeration_zero]
    exact c.property.2

lemma numberedEdge_parent {n : ℕ} (t : OrderedTree n) (z : NumberedChildNodes t) :
    t.parent (numberedEdgeEquiv t z) = parentVertex t (childEnumeration t z.1 z.2).val := by
  rw [← numberedEdgeIndex_succ t z]
  rfl

/-- The physical sum of root exits is exactly the sum of the extracted connector rates. -/
theorem rootConnectors_sum {n : ℕ} (t : OrderedTree n) (f : EdgeValues n) :
    parentCLM t f 0 = ∑ c : RootChild t, outwardByVertex f c.val := by
  rw [parentCLM_apply, ← (numberedEdgeEquiv t).sum_comp
    (fun e => if t.parent e = 0 then f e else 0), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [numberedEdge_parent, childEnumeration_parent_zero_iff]
  rw [Finset.sum_eq_single 0]
  · rw [ite_eq_left rfl, outward_at_numbered_child t f c 0, childEnumeration_zero]
    rfl
  · intro i _ hi
    exact ite_eq_right hi
  · simp

abbrev ChildStates {n : ℕ} (t : OrderedTree n) := (c : RootChild t) → TreeRates (childEdgeCount t c)

/-- Genuine child-leak projection, not a prescribed auxiliary parameter function. -/
def childLeakMap {n : ℕ} (t : OrderedTree n) : ChildStates t →L[ℝ] (RootChild t → ℝ) :=
  ContinuousLinearMap.pi fun c => (ContinuousLinearMap.proj 0).comp
    ((ContinuousLinearMap.fst ℝ (VertexValues (childEdgeCount t c)) (EdgeValues (childEdgeCount t c))).comp
      (ContinuousLinearMap.proj c))

@[simp] lemma childLeakMap_apply {n : ℕ} (t : OrderedTree n) (y : ChildStates t) (c : RootChild t) :
    childLeakMap t y c = (y c).1 0 := rfl

def originalCouplingInputs {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    ChildStates t × (ℝ × (RootChild t → ℝ)) :=
  (fun c => childRates t c x, (x.1 0, fun c => outwardByVertex x.2 c.val))

/-- On original rates, the nonlinear coupling map computes exactly the root
diagonal and every connector's actual opposed-rate product. -/
theorem rootCoupling_physical_coordinates {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    rootCoupling (childLeakMap t) (originalCouplingInputs t x) =
      (fun c => childRates t c x,
        ((rateChart t x).1 0, fun c => x.1 c.val * outwardByVertex x.2 c.val)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change x.1 0 + sumCoordinates (fun c : RootChild t => outwardByVertex x.2 c.val) =
        x.1 0 + parentCLM t x.2 0
      rw [sumCoordinates_apply, rootConnectors_sum]
    · funext c
      change (childRates t c x).1 0 * outwardByVertex x.2 c.val = _
      rw [childRates_leak]

/-- The true preprocessing Jacobian on independent child and root-connector
coordinates, with no omitted zero-leak cases. -/
theorem actualCoupling_jacobian {n : ℕ} (t : OrderedTree n) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ (ChildStates t))
    (z : ChildStates t × (ℝ × (RootChild t → ℝ))) :
    (LinearMap.toMatrix (b.prod ((Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ (RootChild t))))
      (b.prod ((Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ (RootChild t))))
      (fderiv ℝ (rootCoupling (childLeakMap t)) z).toLinearMap).det =
      ∏ c : RootChild t, (z.1 c).1 0 :=
  rootCoupling_jacobian b (childLeakMap t) z

end HydrologyTree
