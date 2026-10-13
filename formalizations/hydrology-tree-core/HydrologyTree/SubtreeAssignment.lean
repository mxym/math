import HydrologyTree.PhysicalBranchRecovery
import HydrologyTree.RateCoordinates

/-! Global all-size uniqueness for a prescribed recursive assignment of actual
subtree characteristic polynomials. This proves uniqueness per assignment;
existence of all assignments and their total count are separate obligations. -/
noncomputable section
namespace HydrologyTree

/-- Every local sibling family of the actual recursive principal model is coprime. -/
def CoprimeAtEveryBranch {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : Prop :=
  (∀ c d : RootChild t, c ≠ d →
    IsCoprime (childCharacteristic t x c) (childCharacteristic t x d)) ∧
  ∀ c : RootChild t, CoprimeAtEveryBranch (childTree t c) (childRates t c x)
termination_by n
decreasing_by exact childEdgeCount_lt t c

/-- Fixed labelled factor assignment at every vertex, using ACTUAL principal
subtree characteristic polynomials. Cofactors and rates are not assumed equal. -/
def SameSubtreeCharacteristics {n : ℕ} (t : OrderedTree n) (x y : TreeRates n) : Prop :=
  physicalCharacteristic t x = physicalCharacteristic t y ∧
  ∀ c : RootChild t, SameSubtreeCharacteristics (childTree t c) (childRates t c x) (childRates t c y)
termination_by n
decreasing_by exact childEdgeCount_lt t c

/-- Every recursive child-denominator assignment has AT MOST one realization
among all real rate vectors when the reference has nonzero internal rates and
coprime siblings. The competitor needs no positivity or regularity hypothesis. -/
theorem physical_subtree_assignment_unique {n : ℕ} (t : OrderedTree n) (x y : TreeRates n)
    (hx : NonzeroTreeEdges x) (hcop : CoprimeAtEveryBranch t x)
    (hassign : SameSubtreeCharacteristics t x y) : x = y := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [CoprimeAtEveryBranch] at hcop
    rw [SameSubtreeCharacteristics] at hassign
    have hchild : ∀ c : RootChild t, childCharacteristic t x c = childCharacteristic t y c := by
      intro c
      have hh := hassign.2 c
      rw [SameSubtreeCharacteristics] at hh
      exact hh.1
    have hcofactor : physicalRootCofactor t x = physicalRootCofactor t y := by
      rw [physicalRootCofactor_child_product, physicalRootCofactor_child_product]
      exact Finset.prod_congr rfl (fun c _ => hchild c)
    have hcoeff : physicalCoefficientMap t x = physicalCoefficientMap t y :=
      (physicalCoefficientMap_eq_iff t x y).mpr ⟨hassign.1,hcofactor⟩
    have hleak := physical_root_leak_identified t x y hx.1 hcoeff
    have hconnectors := physical_child_data_and_connectors_identified t x y hx hcop.1 hchild hassign.1
    have hstates (c : RootChild t) : childRates t c x = childRates t c y :=
      ih (childEdgeCount t c) (childEdgeCount_lt t c) (childTree t c) (childRates t c x)
        (childRates t c y) (nonzero_child_edges t c x hx) (hcop.2 c) (hassign.2 c)
    apply (ratePartitionEquiv t).injective
    apply Prod.ext
    · exact hleak
    · funext c
      rw [ratePartition_child,ratePartition_child,hstates c,(hconnectors c).2]

end HydrologyTree
