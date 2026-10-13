import HydrologyTree.PositiveFiberTypes

/-! Reverse reconstruction of every positive fiber point. A constructed
reference is used only with the proved exact branch-recovery theorem; no
existence or inverse premise is left in the final statement. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- For an actual parent with known child factor assignment, its true child
cofactors must be the normalized residue polynomials for that assignment. -/
theorem positiveFiber_children_membership {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ)
    (d : ℝ) (hb : Function.Injective b) (hpos : ∀ i, 0 < b i) (hg : ∀ i, 0 < g i)
    (hl : 0 < d-∑ i, g i/b i) (x : PositiveReciprocalFiber t b g d)
    (a : TreePoleAllocation t)
    (ha : ∀ c, childCharacteristic t x.val c = allocatedDenominator b a c) :
    ∀ c, physicalRootCofactor (childTree t c) (childRates t c x.val) =
      stieltjesNumerator (allocatedRates b a c) (allocatedWeights t g a c) := by
  let y := Classical.choice (allocatedChildFibers_nonempty t b g hb hpos hg a)
  obtain ⟨z,hz⟩ := allocatedChildren_assemble t b g d hpos hg hl a y
  have hzc (c : RootChild t) : childCharacteristic t z.val c = allocatedDenominator b a c := by
    change physicalCharacteristic (childTree t c) (childRates t c z.val) = _
    rw [hz]
    exact (y c).property.2.1
  have hcop : ∀ c k : RootChild t, c ≠ k →
      IsCoprime (childCharacteristic t x.val c) (childCharacteristic t x.val k) := by
    intro c k hck
    rw [ha c,ha k]
    exact allocated_child_factors_coprime t b hb a c k hck
  have hcoef := physical_child_coefficients_identified t x.val z.val
    ⟨fun e => ne_of_gt (x.property.1.1 e.succ),fun e => ne_of_gt (x.property.1.2 e)⟩
    hcop (fun c => (ha c).trans (hzc c).symm) (x.property.2.1.trans z.property.2.1.symm)
  intro c
  change childCofactor t x.val c = _
  rw [(hcoef c).1]
  change physicalRootCofactor (childTree t c) (childRates t c z.val) = _
  rw [hz]
  exact (y c).property.2.2

/-- Equal actual child rate vectors and full parent coefficient data determine
the complete parent rate vector, including all original outward connectors. -/
theorem positive_parent_unique_from_children {n : ℕ} (t : OrderedTree n) (x y : TreeRates n)
    (hx : PositiveRateVector x)
    (hcop : ∀ c k : RootChild t, c ≠ k →
      IsCoprime (childCharacteristic t x c) (childCharacteristic t x k))
    (hP : physicalCharacteristic t x=physicalCharacteristic t y)
    (hF : physicalRootCofactor t x=physicalRootCofactor t y)
    (hchild : ∀ c, childRates t c x=childRates t c y) : x=y := by
  have hn : NonzeroTreeEdges x :=
    ⟨fun e => ne_of_gt (hx.1 e.succ),fun e => ne_of_gt (hx.2 e)⟩
  have hpc : ∀ c, childCharacteristic t x c=childCharacteristic t y c := by
    intro c
    change physicalCharacteristic _ (childRates t c x) = physicalCharacteristic _ (childRates t c y)
    rw [hchild]
  have hconn := physical_child_data_and_connectors_identified t x y hn hcop hpc hP
  have hroot := physical_root_leak_identified t x y hn.1
    ((physicalCoefficientMap_eq_iff t x y).mpr ⟨hP,hF⟩)
  apply (ratePartitionEquiv t).injective
  apply Prod.ext hroot
  funext c
  rw [ratePartition_child,ratePartition_child]
  exact Prod.ext (hconn c).2 (hchild c)

end HydrologyTree
