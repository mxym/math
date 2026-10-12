import HydrologyTree.PositiveFiberRecovery

/-! The exhaustive one-level bijection between ACTUAL positive parameter fibers
and labelled pole allocations with actual positive child-fiber points. It is
proved both injective and surjective; no allocation-completeness premise remains. -/
open Polynomial
noncomputable section
namespace HydrologyTree

abbrev AllocatedFiberData {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ) :=
  Σ a : TreePoleAllocation t, AllocatedChildFibers t b g a

def allocatedParent {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ) (d : ℝ)
    (hpos : ∀ i, 0 < b i) (hg : ∀ i, 0 < g i) (hl : 0 < d-∑ i, g i/b i)
    (z : AllocatedFiberData t b g) : PositiveReciprocalFiber t b g d :=
  Classical.choose (allocatedChildren_assemble t b g d hpos hg hl z.1 z.2)

lemma allocatedParent_child {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ) (d : ℝ)
    (hpos : ∀ i, 0 < b i) (hg : ∀ i, 0 < g i) (hl : 0 < d-∑ i, g i/b i)
    (z : AllocatedFiberData t b g) (c : RootChild t) :
    childRates t c (allocatedParent t b g d hpos hg hl z).val = (z.2 c).val :=
  Classical.choose_spec (allocatedChildren_assemble t b g d hpos hg hl z.1 z.2) c

lemma allocatedParent_child_characteristic {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ) (d : ℝ)
    (hpos : ∀ i, 0 < b i) (hg : ∀ i, 0 < g i) (hl : 0 < d-∑ i, g i/b i)
    (z : AllocatedFiberData t b g) (c : RootChild t) :
    childCharacteristic t (allocatedParent t b g d hpos hg hl z).val c =
      allocatedDenominator b z.1 c := by
  change physicalCharacteristic (childTree t c)
    (childRates t c (allocatedParent t b g d hpos hg hl z).val) = _
  rw [allocatedParent_child]
  exact (z.2 c).property.2.1

/-- No two distinct labelled allocations or child-fiber tuples produce the
same original physical parent rate vector. -/
theorem allocatedParent_injective {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ) (d : ℝ)
    (hb : Function.Injective b) (hpos : ∀ i, 0 < b i) (hg : ∀ i, 0 < g i)
    (hl : 0 < d-∑ i, g i/b i) : Function.Injective (allocatedParent t b g d hpos hg hl) := by
  rintro ⟨a,u⟩ ⟨k,v⟩ h
  have hak : a=k := by
    apply allocatedDenominators_injective b hb
    funext c
    have he := congrArg (fun z : PositiveReciprocalFiber t b g d => childCharacteristic t z.val c) h
    simpa only [allocatedParent_child_characteristic] using he
  subst k
  have huv : u=v := by
    funext c
    apply Subtype.ext
    have he := congrArg (fun z : PositiveReciprocalFiber t b g d => childRates t c z.val) h
    simpa only [allocatedParent_child] using he
  subst v
  rfl

/-- EVERY original positive parent rate vector is obtained. The proof extracts
its unique root allocation and proves that its true child rates have the required
normalized reciprocal data before reconstructing the parent. -/
theorem allocatedParent_surjective {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ) (d : ℝ)
    (hb : Function.Injective b) (hpos : ∀ i, 0 < b i) (hg : ∀ i, 0 < g i)
    (hl : 0 < d-∑ i, g i/b i) : Function.Surjective (allocatedParent t b g d hpos hg hl) := by
  intro x
  obtain ⟨a,ha⟩ := positive_child_allocation_exists t x.val x.property.1 b hb x.property.2.2
  have hF := positiveFiber_children_membership t b g d hb hpos hg hl x a ha
  let y : AllocatedChildFibers t b g a := fun c =>
    ⟨childRates t c x.val,positive_child_vector t x.val x.property.1 c,ha c,hF c⟩
  let z := allocatedParent t b g d hpos hg hl ⟨a,y⟩
  refine ⟨⟨a,y⟩,?_⟩
  apply Subtype.ext
  change z.val=x.val
  symm
  apply positive_parent_unique_from_children t x.val z.val x.property.1
  · intro c k hck
    rw [ha c,ha k]
    exact allocated_child_factors_coprime t b hb a c k hck
  · exact x.property.2.1.trans z.property.2.1.symm
  · exact x.property.2.2.trans z.property.2.2.symm
  · intro c
    exact (allocatedParent_child t b g d hpos hg hl ⟨a,y⟩ c).symm

/-- Exhaustive actual-fiber classification at one root. Applying it recursively
is a genuine classification of all positive rates, not a count of candidate
factorizations or an unproved identification between those two sets. -/
def positiveReciprocalFiberEquiv {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ) (d : ℝ)
    (hb : Function.Injective b) (hpos : ∀ i, 0 < b i) (hg : ∀ i, 0 < g i)
    (hl : 0 < d-∑ i, g i/b i) :
    PositiveReciprocalFiber t b g d ≃ AllocatedFiberData t b g :=
  (Equiv.ofBijective (allocatedParent t b g d hpos hg hl)
    ⟨allocatedParent_injective t b g d hb hpos hg hl,
      allocatedParent_surjective t b g d hb hpos hg hl⟩).symm

end HydrologyTree
