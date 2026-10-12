import HydrologyTree.RealFactorAllocation
import HydrologyTree.PositiveFiberEquivalence

/-! Automatic strict positivity of every REAL realization of a full positive
Stieltjes response on a fixed labelled tree. Physical admissibility is derived
from the response, not imposed on competing parameters. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Arbitrary real child rates inherit the exact normalized Stieltjes cofactors
once their actual characteristic-factor allocation has been identified. -/
theorem realFiber_child_cofactors {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (b g : Fin n → ℝ) (d : ℝ) (hb : Function.Injective b)
    (hpos : ∀ i, 0 < b i) (hg : ∀ i, 0 < g i) (hl : 0 < d-∑ i, g i/b i)
    (hP : physicalCharacteristic t x=(X+C d)*stieltjesDenominator b-stieltjesNumerator b g)
    (a : TreePoleAllocation t)
    (ha : ∀ c, childCharacteristic t x c=allocatedDenominator b a c) :
    ∀ c, childCofactor t x c=stieltjesNumerator (allocatedRates b a c) (allocatedWeights t g a c) := by
  let y := Classical.choice (allocatedChildFibers_nonempty t b g hb hpos hg a)
  obtain ⟨z,hz⟩ := allocatedChildren_assemble t b g d hpos hg hl a y
  have hzc (c : RootChild t) : childCharacteristic t z.val c=allocatedDenominator b a c := by
    change physicalCharacteristic (childTree t c) (childRates t c z.val) = _
    rw [hz]
    exact (y c).property.2.1
  have hcop : ∀ c k : RootChild t, c ≠ k →
      IsCoprime (childCharacteristic t z.val c) (childCharacteristic t z.val k) := by
    intro c k hck
    rw [hzc c,hzc k]
    exact allocated_child_factors_coprime t b hb a c k hck
  have hh := physical_child_coefficients_identified t z.val x
    ⟨fun e => ne_of_gt (z.property.1.1 e.succ),fun e => ne_of_gt (z.property.1.2 e)⟩
    hcop (fun c => (hzc c).trans (ha c).symm) (z.property.2.1.trans hP.symm)
  intro c
  rw [← (hh c).1]
  change physicalRootCofactor (childTree t c) (childRates t c z.val) = _
  rw [hz]
  exact (y c).property.2.2

/-- Every real parameter vector realizing the full positive Stieltjes pair is
strictly positive, including its root leak and every directed edge rate. No
positivity, nonzero-edge or Jacobian-regularity premise is placed on x. -/
theorem real_stieltjes_realization_is_positive {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1)
    (hP : physicalCharacteristic t x=stieltjesDenominator r)
    (hF : physicalRootCofactor t x=stieltjesNumerator r w) : PositiveRateVector x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨b,g,d,hb,hbpos,hg,hFb,hPb,hl⟩ :=
      exists_positive_reciprocal_data_unordered r w hr hpos hw hm
    have hFx := hF.trans hFb
    have hPx := hP.trans hPb
    obtain ⟨a,ha⟩ := real_child_allocation_exists t x b hb.injective hFx
    have hFc := realFiber_child_cofactors t x b g d hb.injective hbpos hg hl hPx a ha
    have hchild (c : RootChild t) : PositiveRateVector (childRates t c x) :=
      ih _ (childEdgeCount_lt t c) (childTree t c) (childRates t c x)
        (allocatedRates b a c) (allocatedWeights t g a c)
        (allocatedRates_injective t b hb.injective a c) (fun i => hbpos _)
        (allocatedWeights_pos t g hg a c) (allocatedWeights_sum t g hg a c)
        (ha c) (hFc c)
    let y : AllocatedChildFibers t b g a := fun c => ⟨childRates t c x,hchild c,ha c,hFc c⟩
    obtain ⟨z,hz⟩ := allocatedChildren_assemble t b g d hbpos hg hl a y
    have hzc (c : RootChild t) : childCharacteristic t z.val c=allocatedDenominator b a c := by
      change physicalCharacteristic (childTree t c) (childRates t c z.val) = _
      rw [hz]
      exact ha c
    have hzx : z.val=x := by
      apply positive_parent_unique_from_children t z.val x z.property.1
      · intro c k hck
        rw [hzc c,hzc k]
        exact allocated_child_factors_coprime t b hb.injective a c k hck
      · exact z.property.2.1.trans hPx.symm
      · exact z.property.2.2.trans hFx.symm
      · exact hz
    exact hzx ▸ z.property.1

end HydrologyTree
