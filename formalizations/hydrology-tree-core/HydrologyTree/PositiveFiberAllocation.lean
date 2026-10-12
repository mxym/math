import HydrologyTree.AllocationPolynomials
import HydrologyTree.SpectralFactorMatching
import HydrologyTree.PositiveRealizationExistence

/-! Every actual positive model with a prescribed simple root cofactor has a
unique labelled allocation of its reciprocal poles to the actual child blocks.
This is an exhaustive extraction theorem, not just a construction of examples. -/
open Polynomial
noncomputable section
namespace HydrologyTree

abbrev TreePoleAllocation {n : ℕ} (t : OrderedTree n) :=
  SizedAllocation (fun c : RootChild t => childEdgeCount t c+1) n

/-- All actual positive child blocks inherit strict positivity, including their
root exit-to-parent leak, in the full physical-rate convention. -/
lemma positive_child_vector {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : PositiveRateVector x) (c : RootChild t) : PositiveRateVector (childRates t c x) := by
  have h := positive_child_rates t x c (fun e => hx.1 e.succ) hx.2
  constructor
  · intro v
    refine Fin.cases h.1 (fun e => h.2.1 e) v
  · exact h.2.2

/-- Exhaustive allocation extraction from the actual principal characteristic
polynomials. Only the reference pole list is assumed simple. -/
theorem positive_child_allocation_exists {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : PositiveRateVector x) (b : Fin n → ℝ) (hb : Function.Injective b)
    (hF : physicalRootCofactor t x = stieltjesDenominator b) :
    ∃ a : TreePoleAllocation t, ∀ c,
      childCharacteristic t x c = allocatedDenominator b a c := by
  have hc (c : RootChild t) : ∃ q : Fin (childEdgeCount t c+1) → ℝ,
      (∀ i, 0 < q i) ∧ childCharacteristic t x c = stieltjesDenominator q := by
    have h := positive_child_rates t x c (fun e => hx.1 e.succ) hx.2
    exact physical_characteristic_negative_real_factorization (childTree t c)
      (childRates t c x) h.1 h.2.1 h.2.2
  choose q hq hP using hc
  let r : NumberedChildNodes t → ℝ := fun v => q v.1 v.2
  have heq : stieltjesDenominator r = stieltjesDenominator b := by
    rw [stieltjesDenominator_sigma]
    calc
      (∏ c : RootChild t, stieltjesDenominator (q c)) =
          ∏ c : RootChild t, childCharacteristic t x c := by
            exact Finset.prod_congr rfl (fun c _ => (hP c).symm)
      _ = physicalRootCofactor t x := (physicalRootCofactor_child_product t x).symm
      _ = stieltjesDenominator b := hF
  obtain ⟨e,he⟩ := stieltjes_factor_matching (numberedEdgeEquiv t) r b hb heq
  refine ⟨allocationOfEquiv e,?_⟩
  intro c
  rw [hP c,allocatedDenominator_of_equiv]
  congr 1
  funext i
  exact he ⟨c,i⟩

/-- The allocation is genuinely unique for a fixed actual parent model. -/
theorem positive_child_allocation_unique {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (b : Fin n → ℝ) (hb : Function.Injective b) (a d : TreePoleAllocation t)
    (ha : ∀ c, childCharacteristic t x c=allocatedDenominator b a c)
    (hd : ∀ c, childCharacteristic t x c=allocatedDenominator b d c) : a=d := by
  apply allocatedDenominators_injective b hb
  funext c
  exact (ha c).symm.trans (hd c)

/-- Distinct root allocations have disjoint actual positive parameter fibers. -/
theorem allocated_child_factors_coprime {n : ℕ} (t : OrderedTree n)
    (b : Fin n → ℝ) (hb : Function.Injective b) (a : TreePoleAllocation t)
    (c d : RootChild t) (hcd : c ≠ d) :
    IsCoprime (allocatedDenominator b a c) (allocatedDenominator b a d) := by
  change IsCoprime
    (∏ i : Fin (childEdgeCount t c+1), (X+C (allocatedRates b a c i)))
    (∏ j : Fin (childEdgeCount t d+1), (X+C (allocatedRates b a d j)))
  apply IsCoprime.prod_left
  intro i _
  apply IsCoprime.prod_right
  intro j _
  apply coprime_linear_of_ne
  intro hrate
  have he := (allocationEquiv a).injective (hb hrate)
  exact hcd (congrArg Sigma.fst he)

end HydrologyTree
