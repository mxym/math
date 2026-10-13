import HydrologyTree.CoprimeBranchRecovery
import HydrologyTree.RootRecovery
import HydrologyTree.PhysicalCancellation

/-! Actual one-level physical recovery for prescribed labelled child denominator
factors. The reference's internal rates are nonzero; the competing real rate
vector is unrestricted. This is a building block for complete fiber classification. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Actual edge product times the actual child cofactor. -/
def physicalChildNumerator {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t) : ℝ[X] :=
  C (x.1 c.val * outwardByVertex x.2 c.val) * childCofactor t x c

lemma physicalChildNumerator_degree {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t) :
    (physicalChildNumerator t x c).degree < (childCharacteristic t x c).degree := by
  have hP : (childCharacteristic t x c).degree = ((childEdgeCount t c+1 : ℕ) : WithBot ℕ) := by
    unfold childCharacteristic
    rw [Polynomial.degree_eq_natDegree (physicalCharacteristic_monic _ _).ne_zero]
    exact congrArg (fun k : ℕ => (k : WithBot ℕ)) (physicalCharacteristic_natDegree _ _)
  rw [hP]
  by_cases hc : x.1 c.val * outwardByVertex x.2 c.val = 0
  · simp [physicalChildNumerator, hc]
  · rw [physicalChildNumerator, Polynomial.degree_C_mul hc]
    unfold childCofactor
    rw [Polynomial.degree_eq_natDegree (physicalRootCofactor_monic _ _).ne_zero,
      physicalRootCofactor_natDegree]
    exact_mod_cast Nat.lt_succ_self (childEdgeCount t c)

lemma physical_branch_numerator_sum {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    branchNumeratorSum (childCharacteristic t x) (physicalChildNumerator t x) =
      (X+C ((rateChart t x).1 0)) * (∏ c : RootChild t, childCharacteristic t x c) -
        physicalCharacteristic t x := by
  have h := physicalCharacteristic_child_recursion t x
  change physicalCharacteristic t x =
    (X+C ((rateChart t x).1 0)) * (∏ c : RootChild t, childCharacteristic t x c) -
      branchNumeratorSum (childCharacteristic t x) (physicalChildNumerator t x) at h
  linear_combination h

/-- The original parent characteristic and a fixed pairwise-coprime child-factor
assignment determine every actual edge-product times child cofactor globally. -/
theorem physical_child_numerators_identified {n : ℕ} (t : OrderedTree n) (x y : TreeRates n)
    (hcop : ∀ c d : RootChild t, c ≠ d →
      IsCoprime (childCharacteristic t x c) (childCharacteristic t x d))
    (hchild : ∀ c : RootChild t, childCharacteristic t x c = childCharacteristic t y c)
    (hparent : physicalCharacteristic t x = physicalCharacteristic t y) :
    physicalChildNumerator t x = physicalChildNumerator t y := by
  have hp : childCharacteristic t x = childCharacteristic t y := funext hchild
  apply coprime_branch_numerators_unique_mod_product (childCharacteristic t x)
    (physicalChildNumerator t x) (physicalChildNumerator t y) hcop
    (physicalChildNumerator_degree t x)
  · intro c
    rw [hchild c]
    exact physicalChildNumerator_degree t y c
  · refine ⟨C ((rateChart t x).1 0 - (rateChart t y).1 0), ?_⟩
    rw [physical_branch_numerator_sum, hp, physical_branch_numerator_sum, hparent]
    rw [map_sub]
    ring

/-- After the child denominators have been assigned, both child cofactors and
connector products are uniquely determined. No positivity premise is needed. -/
theorem physical_child_coefficients_identified {n : ℕ} (t : OrderedTree n) (x y : TreeRates n)
    (hx : NonzeroTreeEdges x)
    (hcop : ∀ c d : RootChild t, c ≠ d →
      IsCoprime (childCharacteristic t x c) (childCharacteristic t x d))
    (hchild : ∀ c : RootChild t, childCharacteristic t x c = childCharacteristic t y c)
    (hparent : physicalCharacteristic t x = physicalCharacteristic t y) :
    ∀ c : RootChild t,
      childCofactor t x c = childCofactor t y c ∧
      x.1 c.val * outwardByVertex x.2 c.val = y.1 c.val * outwardByVertex y.2 c.val := by
  have h := physical_child_numerators_identified t x y hcop hchild hparent
  intro c
  have he := congrFun h c
  have hn : x.1 c.val * outwardByVertex x.2 c.val ≠ 0 :=
    mul_ne_zero (inward_nonroot_ne_zero x hx c.val c.property.1)
      (outward_nonroot_ne_zero x hx c.val c.property.1)
  have hm := scalar_monic_polynomial_unique (childCofactor t x c) (childCofactor t y c)
    (physicalRootCofactor_monic _ _) (physicalRootCofactor_monic _ _)
    _ _ hn he
  exact ⟨hm.2,hm.1⟩

/-- A fixed child denominator assignment recovers the complete child coefficient
data and each actual outward connector, even for unrestricted alternative rates. -/
theorem physical_child_data_and_connectors_identified {n : ℕ} (t : OrderedTree n) (x y : TreeRates n)
    (hx : NonzeroTreeEdges x)
    (hcop : ∀ c d : RootChild t, c ≠ d →
      IsCoprime (childCharacteristic t x c) (childCharacteristic t x d))
    (hchild : ∀ c : RootChild t, childCharacteristic t x c = childCharacteristic t y c)
    (hparent : physicalCharacteristic t x = physicalCharacteristic t y) :
    ∀ c : RootChild t,
      physicalCoefficientMap (childTree t c) (childRates t c x) =
        physicalCoefficientMap (childTree t c) (childRates t c y) ∧
      outwardByVertex x.2 c.val = outwardByVertex y.2 c.val := by
  intro c
  have hc := physical_child_coefficients_identified t x y hx hcop hchild hparent c
  have he : physicalCoefficientMap (childTree t c) (childRates t c x) =
      physicalCoefficientMap (childTree t c) (childRates t c y) :=
    (physicalCoefficientMap_eq_iff _ _ _).mpr ⟨hchild c,hc.1⟩
  have hleak := physical_root_leak_identified (childTree t c) (childRates t c x)
    (childRates t c y) (nonzero_child_edges t c x hx).1 he
  rw [childRates_leak,childRates_leak] at hleak
  refine ⟨he,?_⟩
  rw [← hleak] at hc
  exact mul_left_cancel₀ (inward_nonroot_ne_zero x hx c.val c.property.1) hc.2

end HydrologyTree
