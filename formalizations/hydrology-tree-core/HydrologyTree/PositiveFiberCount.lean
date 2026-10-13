import HydrologyTree.PositiveFiberEquivalence
import HydrologyTree.TreeFiberCombinatorics
import Mathlib.SetTheory.Cardinal.Finite

/-! Complete all-size positive realization count for the actual physical model.
The finiteness statement is proved separately, so Nat.card cannot silently
encode an infinite fiber by zero. The main theorem leaves no child-fiber count,
allocation-completeness, positivity or inverse-realization assertion unproved. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Actual positive full-response fibers are finite and have exactly the
recursive labelled-allocation degree. All smaller-fiber obligations are discharged
by strong induction, not hypotheses of the final theorem. -/
theorem positive_stieltjes_fiber_finite_card {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Finite (PositiveStieltjesFiber t r w) ∧
      Nat.card (PositiveStieltjesFiber t r w)=treeFiberDegree t := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨b,g,d,hb,hbpos,hg,hF,hP,hl⟩ :=
      exists_positive_reciprocal_data_unordered r w hr hpos hw hm
    have hc (a : TreePoleAllocation t) (c : RootChild t) :
        Finite (PositiveStieltjesFiber (childTree t c) (allocatedRates b a c) (allocatedWeights t g a c)) ∧
        Nat.card (PositiveStieltjesFiber (childTree t c) (allocatedRates b a c) (allocatedWeights t g a c)) =
          treeFiberDegree (childTree t c) :=
      ih _ (childEdgeCount_lt t c) (childTree t c)
        (allocatedRates b a c) (allocatedWeights t g a c)
        (allocatedRates_injective t b hb.injective a c) (fun i => hbpos _)
        (allocatedWeights_pos t g hg a c) (allocatedWeights_sum t g hg a c)
    letI : ∀ (a : TreePoleAllocation t) (c : RootChild t),
        Finite (PositiveStieltjesFiber (childTree t c) (allocatedRates b a c) (allocatedWeights t g a c)) :=
      fun a c => (hc a c).1
    let e := positiveReciprocalFiberEquiv t b g d hb.injective hbpos hg hl
    have hf : Finite (PositiveReciprocalFiber t b g d) := Finite.of_injective e e.injective
    have hcard : Nat.card (PositiveReciprocalFiber t b g d) = treeFiberDegree t := by
      rw [Nat.card_congr e,Nat.card_sigma]
      calc
        (∑ a : TreePoleAllocation t, Nat.card (AllocatedChildFibers t b g a)) =
            ∑ _a : TreePoleAllocation t, ∏ c : RootChild t, treeFiberDegree (childTree t c) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Nat.card_pi]
          exact Finset.prod_congr rfl (fun c _ => (hc a c).2)
        _ = Fintype.card (TreePoleAllocation t) * ∏ c : RootChild t, treeFiberDegree (childTree t c) := by
          rw [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul]
        _ = treeFiberDegree t := by rw [treeFiberDegree]
    change Finite (PositivePolynomialFiber t (stieltjesDenominator r) (stieltjesNumerator r w)) ∧
      Nat.card (PositivePolynomialFiber t (stieltjesDenominator r) (stieltjesNumerator r w)) = _
    rw [hP,hF]
    exact ⟨hf,hcard⟩

/-- The complete exact positive-fiber theorem in ORIGINAL tree coordinates:
for a tree with n+1 vertices, exactly n! / product_(v≠root) |T_v| distinct
strictly positive rate vectors realize the specified full Stieltjes pair.
Store labels are retained; no quotient by tree automorphisms is being taken. -/
theorem positive_stieltjes_fiber_exact_card {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Finite (PositiveStieltjesFiber t r w) ∧
      Nat.card (PositiveStieltjesFiber t r w) =
        n.factorial / (∏ e : Fin n, subtreeVertexCount t e.succ) := by
  obtain ⟨hf,hc⟩ := positive_stieltjes_fiber_finite_card t r w hr hpos hw hm
  exact ⟨hf,hc.trans (treeFiberDegree_eq_factorial_quotient t)⟩

/-- The exact count depends only on topology, not on the distinct positive poles
or normalized positive weights of the full target response. -/
theorem positive_stieltjes_card_independent_of_response {n : ℕ} (t : OrderedTree n)
    (r w q v : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1)
    (hq : Function.Injective q) (hqpos : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) (hn : (∑ i, v i)=1) :
    Nat.card (PositiveStieltjesFiber t r w)=Nat.card (PositiveStieltjesFiber t q v) := by
  rw [(positive_stieltjes_fiber_finite_card t r w hr hpos hw hm).2,
    (positive_stieltjes_fiber_finite_card t q v hq hqpos hv hn).2]

end HydrologyTree
