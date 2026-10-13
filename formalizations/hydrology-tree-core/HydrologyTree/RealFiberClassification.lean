import HydrologyTree.RealFiberRigidity
import HydrologyTree.PositiveResponseFiber
import HydrologyTree.RecursiveFiberClassification

/-! Complete classification of UNRESTRICTED REAL realizations. For a full
positive Stieltjes target, the positive physical locus is forced by the data;
there are no additional mixed-sign, zero-rate, or singular real solutions.
The root leak location and original tree encoding are unchanged. -/
open Polynomial
noncomputable section
namespace HydrologyTree

abbrev RealStieltjesFiber {n : ℕ} (t : OrderedTree n) (r w : Fin (n+1) → ℝ) :=
  {x : TreeRates n // physicalCharacteristic t x=stieltjesDenominator r ∧
    physicalRootCofactor t x=stieltjesNumerator r w}

abbrev RealResponseFiber {n : ℕ} (t : OrderedTree n) (r w : Fin (n+1) → ℝ) :=
  {x : TreeRates n // HasStieltjesRootResponse t x r w}

/-- The entire real coefficient fiber is the positive fiber, with the SAME
rate vector. No positivity, minimality or regularity hypothesis is discarded. -/
def realStieltjesFiberEquivPositive {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    RealStieltjesFiber t r w ≃ PositiveStieltjesFiber t r w where
  toFun x := ⟨x.val,real_stieltjes_realization_is_positive t x.val r w hr hpos hw hm
    x.property.1 x.property.2,x.property⟩
  invFun x := ⟨x.val,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equality of actual root resolvents suffices for the same unrestricted-real
classification. Coefficients are recovered; they are not extra observations. -/
def realResponseFiberEquivCoefficients {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    RealResponseFiber t r w ≃ RealStieltjesFiber t r w where
  toFun x := ⟨x.val,(stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x.val).mp x.property⟩
  invFun x := ⟨x.val,(stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x.val).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full all-real response fiber bijection with the finite recursive labelled
allocation type. This is stronger than enumerating admissible positive models. -/
def realResponseRecursiveEquiv {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    RealResponseFiber t r w ≃ RecursivePoleAllocations t :=
  (realResponseFiberEquivCoefficients t r w hr hpos hw hm).trans
    ((realStieltjesFiberEquivPositive t r w hr hpos hw hm).trans
      (positiveStieltjesRecursiveEquiv t r w hr hpos hw hm))

/-- Exact finite count of ALL REAL coefficient realizations, not only the
positive subset. All real solutions are necessarily strictly positive. -/
theorem real_stieltjes_fiber_exact_card {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Finite (RealStieltjesFiber t r w) ∧
      Nat.card (RealStieltjesFiber t r w) =
        n.factorial / (∏ e : Fin n, subtreeVertexCount t e.succ) := by
  obtain ⟨hf,hc⟩ := positive_stieltjes_fiber_exact_card t r w hr hpos hw hm
  letI := hf
  let E := realStieltjesFiberEquivPositive t r w hr hpos hw hm
  exact ⟨Finite.of_injective E E.injective,(Nat.card_congr E).trans hc⟩

/-- Exact finite count of ALL REAL models sharing the actual full root response.
No physical sign constraints are assumptions on the counted rate vectors. -/
theorem real_root_response_fiber_exact_card {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Finite (RealResponseFiber t r w) ∧
      Nat.card (RealResponseFiber t r w) =
        n.factorial / (∏ e : Fin n, subtreeVertexCount t e.succ) := by
  obtain ⟨hf,hc⟩ := real_stieltjes_fiber_exact_card t r w hr hpos hw hm
  letI := hf
  let E := realResponseFiberEquivCoefficients t r w hr hpos hw hm
  exact ⟨Finite.of_injective E E.injective,(Nat.card_congr E).trans hc⟩

/-- The full target response forces strict positivity and a nonzero ACTUAL
coefficient Jacobian of any competing real vector, even one allowed initially
to have negative rates, vanishing rates or a nonpositive root leak. -/
theorem real_full_response_forces_positive_regular {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (hx : HasStieltjesRootResponse t x r w) :
    PositiveRateVector x ∧ treeCanonicalJacobian t x ≠ 0 := by
  obtain ⟨hP,hF⟩ := (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x).mp hx
  have hp := real_stieltjes_realization_is_positive t x r w hr hpos hw hm hP hF
  exact ⟨hp,positive_stieltjes_fiber_regular t r w hr hpos hw hm ⟨x,hp,hP,hF⟩⟩

end HydrologyTree
