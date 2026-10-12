import HydrologyTree.PositiveFiberCount
import HydrologyTree.PositiveJacobian
import HydrologyTree.ResultantBoundary
import HydrologyTree.CatenaryCoprime

/-! The exact positive count applies to the ACTUAL root resolvent, not merely
to independently observed characteristic/cofactor coefficients. Equality is only
required on the common nonpole domain. No totalized value at a pole is interpreted
as a finite physical response, and no ODE solution bridge is assumed here. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Equality to the given Stieltjes response wherever both expressions are
actual nonpole resolvents. Characteristic coefficients are not extra observations. -/
def HasStieltjesRootResponse {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) : Prop :=
  ∀ s : ℝ, (physicalCharacteristic t x).eval s ≠ 0 → (∀ i, s+r i ≠ 0) →
    physicalRootResponse t x s = ∑ i, w i/(s+r i)

abbrev PositiveResponseFiber {n : ℕ} (t : OrderedTree n) (r w : Fin (n+1) → ℝ) :=
  {x : TreeRates n // PositiveRateVector x ∧ HasStieltjesRootResponse t x r w}

/-- Every member of a positive full-response coefficient fiber is actually
regular. The nonzero Jacobian is a conclusion, not a restriction on the counted set. -/
theorem positive_stieltjes_fiber_regular {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (x : PositiveStieltjesFiber t r w) :
    treeCanonicalJacobian t x.val ≠ 0 := by
  apply (positive_tree_jacobian_iff_full_modes t x.val (x.property.1.1 0)
    (fun e => x.property.1.1 e.succ) x.property.1.2).mpr
  exact ⟨r,w,hpos,hr,hw,hm,x.property.2.1,x.property.2.2⟩

/-- Full-size noncancelling response equality forces the entire polynomial pair,
even for a competing real rate vector not assumed positive or regular. -/
theorem stieltjes_root_response_iff_polynomials {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (x : TreeRates n) :
    HasStieltjesRootResponse t x r w ↔
      physicalCharacteristic t x=stieltjesDenominator r ∧
      physicalRootCofactor t x=stieltjesNumerator r w := by
  constructor
  · intro h
    obtain ⟨z,hz,hPz,hFz⟩ := positive_tree_stieltjes_realization_exists t r w hr hpos hw hm
    have hJ := positive_stieltjes_fiber_regular t r w hr hpos hw hm ⟨z,hz,hPz,hFz⟩
    have hcop := (physicalPair_coprime_iff_all_rates t z).mpr
      ⟨fun e => ne_of_gt (hz.2 e),hJ⟩
    have hcross := physical_response_eq_implies_cross_identity t z x (by
      intro s hs hx
      have hden : (stieltjesDenominator r).eval s ≠ 0 := by rwa [← hPz]
      have hi : ∀ i, s+r i ≠ 0 := by
        rw [eval_stieltjesDenominator,Finset.prod_ne_zero_iff] at hden
        exact fun i => hden i (Finset.mem_univ i)
      rw [physicalRootResponse_eq,hPz,hFz]
      exact (stieltjes_quotient_eq_sum r w s hi).trans (h s hx hi).symm)
    have hdeg : (physicalCharacteristic t x).natDegree=(physicalCharacteristic t z).natDegree := by
      rw [physicalCharacteristic_natDegree,physicalCharacteristic_natDegree]
    obtain ⟨heP,heF⟩ := full_degree_fraction_unique _ _ _ _
      (physicalCharacteristic_monic t z) (physicalCharacteristic_monic t x) hdeg hcop hcross
    exact ⟨heP.symm.trans hPz,heF.symm.trans hFz⟩
  · rintro ⟨hP,hF⟩ s _ hs
    rw [physicalRootResponse_eq,hP,hF]
    exact stieltjes_quotient_eq_sum r w s hs

def positiveResponseFiberEquiv {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    PositiveResponseFiber t r w ≃ PositiveStieltjesFiber t r w where
  toFun x := ⟨x.val,x.property.1,
    (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x.val).mp x.property.2⟩
  invFun x := ⟨x.val,x.property.1,
    (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x.val).mpr x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact all-size count of actual positive models sharing the prescribed root
resolvent. Finiteness and completeness are both proved, without genericity or
an extra observation of the internal characteristic polynomials. -/
theorem positive_root_response_fiber_exact_card {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Finite (PositiveResponseFiber t r w) ∧
      Nat.card (PositiveResponseFiber t r w) =
        n.factorial / (∏ e : Fin n, subtreeVertexCount t e.succ) := by
  obtain ⟨hf,hcard⟩ := positive_stieltjes_fiber_exact_card t r w hr hpos hw hm
  letI := hf
  let e := positiveResponseFiberEquiv t r w hr hpos hw hm
  exact ⟨Finite.of_injective e e.injective,(Nat.card_congr e).trans hcard⟩

end HydrologyTree
