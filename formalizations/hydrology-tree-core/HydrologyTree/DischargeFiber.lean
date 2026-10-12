import HydrologyTree.RealFiberClassification

/-! Actual root-discharge transfer: the observed output is the root leak times
root storage. The leak is recovered from the transfer, not assumed calibrated.
This is a matrix-resolvent theorem; no unproved all-input ODE bridge is claimed. -/
open Polynomial
noncomputable section
namespace HydrologyTree

def physicalDischargeResponse {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (s : ℝ) : ℝ :=
  x.1 0 * physicalRootResponse t x s

def stieltjesLeak {n : ℕ} (r w : Fin (n+1) → ℝ) : ℝ := (∑ i, w i/r i)⁻¹

lemma stieltjesLeak_pos {n : ℕ} (r w : Fin (n+1) → ℝ)
    (hr : ∀ i, 0 < r i) (hw : ∀ i, 0 < w i) : 0 < stieltjesLeak r w := by
  apply inv_pos.mpr
  exact Finset.sum_pos (fun i _ => div_pos (hw i) (hr i)) Finset.univ_nonempty

/-- The root leak is fixed by the full target response, not an independently
assumed known parameter. No positivity premise is made on the competing x. -/
theorem full_stieltjes_leak_identified {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1)
    (hP : physicalCharacteristic t x=stieltjesDenominator r)
    (hF : physicalRootCofactor t x=stieltjesNumerator r w) : x.1 0=stieltjesLeak r w := by
  have hx := real_stieltjes_realization_is_positive t x r w hr hpos hw hm hP hF
  rw [physical_root_leak_eq_ratio t x (fun e => ne_of_gt (hx.1 e.succ)),hP,hF,stieltjesLeak]
  have hz := stieltjes_quotient_eq_sum r w 0 (fun i => by simpa using ne_of_gt (hpos i))
  simp only [zero_add] at hz
  rw [← hz]
  simp [div_eq_mul_inv,mul_comm]

/-- Two equal actual discharge transfers have the same leak coefficient,
recovered by the leading coefficients of the full cross-polynomial identity. -/
theorem equal_discharge_recovers_leak {n : ℕ} (t : OrderedTree n) (x y : TreeRates n)
    (h : ∀ s, (physicalCharacteristic t x).eval s ≠ 0 → (physicalCharacteristic t y).eval s ≠ 0 →
      physicalDischargeResponse t x s=physicalDischargeResponse t y s) : x.1 0=y.1 0 := by
  have hc : C (x.1 0)*physicalRootCofactor t x*physicalCharacteristic t y =
      C (y.1 0)*physicalRootCofactor t y*physicalCharacteristic t x := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (infinite_nonroots (physicalCharacteristic t x*physicalCharacteristic t y)
      (mul_ne_zero (physicalCharacteristic_monic t x).ne_zero
        (physicalCharacteristic_monic t y).ne_zero)).mono
    intro s hs
    have hp : (physicalCharacteristic t x).eval s*(physicalCharacteristic t y).eval s ≠ 0 := by
      simpa only [Set.mem_setOf_eq,Polynomial.eval_mul] using hs
    have hx := left_ne_zero_of_mul hp
    have hy := right_ne_zero_of_mul hp
    have he := h s hx hy
    simp only [physicalDischargeResponse,physicalRootResponse_eq,← mul_div_assoc] at he
    have heq := (div_eq_div_iff hx hy).mp he
    simpa only [Set.mem_setOf_eq,Polynomial.eval_mul,Polynomial.eval_C] using heq
  have hl := congrArg Polynomial.leadingCoeff hc
  simpa only [Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_C,
    (physicalRootCofactor_monic t x).leadingCoeff,(physicalRootCofactor_monic t y).leadingCoeff,
    (physicalCharacteristic_monic t x).leadingCoeff,(physicalCharacteristic_monic t y).leadingCoeff,
    mul_one] using hl

def HasStieltjesDischargeResponse {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) : Prop :=
  ∀ s, (physicalCharacteristic t x).eval s ≠ 0 → (∀ i, s+r i ≠ 0) →
    physicalDischargeResponse t x s = stieltjesLeak r w * ∑ i, w i/(s+r i)

/-- Actual discharge data identify the leak and hence the normalized root
response. The competing real rates have no imposed sign restrictions. -/
theorem stieltjes_discharge_iff_root_response {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    HasStieltjesDischargeResponse t x r w ↔ HasStieltjesRootResponse t x r w := by
  constructor
  · intro h
    obtain ⟨z,hz,hPz,hFz⟩ := positive_tree_stieltjes_realization_exists t r w hr hpos hw hm
    have hlz := full_stieltjes_leak_identified t z r w hr hpos hw hm hPz hFz
    have hleak := equal_discharge_recovers_leak t x z (by
      intro s hx hz
      have hi : ∀ i, s+r i ≠ 0 := by
        rw [hPz,eval_stieltjesDenominator,Finset.prod_ne_zero_iff] at hz
        exact fun i => hz i (Finset.mem_univ i)
      rw [h s hx hi,physicalDischargeResponse,hlz,physicalRootResponse_eq,hPz,hFz,
        stieltjes_quotient_eq_sum r w s hi])
    intro s hx hi
    have he := h s hx hi
    rw [physicalDischargeResponse,hleak,hlz] at he
    exact mul_left_cancel₀ (ne_of_gt (stieltjesLeak_pos r w hpos hw)) he
  · intro h
    obtain ⟨hP,hF⟩ := (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x).mp h
    have hl := full_stieltjes_leak_identified t x r w hr hpos hw hm hP hF
    intro s hx hi
    rw [physicalDischargeResponse,hl,h s hx hi]

abbrev RealDischargeFiber {n : ℕ} (t : OrderedTree n) (r w : Fin (n+1) → ℝ) :=
  {x : TreeRates n // HasStieltjesDischargeResponse t x r w}

def realDischargeFiberEquivRoot {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    RealDischargeFiber t r w ≃ RealResponseFiber t r w where
  toFun x := ⟨x.val,(stieltjes_discharge_iff_root_response t x.val r w hr hpos hw hm).mp x.property⟩
  invFun x := ⟨x.val,(stieltjes_discharge_iff_root_response t x.val r w hr hpos hw hm).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact finite count for the ACTUAL discharge transfer, with its unknown
root-leak coefficient identified rather than assumed supplied. -/
theorem real_discharge_fiber_exact_card {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Finite (RealDischargeFiber t r w) ∧
      Nat.card (RealDischargeFiber t r w)=n.factorial / (∏ e : Fin n, subtreeVertexCount t e.succ) := by
  obtain ⟨hf,hc⟩ := real_root_response_fiber_exact_card t r w hr hpos hw hm
  letI := hf
  let E := realDischargeFiberEquivRoot t r w hr hpos hw hm
  exact ⟨Finite.of_injective E E.injective,(Nat.card_congr E).trans hc⟩

end HydrologyTree
