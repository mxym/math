import HydrologyTree.TimeDomainDischarge

/-! Exact all-real classification from actual continuous-input discharge histories.
The root leak is recovered from those histories, not externally prescribed. -/
open Polynomial
noncomputable section
namespace HydrologyTree

def HasFullContinuousDischargeOutput {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) : Prop :=
  ∀ (u : ℝ → ℝ), Continuous u → ∀ z : ℝ → Fin (n+1) → ℝ,
    IsPhysicalForcedSolution t x u z → z 0=0 → ∀ s : ℝ, 0 ≤ s →
      x.1 0*z s 0=stieltjesLeak r w*(∑ i, w i*scalarForcedSolution (r i) u 0 0 s)

/-- Exact inverse and forward equivalence, for unrestricted real competitors. -/
theorem continuous_discharge_output_iff_response {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    HasFullContinuousDischargeOutput t x r w ↔ HasStieltjesRootResponse t x r w := by
  constructor
  · intro h
    obtain ⟨y,hy,hPy,hFy⟩ := positive_tree_stieltjes_realization_exists t r w hr hpos hw hm
    have hly := full_stieltjes_leak_identified t y r w hr hpos hw hm hPy hFy
    have hsame : SameContinuousDischargeOutputs t t x y := by
      intro u hu z q hz hq hz0 hq0 s hs
      rw [h u hu z hz hz0 s hs,hly,
        physical_forced_root_formula t y hy r w hr hPy hFy u hu 0 q hq hq0 s]
    have hlx : x.1 0=stieltjesLeak r w := (same_continuous_discharge_leak t t x y hsame).trans hly
    apply (continuous_root_output_iff_response t x r w hr hpos hw hm).mp
    intro u hu z hz hz0 s hs
    have he := h u hu z hz hz0 s hs
    rw [hlx] at he
    exact mul_left_cancel₀ (ne_of_gt (stieltjesLeak_pos r w hpos hw)) he
  · intro h u hu z hz hz0 s hs
    obtain ⟨hP,hF⟩ := (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x).mp h
    rw [full_stieltjes_leak_identified t x r w hr hpos hw hm hP hF,
      (continuous_root_output_iff_response t x r w hr hpos hw hm).mpr h u hu z hz hz0 s hs]

abbrev RealContinuousDischargeFiber {n : ℕ} (t : OrderedTree n) (r w : Fin (n+1) → ℝ) :=
  {x : TreeRates n // HasFullContinuousDischargeOutput t x r w}

def continuousDischargeFiberEquivResponse {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    RealContinuousDischargeFiber t r w ≃ RealResponseFiber t r w where
  toFun x := ⟨x.val,(continuous_discharge_output_iff_response t x.val r w hr hpos hw hm).mp x.property⟩
  invFun x := ⟨x.val,(continuous_discharge_output_iff_response t x.val r w hr hpos hw hm).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual finite ODE discharge-fiber cardinality, with unknown leak recovered. -/
theorem real_continuous_discharge_fiber_exact_card {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Finite (RealContinuousDischargeFiber t r w) ∧
      Nat.card (RealContinuousDischargeFiber t r w)=n.factorial / (∏ e : Fin n, subtreeVertexCount t e.succ) := by
  obtain ⟨hf,hc⟩ := real_root_response_fiber_exact_card t r w hr hpos hw hm
  letI := hf
  let E := continuousDischargeFiberEquivResponse t r w hr hpos hw hm
  exact ⟨Finite.of_injective E E.injective,(Nat.card_congr E).trans hc⟩

end HydrologyTree
