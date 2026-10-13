import HydrologyTree.TimeDomainIdentification
import HydrologyTree.FullResponseDynamics

/-! Complete identification and finite-fiber classification from actual
continuous-input ODE outputs. No positivity, stability, or trajectory-existence
assumption on a competing real parameter vector is hidden in the membership. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Actual zero-initial root output for every continuous forcing at all
nonnegative times. It specifies no internal coefficients or states. -/
def HasFullContinuousRootOutput {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) : Prop :=
  ∀ (u : ℝ → ℝ), Continuous u → ∀ z : ℝ → Fin (n+1) → ℝ,
    IsPhysicalForcedSolution t x u z → z 0=0 → ∀ s : ℝ, 0 ≤ s →
      z s 0=∑ i, w i*scalarForcedSolution (r i) u 0 0 s

/-- Both directions are proved for unrestricted real competitors. Explicit
exponential probes prevent a vacuous use of the universal trajectory predicate. -/
theorem continuous_root_output_iff_response {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    HasFullContinuousRootOutput t x r w ↔ HasStieltjesRootResponse t x r w := by
  constructor
  · intro h
    obtain ⟨y,hy,hPy,hFy⟩ := positive_tree_stieltjes_realization_exists t r w hr hpos hw hm
    have hsame : SameContinuousRootOutputs t t y x := by
      intro u hu z q hz hq hz0 hq0 s hs
      exact (physical_forced_root_formula t y hy r w hr hPy hFy u hu 0 z hz hz0 s).trans
        (h u hu q hq hq0 s hs).symm
    have hcross := same_continuous_outputs_cross_identity t t y x hsame
    have hJ := positive_stieltjes_fiber_regular t r w hr hpos hw hm ⟨y,hy,hPy,hFy⟩
    have hcop := (physicalPair_coprime_iff_all_rates t y).mpr ⟨fun e => ne_of_gt (hy.2 e),hJ⟩
    have hdeg : (physicalCharacteristic t x).natDegree=(physicalCharacteristic t y).natDegree := by
      rw [physicalCharacteristic_natDegree,physicalCharacteristic_natDegree]
    obtain ⟨hP,hF⟩ := full_degree_fraction_unique _ _ _ _
      (physicalCharacteristic_monic t y) (physicalCharacteristic_monic t x) hdeg hcop hcross
    exact (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x).mpr
      ⟨hP.symm.trans hPy,hF.symm.trans hFy⟩
  · intro h u hu z hz hz0 s _
    obtain ⟨hP,hF⟩ := (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x).mp h
    have hx := real_stieltjes_realization_is_positive t x r w hr hpos hw hm hP hF
    exact physical_forced_root_formula t x hx r w hr hP hF u hu 0 z hz hz0 s

abbrev RealContinuousOutputFiber {n : ℕ} (t : OrderedTree n) (r w : Fin (n+1) → ℝ) :=
  {x : TreeRates n // HasFullContinuousRootOutput t x r w}

def continuousOutputFiberEquivResponse {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    RealContinuousOutputFiber t r w ≃ RealResponseFiber t r w where
  toFun x := ⟨x.val,(continuous_root_output_iff_response t x.val r w hr hpos hw hm).mp x.property⟩
  invFun x := ⟨x.val,(continuous_root_output_iff_response t x.val r w hr hpos hw hm).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complete exact real fiber count now applies to genuine continuous-input
ODE behavior, not only formal rational functions or extra coefficient data. -/
theorem real_continuous_output_fiber_exact_card {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Finite (RealContinuousOutputFiber t r w) ∧
      Nat.card (RealContinuousOutputFiber t r w)=n.factorial / (∏ e : Fin n, subtreeVertexCount t e.succ) := by
  obtain ⟨hf,hc⟩ := real_root_response_fiber_exact_card t r w hr hpos hw hm
  letI := hf
  let E := continuousOutputFiberEquivResponse t r w hr hpos hw hm
  exact ⟨Finite.of_injective E E.injective,(Nat.card_congr E).trans hc⟩

/-- The observed ODE behavior forces physical positivity, regularity, and
actual global existence and uniqueness for every continuous input. -/
theorem continuous_output_forces_physical_wellposedness {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (hx : HasFullContinuousRootOutput t x r w) :
    PositiveRateVector x ∧ treeCanonicalJacobian t x ≠ 0 ∧
      ∀ (u : ℝ → ℝ), Continuous u → ∀ (a : ℝ) (z0 : Fin (n+1) → ℝ),
        ∃! z : ℝ → Fin (n+1) → ℝ, IsPhysicalForcedSolution t x u z ∧ z a=z0 := by
  have hR := (continuous_root_output_iff_response t x r w hr hpos hw hm).mp hx
  obtain ⟨hposx,hJ⟩ := real_full_response_forces_positive_regular t x r w hr hpos hw hm hR
  exact ⟨hposx,hJ,fun u hu a z0 => physical_forced_ODE_existsUnique t x hposx u hu a z0⟩

end HydrologyTree
