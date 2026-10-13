import HydrologyTree.PhysicalControllability
import HydrologyTree.ContinuousDischargeFiber
import HydrologyTree.TrajectoryObservability
import HydrologyTree.PhysicalMassODE

/-! A single unconditional entry for the original root-leak model's full
real-fiber and actual continuous-time system theory. Other leak locations and
independent graph presentations are deliberately not asserted here. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

def rootLeakDynamicalFiberEquiv {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    RealContinuousDischargeFiber t r w ≃ RecursivePoleAllocations t :=
  (continuousDischargeFiberEquivResponse t r w hr hpos hw hm).trans
    (realResponseRecursiveEquiv t r w hr hpos hw hm)

/-- Complete exact classification of actual continuous-input discharge histories,
with no sign or regularity assumption on a competing real model. -/
theorem root_leak_dynamical_fiber_classification {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Nonempty (RealContinuousDischargeFiber t r w ≃ RecursivePoleAllocations t) ∧
    Finite (RealContinuousDischargeFiber t r w) ∧
    Nat.card (RealContinuousDischargeFiber t r w)=n.factorial / (∏ e : Fin n, subtreeVertexCount t e.succ) := by
  exact ⟨⟨rootLeakDynamicalFiberEquiv t r w hr hpos hw hm⟩,
    real_continuous_discharge_fiber_exact_card t r w hr hpos hw hm⟩

/-- Every actual behavior-class member is positive, regular, globally classically
well-posed, controllable in every positive horizon with signed continuous input,
and observable from any nonempty open root-output time window. All prerequisites
are conclusions derived from the target, not additional assumptions on x. -/
theorem root_leak_full_dynamical_properties {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1)
    (x : RealContinuousDischargeFiber t r w) :
    PositiveRateVector x.val ∧ treeCanonicalJacobian t x.val ≠ 0 ∧
    (∀ (u : ℝ → ℝ), Continuous u → ∀ (a : ℝ) (z0 : Fin (n+1) → ℝ),
      ∃! z : ℝ → Fin (n+1) → ℝ, IsPhysicalForcedSolution t x.val u z ∧ z a=z0) ∧
    (∀ (T : ℝ), 0 < T → ∀ z0 z1 : Fin (n+1) → ℝ,
      ∃ u : ℝ → ℝ, Continuous u ∧ ∃! z : ℝ → Fin (n+1) → ℝ,
        IsPhysicalForcedSolution t x.val u z ∧ z 0=z0 ∧ z T=z1) ∧
    (∀ (u : ℝ → ℝ) (z q : ℝ → Fin (n+1) → ℝ),
      IsPhysicalForcedSolution t x.val u z → IsPhysicalForcedSolution t x.val u q →
      ∀ (a b : ℝ), a < b → (∀ s ∈ Set.Ioo a b, z s 0=q s 0) → z=q) := by
  have hR := (continuous_discharge_output_iff_response t x.val r w hr hpos hw hm).mp x.property
  obtain ⟨hp,hJ⟩ := real_full_response_forces_positive_regular t x.val r w hr hpos hw hm hR
  refine ⟨hp,hJ,?_,?_,?_⟩
  · exact fun u hu a z0 => physical_forced_ODE_existsUnique t x.val hp u hu a z0
  · exact fun T hT z0 z1 => real_full_response_controllable t x.val r w hr hpos hw hm hR T hT z0 z1
  · exact fun u z q hz hq a b hab hout =>
      real_full_response_trajectory_observable t x.val r w hr hpos hw hm hR u z q hz hq a b hab hout

end HydrologyTree
