import HydrologyTree.ExponentialODEProbe
import HydrologyTree.PhysicalForcedODE
import Mathlib.Order.Interval.Set.Infinite

/-! Actual all-continuous-input equality implies a polynomial transfer identity
for arbitrary real matrices. Positive exponential probes are genuine classical
solutions; the universal output predicate cannot be used vacuously. -/
open Matrix Polynomial Filter
open scoped Topology
noncomputable section
namespace HydrologyTree

def SameContinuousRootOutputs {n : ℕ} (t v : OrderedTree n) (x y : TreeRates n) : Prop :=
  ∀ (u : ℝ → ℝ), Continuous u →
    ∀ z q : ℝ → Fin (n+1) → ℝ,
      IsPhysicalForcedSolution t x u z → IsPhysicalForcedSolution v y u q →
      z 0=0 → q 0=0 → ∀ s : ℝ, 0 ≤ s → z s 0=q s 0

/-- Exponential input probes identify each sufficiently high nonpole resolvent
from actual trajectories, without assuming either matrix is stable. -/
theorem same_continuous_outputs_resolvent {n : ℕ} (t v : OrderedTree n) (x y : TreeRates n)
    (h : SameContinuousRootOutputs t v x y) (q : ℝ)
    (hqA : ‖matrixOperator (compartmentMatrix t x)‖ < q)
    (hqB : ‖matrixOperator (compartmentMatrix v y)‖ < q)
    (hA : (physicalCharacteristic t x).eval q ≠ 0)
    (hB : (physicalCharacteristic v y).eval q ≠ 0) :
    physicalRootResponse t x q=physicalRootResponse v y q := by
  let A := compartmentMatrix t x
  let B := compartmentMatrix v y
  let b : Fin (n+1) → ℝ := Pi.single 0 1
  have hdA : (Matrix.scalar (Fin (n+1)) q-A).det ≠ 0 := by rwa [← Matrix.eval_charpoly]
  have hdB : (Matrix.scalar (Fin (n+1)) q-B).det ≠ 0 := by rwa [← Matrix.eval_charpoly]
  have hout := h (fun s => Real.exp (q*s)) (by fun_prop)
    (exponentialODEProbe A b q) (exponentialODEProbe B b q)
    (exponentialODEProbe_ode A b q hdA) (exponentialODEProbe_ode B b q hdB)
    (exponentialODEProbe_initial A b q) (exponentialODEProbe_initial B b q)
  have hlA := exponentialODEProbe_coordinate_limit A b q hqA (0 : Fin (n+1))
  have hlB := exponentialODEProbe_coordinate_limit B b q hqB (0 : Fin (n+1))
  have he : (fun s : ℝ => Real.exp (-q*s)*exponentialODEProbe A b q s 0) =ᶠ[atTop]
      (fun s : ℝ => Real.exp (-q*s)*exponentialODEProbe B b q s 0) :=
    (eventually_ge_atTop (0 : ℝ)).mono (fun s hs => congrArg (fun z => Real.exp (-q*s)*z) (hout s hs))
  have hh := tendsto_nhds_unique (hlA.congr' he) hlB
  simpa only [resolventVector,b,Matrix.mulVec_single_one,Matrix.col_apply,physicalRootResponse,A,B] using hh

/-- Exact transfer cross identity from actual input/output trajectories.
The proof uses infinitely many high exponential probes, not a finite test set. -/
theorem same_continuous_outputs_cross_identity {n : ℕ} (t v : OrderedTree n) (x y : TreeRates n)
    (h : SameContinuousRootOutputs t v x y) :
    physicalRootCofactor t x*physicalCharacteristic v y =
      physicalRootCofactor v y*physicalCharacteristic t x := by
  obtain ⟨a,ha⟩ := Polynomial.exists_max_root (physicalCharacteristic t x) (physicalCharacteristic_monic t x).ne_zero
  obtain ⟨b,hb⟩ := Polynomial.exists_max_root (physicalCharacteristic v y) (physicalCharacteristic_monic v y).ne_zero
  let R := max (max a b) (max ‖matrixOperator (compartmentMatrix t x)‖ ‖matrixOperator (compartmentMatrix v y)‖)
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite R).mono
  intro q hq
  change R < q at hq
  have hqa : a < q := lt_of_le_of_lt (le_trans (le_max_left a b) (le_max_left _ _)) hq
  have hqb : b < q := lt_of_le_of_lt (le_trans (le_max_right a b) (le_max_left _ _)) hq
  have hnA : (physicalCharacteristic t x).eval q ≠ 0 := fun hz => (not_le_of_gt hqa) (ha q hz)
  have hnB : (physicalCharacteristic v y).eval q ≠ 0 := fun hz => (not_le_of_gt hqb) (hb q hz)
  have hqA : ‖matrixOperator (compartmentMatrix t x)‖ < q :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hqB : ‖matrixOperator (compartmentMatrix v y)‖ < q :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have he := same_continuous_outputs_resolvent t v x y h q hqA hqB hnA hnB
  rw [physicalRootResponse_eq,physicalRootResponse_eq] at he
  have hh := (div_eq_div_iff hnA hnB).mp he
  simpa only [Set.mem_setOf_eq,Polynomial.eval_mul] using hh

end HydrologyTree
