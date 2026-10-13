import HydrologyTree.ContinuousOutputFiber

/-! Reverse identification from actual discharge histories, including recovery
of an uncalibrated leak. Continuous forcing and actual classical solutions only. -/
open Matrix Polynomial Filter
open scoped Topology
noncomputable section
namespace HydrologyTree

def SameContinuousDischargeOutputs {n : ℕ} (t v : OrderedTree n) (x y : TreeRates n) : Prop :=
  ∀ (u : ℝ → ℝ), Continuous u → ∀ z q : ℝ → Fin (n+1) → ℝ,
    IsPhysicalForcedSolution t x u z → IsPhysicalForcedSolution v y u q →
    z 0=0 → q 0=0 → ∀ s : ℝ, 0 ≤ s → x.1 0*z s 0=y.1 0*q s 0

lemma same_continuous_discharge_resolvent {n : ℕ} (t v : OrderedTree n) (x y : TreeRates n)
    (h : SameContinuousDischargeOutputs t v x y) (q : ℝ)
    (hqA : ‖matrixOperator (compartmentMatrix t x)‖ < q)
    (hqB : ‖matrixOperator (compartmentMatrix v y)‖ < q)
    (hA : (physicalCharacteristic t x).eval q ≠ 0)
    (hB : (physicalCharacteristic v y).eval q ≠ 0) :
    physicalDischargeResponse t x q=physicalDischargeResponse v y q := by
  let A := compartmentMatrix t x
  let B := compartmentMatrix v y
  let b : Fin (n+1) → ℝ := Pi.single 0 1
  have hdA : (Matrix.scalar (Fin (n+1)) q-A).det ≠ 0 := by rwa [← Matrix.eval_charpoly]
  have hdB : (Matrix.scalar (Fin (n+1)) q-B).det ≠ 0 := by rwa [← Matrix.eval_charpoly]
  have hout := h (fun s => Real.exp (q*s)) (by fun_prop)
    (exponentialODEProbe A b q) (exponentialODEProbe B b q)
    (exponentialODEProbe_ode A b q hdA) (exponentialODEProbe_ode B b q hdB)
    (exponentialODEProbe_initial A b q) (exponentialODEProbe_initial B b q)
  have hlA := (exponentialODEProbe_coordinate_limit A b q hqA (0 : Fin (n+1))).const_mul (x.1 0)
  have hlB := (exponentialODEProbe_coordinate_limit B b q hqB (0 : Fin (n+1))).const_mul (y.1 0)
  have he : (fun s : ℝ => x.1 0*(Real.exp (-q*s)*exponentialODEProbe A b q s 0)) =ᶠ[atTop]
      (fun s : ℝ => y.1 0*(Real.exp (-q*s)*exponentialODEProbe B b q s 0)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    have hh := congrArg (fun z => Real.exp (-q*s)*z) (hout s hs)
    simpa only [mul_left_comm] using hh
  have hh := tendsto_nhds_unique (hlA.congr' he) hlB
  simpa only [resolventVector,b,Matrix.mulVec_single_one,Matrix.col_apply,
    physicalDischargeResponse,physicalRootResponse,A,B] using hh

/-- The unknown actual leak is identified from discharge ODE histories, even
for competing real vectors with no sign or regularity assumptions. -/
theorem same_continuous_discharge_leak {n : ℕ} (t v : OrderedTree n) (x y : TreeRates n)
    (h : SameContinuousDischargeOutputs t v x y) : x.1 0=y.1 0 := by
  have hcross : C (x.1 0)*physicalRootCofactor t x*physicalCharacteristic v y =
      C (y.1 0)*physicalRootCofactor v y*physicalCharacteristic t x := by
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
    have he := same_continuous_discharge_resolvent t v x y h q hqA hqB hnA hnB
    simp only [physicalDischargeResponse,physicalRootResponse_eq,← mul_div_assoc] at he
    simpa only [Set.mem_setOf_eq,Polynomial.eval_mul,Polynomial.eval_C] using (div_eq_div_iff hnA hnB).mp he
  have hl := congrArg Polynomial.leadingCoeff hcross
  simpa only [Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_C,
    (physicalRootCofactor_monic t x).leadingCoeff,(physicalRootCofactor_monic v y).leadingCoeff,
    (physicalCharacteristic_monic t x).leadingCoeff,(physicalCharacteristic_monic v y).leadingCoeff,mul_one] using hl

end HydrologyTree
