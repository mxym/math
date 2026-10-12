import HydrologyTree.PhysicalModalConstruction
import HydrologyTree.ModalForcedODE
import HydrologyTree.StieltjesWeightedMatching
import HydrologyTree.PositiveRateAssembly

/-! Global actual state-equation existence, uniqueness and forced root output.
The modal witness used below is constructed from the original physical matrix. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

abbrev IsPhysicalForcedSolution {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (u : ℝ → ℝ) (z : ℝ → Fin (n+1) → ℝ) : Prop :=
  IsForcedMatrixSolution (compartmentMatrix t x) (Pi.single 0 1) u z

/-- Arbitrary continuous forcing and arbitrary initial physical state. -/
theorem physical_forced_ODE_existsUnique {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : PositiveRateVector x) (u : ℝ → ℝ) (hu : Continuous u)
    (a : ℝ) (z0 : Fin (n+1) → ℝ) :
    ∃! z : ℝ → Fin (n+1) → ℝ, IsPhysicalForcedSolution t x u z ∧ z a=z0 := by
  obtain ⟨M,_,_,_⟩ := physical_root_modal_representation t x (hx.1 0) (fun e => hx.1 e.succ) hx.2
  exact modalForcedSolution_existsUnique M u hu a z0

/-- Any actual zero-initial trajectory has the full target's forced root output.
No extra observation of internal states or modal coordinates is assumed. -/
theorem physical_forced_root_formula {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : PositiveRateVector x) (r w : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (hP : physicalCharacteristic t x=stieltjesDenominator r)
    (hF : physicalRootCofactor t x=stieltjesNumerator r w)
    (u : ℝ → ℝ) (hu : Continuous u) (a : ℝ) (z : ℝ → Fin (n+1) → ℝ)
    (hz : IsPhysicalForcedSolution t x u z) (hz0 : z a=0) (s : ℝ) :
    z s 0=∑ i, w i*scalarForcedSolution (r i) u a 0 s := by
  obtain ⟨M,_,hMP,hMF⟩ := physical_root_modal_representation t x (hx.1 0) (fun e => hx.1 e.succ) hx.2
  have he : z=modalForcedSolution M u a 0 :=
    forcedMatrixSolution_unique (compartmentMatrix t x) (Pi.single 0 1) u z
      (modalForcedSolution M u a 0) a hz (modalForcedSolution_ode M u hu a 0)
      (hz0.trans (modalForcedSolution_initial M u a 0).symm)
  rw [he,modalForcedSolution_root_zero]
  exact stieltjes_weighted_sum_congr M.rates r (fun i => (M.amplitudes i)^2) w hr
    (hMP.symm.trans hP) (hMF.symm.trans hF) (fun q => scalarForcedSolution q u a 0 s)

end HydrologyTree
