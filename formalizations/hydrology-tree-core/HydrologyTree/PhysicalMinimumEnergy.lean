import HydrologyTree.ModalMinimumEnergy
import HydrologyTree.PhysicalControllability
import HydrologyTree.PhysicalForcedODE

/-! Unconditional optimal control theorem for the actual tree model. Signed
continuous controls and arbitrary real state endpoints are permitted. This is
not a claim about arbitrary steering with nonnegative rainfall alone. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

/-- The complete simple modal witness is constructed from the actual target
response; neither modal decomposition nor nonzero amplitudes is assumed. -/
theorem real_full_response_simple_modal_data {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (hx : HasStieltjesRootResponse t x r w) :
    ∃ M : RootModalData (compartmentMatrix t x), Function.Injective M.rates ∧
      ∀ i, M.amplitudes i ≠ 0 := by
  obtain ⟨hP,hF⟩ := (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x).mp hx
  have hp := real_stieltjes_realization_is_positive t x r w hr hpos hw hm hP hF
  obtain ⟨M,_,hMP,hMF⟩ := physical_root_modal_representation t x (hp.1 0) (fun e => hp.1 e.succ) hp.2
  obtain ⟨e,he,hweights⟩ := stieltjes_pair_matching M.rates r (fun i => (M.amplitudes i)^2) w hr
    (hMP.symm.trans hP) (hMF.symm.trans hF)
  refine ⟨M,?_,?_⟩
  · intro i j hij
    apply e.injective
    apply hr
    rwa [← he i,← he j]
  · intro i hi
    have h := hw (e i)
    rw [← hweights i,hi] at h
    norm_num at h

/-- Actual finite-horizon optimal steering: a continuous minimizing control,
its unique global classical state trajectory, and the exact energy gap for
EVERY continuous competing control with the same physical endpoints. -/
theorem real_full_response_minimum_energy_control {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (hx : HasStieltjesRootResponse t x r w)
    (T : ℝ) (hT : 0 < T) (z0 z1 : Fin (n+1) → ℝ) :
    ∃ u0 : ℝ → ℝ, Continuous u0 ∧
      (∃! z : ℝ → Fin (n+1) → ℝ,
        IsPhysicalForcedSolution t x u0 z ∧ z 0=z0 ∧ z T=z1) ∧
      ∀ (u : ℝ → ℝ), Continuous u → ∀ z : ℝ → Fin (n+1) → ℝ,
        IsPhysicalForcedSolution t x u z → z 0=z0 → z T=z1 →
        controlEnergy T u=controlEnergy T u0+controlEnergy T (fun s => u s-u0 s) ∧
        controlEnergy T u0 ≤ controlEnergy T u ∧
        (controlEnergy T u=controlEnergy T u0 ↔ ∀ s ∈ Set.Icc 0 T, u s=u0 s) := by
  obtain ⟨M,hMr,hMk⟩ := real_full_response_simple_modal_data t x r w hr hpos hw hm hx
  let u0 := modalSteeringInput M T z0 z1
  have hu0 : Continuous u0 := continuous_exponentialSignal _ _
  refine ⟨u0,hu0,?_,?_⟩
  · refine ⟨modalForcedSolution M u0 0 z0,?_,?_⟩
    · exact ⟨modalForcedSolution_ode M u0 hu0 0 z0,modalForcedSolution_initial M u0 0 z0,
        modalSteering_terminal M hMr hMk T hT z0 z1⟩
    · intro z hz
      exact forcedMatrixSolution_unique (compartmentMatrix t x) (Pi.single 0 1) u0 z
        (modalForcedSolution M u0 0 z0) 0 hz.1 (modalForcedSolution_ode M u0 hu0 0 z0)
        (hz.2.1.trans (modalForcedSolution_initial M u0 0 z0).symm)
  · intro u hu z hz h0 h1
    have hval : controlEnergy T u0=modalMinimumEnergy M T z0 z1 :=
      modalSteeringInput_energy M hMr T hT z0 z1
    rw [hval]
    exact ⟨modal_steering_exact_energy_gap M hMr hMk T hT z0 z1 u hu z hz h0 h1,
      modal_steering_optimal_and_rigid M hMr hMk T hT z0 z1 u hu z hz h0 h1⟩

end HydrologyTree
