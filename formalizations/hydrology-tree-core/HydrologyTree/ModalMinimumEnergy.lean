import HydrologyTree.MinimumEnergyMoments
import HydrologyTree.ModalSteering

/-! Exact minimum control energy for actual state transfer, not for assumed
moment constraints. Every feasible classical trajectory is proved to satisfy
those constraints. Equality is classified on the closed control interval. -/
open Matrix MeasureTheory
noncomputable section
namespace HydrologyTree

lemma scalarForcedSolution_integral_moment (r k : ℝ) (u : ℝ → ℝ) (y0 T : ℝ) :
    scalarForcedSolution r (fun s => k*u s) 0 y0 T =
      Real.exp (-r*T)*(y0+k*(∫ s in 0..T, Real.exp (r*s)*u s)) := by
  simp only [scalarForcedSolution,sub_zero]
  have he : (fun s : ℝ => Real.exp (r*s)*(k*u s)) =
      (fun s : ℝ => k*(Real.exp (r*s)*u s)) := by funext s; ring
  rw [he,intervalIntegral.integral_const_mul]

/-- An actual scalar endpoint is equivalent to its exact exponential moment. -/
theorem scalarForcedSolution_terminal_iff_moment (r k : ℝ) (hk : k ≠ 0)
    (u : ℝ → ℝ) (y0 y1 T : ℝ) :
    scalarForcedSolution r (fun s => k*u s) 0 y0 T=y1 ↔
      (∫ s in 0..T, Real.exp (r*s)*u s)=(Real.exp (r*T)*y1-y0)/k := by
  rw [scalarForcedSolution_integral_moment]
  have hc : Real.exp (r*T)*Real.exp (-r*T)=1 := by
    simpa only [sub_zero,mul_comm] using scalarIntegratingFactor_cancel r 0 T
  constructor
  · intro h
    have h1 := congrArg (fun q : ℝ => Real.exp (r*T)*q) h
    rw [← mul_assoc,hc,one_mul] at h1
    apply (eq_div_iff hk).mpr
    linarith
  · intro h
    rw [h,mul_div_cancel₀ _ hk]
    calc
      _ = (Real.exp (-r*T)*Real.exp (r*T))*y1 := by ring
      _ = y1 := by rw [mul_comm (Real.exp (-r*T)),hc,one_mul]

variable {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}

/-- Every actual endpoint-feasible trajectory supplies the exact moment
constraints needed by the global variational theorem. -/
theorem actual_terminal_implies_moments (M : RootModalData A)
    (hk : ∀ i, M.amplitudes i ≠ 0) (T : ℝ) (z0 z1 : Fin (n+1) → ℝ)
    (u : ℝ → ℝ) (hu : Continuous u) (z : ℝ → Fin (n+1) → ℝ)
    (hz : IsForcedMatrixSolution A (Pi.single 0 1) u z) (h0 : z 0=z0) (hT : z T=z1) :
    HasExponentialMoments M.rates (modalSteeringTarget M T z0 z1) T u := by
  have he : z=modalForcedSolution M u 0 z0 :=
    forcedMatrixSolution_unique A (Pi.single 0 1) u z (modalForcedSolution M u 0 z0) 0
      hz (modalForcedSolution_ode M u hu 0 z0)
      (h0.trans (modalForcedSolution_initial M u 0 z0).symm)
  have hterminal : modalForcedSolution M u 0 z0 T=z1 := (congrFun he T).symm.trans hT
  have ha := congrArg (fun v : Fin (n+1) → ℝ => M.analysis*ᵥv) hterminal
  rw [modalForcedSolution,Matrix.mulVec_mulVec,M.analysis_synth,Matrix.one_mulVec] at ha
  intro i
  have hi := congrFun ha i
  exact (scalarForcedSolution_terminal_iff_moment (M.rates i) (M.amplitudes i) (hk i)
    u ((M.analysis*ᵥz0) i) ((M.analysis*ᵥz1) i) T).mp hi

lemma modalSteeringInput_eq_minimumEnergy (M : RootModalData A) (T : ℝ)
    (z0 z1 : Fin (n+1) → ℝ) :
    modalSteeringInput M T z0 z1=minimumEnergyInput M.rates (modalSteeringTarget M T z0 z1) T := rfl

def modalMinimumEnergy (M : RootModalData A) (T : ℝ) (z0 z1 : Fin (n+1) → ℝ) : ℝ :=
  modalSteeringTarget M T z0 z1 ⬝ᵥ ((exponentialGramian M.rates T)⁻¹*ᵥmodalSteeringTarget M T z0 z1)

/-- Exact optimum value, attained by the constructed physical steering input. -/
theorem modalSteeringInput_energy (M : RootModalData A) (hr : Function.Injective M.rates)
    (T : ℝ) (hT : 0 < T) (z0 z1 : Fin (n+1) → ℝ) :
    controlEnergy T (modalSteeringInput M T z0 z1)=modalMinimumEnergy M T z0 z1 :=
  minimumEnergyInput_energy _ _ hr T hT

/-- The full energy gap identity holds for EVERY actual classical trajectory
with the two endpoints. The moment equations are proved from that trajectory. -/
theorem modal_steering_exact_energy_gap (M : RootModalData A) (hr : Function.Injective M.rates)
    (hk : ∀ i, M.amplitudes i ≠ 0) (T : ℝ) (hT : 0 < T) (z0 z1 : Fin (n+1) → ℝ)
    (u : ℝ → ℝ) (hu : Continuous u) (z : ℝ → Fin (n+1) → ℝ)
    (hz : IsForcedMatrixSolution A (Pi.single 0 1) u z) (h0 : z 0=z0) (h1 : z T=z1) :
    controlEnergy T u=modalMinimumEnergy M T z0 z1+
      controlEnergy T (fun s => u s-modalSteeringInput M T z0 z1 s) :=
  minimumEnergyInput_exact_gap _ _ hr T hT u hu (actual_terminal_implies_moments M hk T z0 z1 u hu z hz h0 h1)

/-- Global optimum and complete equality classification for actual state steering.
Only the target-time interval is identified; no condition is imposed elsewhere. -/
theorem modal_steering_optimal_and_rigid (M : RootModalData A) (hr : Function.Injective M.rates)
    (hk : ∀ i, M.amplitudes i ≠ 0) (T : ℝ) (hT : 0 < T) (z0 z1 : Fin (n+1) → ℝ)
    (u : ℝ → ℝ) (hu : Continuous u) (z : ℝ → Fin (n+1) → ℝ)
    (hz : IsForcedMatrixSolution A (Pi.single 0 1) u z) (h0 : z 0=z0) (h1 : z T=z1) :
    modalMinimumEnergy M T z0 z1 ≤ controlEnergy T u ∧
      (controlEnergy T u=modalMinimumEnergy M T z0 z1 ↔
        ∀ s ∈ Set.Icc 0 T, u s=modalSteeringInput M T z0 z1 s) := by
  have hm := actual_terminal_implies_moments M hk T z0 z1 u hu z hz h0 h1
  exact ⟨minimumEnergyInput_optimal _ _ hr T hT u hu hm,
    minimumEnergyInput_equality_iff _ _ hr T hT u hu hm⟩

/-- The exact cost is independent of the chosen modal coordinates: both sides
are minima for the same actual state equation and the same physical endpoints. -/
theorem modalMinimumEnergy_independent_of_witness (M N : RootModalData A)
    (hMr : Function.Injective M.rates) (hMk : ∀ i, M.amplitudes i ≠ 0)
    (hNr : Function.Injective N.rates) (hNk : ∀ i, N.amplitudes i ≠ 0)
    (T : ℝ) (hT : 0 < T) (z0 z1 : Fin (n+1) → ℝ) :
    modalMinimumEnergy M T z0 z1=modalMinimumEnergy N T z0 z1 := by
  have hMN : modalMinimumEnergy M T z0 z1 ≤ modalMinimumEnergy N T z0 z1 := by
    have h := (modal_steering_optimal_and_rigid M hMr hMk T hT z0 z1
      (modalSteeringInput N T z0 z1) (continuous_exponentialSignal _ _)
      (modalForcedSolution N (modalSteeringInput N T z0 z1) 0 z0)
      (modalForcedSolution_ode N _ (continuous_exponentialSignal _ _) 0 z0)
      (modalForcedSolution_initial N _ 0 z0) (modalSteering_terminal N hNr hNk T hT z0 z1)).1
    rwa [modalSteeringInput_energy N hNr T hT z0 z1] at h
  have hNM : modalMinimumEnergy N T z0 z1 ≤ modalMinimumEnergy M T z0 z1 := by
    have h := (modal_steering_optimal_and_rigid N hNr hNk T hT z0 z1
      (modalSteeringInput M T z0 z1) (continuous_exponentialSignal _ _)
      (modalForcedSolution M (modalSteeringInput M T z0 z1) 0 z0)
      (modalForcedSolution_ode M _ (continuous_exponentialSignal _ _) 0 z0)
      (modalForcedSolution_initial M _ 0 z0) (modalSteering_terminal M hMr hMk T hT z0 z1)).1
    rwa [modalSteeringInput_energy M hMr T hT z0 z1] at h
  exact le_antisymm hMN hNM

end HydrologyTree
