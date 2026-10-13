import HydrologyTree.ExponentialGramian
import HydrologyTree.ModalForcedODE

/-! Explicit finite-horizon steering by actual continuous controls. Controls
are real-valued, as in linear controllability; nonnegative-only control is NOT
asserted. All initial and terminal physical state vectors are allowed. -/
open Matrix
noncomputable section
namespace HydrologyTree

variable {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}

lemma scalar_exponentialSignal_terminal (r c : Fin (n+1) → ℝ)
    (k y0 T : ℝ) (i : Fin (n+1)) :
    scalarForcedSolution (r i) (fun s => k*exponentialSignal r c s) 0 y0 T =
      Real.exp (-r i*T)*(y0+k*(exponentialGramian r T*ᵥc) i) := by
  simp only [scalarForcedSolution,sub_zero,exponentialGramian_mulVec]
  have he : (fun s : ℝ => Real.exp (r i*s)*(k*exponentialSignal r c s)) =
      (fun s : ℝ => k*(Real.exp (r i*s)*exponentialSignal r c s)) := by funext s; ring
  rw [he,intervalIntegral.integral_const_mul]

def modalSteeringTarget (M : RootModalData A) (T : ℝ)
    (z0 z1 : Fin (n+1) → ℝ) : Fin (n+1) → ℝ := fun i =>
  (Real.exp (M.rates i*T)*(M.analysis*ᵥz1) i - (M.analysis*ᵥz0) i)/M.amplitudes i

def modalSteeringCoefficients (M : RootModalData A) (T : ℝ)
    (z0 z1 : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  (exponentialGramian M.rates T)⁻¹*ᵥmodalSteeringTarget M T z0 z1

def modalSteeringInput (M : RootModalData A) (T : ℝ)
    (z0 z1 : Fin (n+1) → ℝ) : ℝ → ℝ :=
  exponentialSignal M.rates (modalSteeringCoefficients M T z0 z1)

lemma modalSteering_gramian_equation (M : RootModalData A) (hr : Function.Injective M.rates)
    (T : ℝ) (hT : 0 < T) (z0 z1 : Fin (n+1) → ℝ) :
    exponentialGramian M.rates T*ᵥmodalSteeringCoefficients M T z0 z1=modalSteeringTarget M T z0 z1 := by
  rw [modalSteeringCoefficients,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_gt (exponentialGramian_posDef M.rates hr T hT).det_pos)),
    Matrix.one_mulVec]

/-- The constructed control reaches the exact target at every positive horizon. -/
theorem modalSteering_terminal (M : RootModalData A) (hr : Function.Injective M.rates)
    (hk : ∀ i, M.amplitudes i ≠ 0) (T : ℝ) (hT : 0 < T) (z0 z1 : Fin (n+1) → ℝ) :
    modalForcedSolution M (modalSteeringInput M T z0 z1) 0 z0 T=z1 := by
  have hG := modalSteering_gramian_equation M hr T hT z0 z1
  have he : (fun i => scalarForcedSolution (M.rates i)
      (fun s => M.amplitudes i*modalSteeringInput M T z0 z1 s) 0 ((M.analysis*ᵥz0) i) T) = M.analysis*ᵥz1 := by
    funext i
    rw [modalSteeringInput,scalar_exponentialSignal_terminal,hG]
    dsimp only [modalSteeringTarget]
    rw [mul_div_cancel₀ _ (hk i)]
    have hc := scalarIntegratingFactor_cancel (M.rates i) 0 T
    simp only [sub_zero] at hc
    calc
      _ = (Real.exp (-M.rates i*T)*Real.exp (M.rates i*T))*(M.analysis*ᵥz1) i := by ring
      _ = _ := by rw [hc,one_mul]
  rw [modalForcedSolution,he,Matrix.mulVec_mulVec,M.synth_analysis,Matrix.one_mulVec]

/-- Actual continuous-time controllability, not just a Kalman rank statement.
For every T>0 and every initial/final state, a continuous real input and its
unique global classical trajectory are constructed. -/
theorem modal_finite_horizon_steering (M : RootModalData A) (hr : Function.Injective M.rates)
    (hk : ∀ i, M.amplitudes i ≠ 0) (T : ℝ) (hT : 0 < T) (z0 z1 : Fin (n+1) → ℝ) :
    ∃ u : ℝ → ℝ, Continuous u ∧
      ∃! z : ℝ → Fin (n+1) → ℝ, IsForcedMatrixSolution A (Pi.single 0 1) u z ∧ z 0=z0 ∧ z T=z1 := by
  let u := modalSteeringInput M T z0 z1
  have hu : Continuous u := continuous_exponentialSignal _ _
  refine ⟨u,hu,modalForcedSolution M u 0 z0,?_,?_⟩
  · exact ⟨modalForcedSolution_ode M u hu 0 z0,modalForcedSolution_initial M u 0 z0,
      modalSteering_terminal M hr hk T hT z0 z1⟩
  · intro z hz
    exact forcedMatrixSolution_unique A (Pi.single 0 1) u z (modalForcedSolution M u 0 z0) 0
      hz.1 (modalForcedSolution_ode M u hu 0 z0)
      (hz.2.1.trans (modalForcedSolution_initial M u 0 z0).symm)

end HydrologyTree
