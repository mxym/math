import HydrologyTree.RootModalData
import HydrologyTree.ScalarForcedODE

/-! Explicit actual state trajectories from a proved modal coordinate witness.
The forcing is any continuous real function; the initial state is arbitrary. -/
open Matrix
noncomputable section
namespace HydrologyTree

variable {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}

def modalForcedSolution (M : RootModalData A) (u : ℝ → ℝ) (a : ℝ)
    (z0 : Fin (n+1) → ℝ) (s : ℝ) : Fin (n+1) → ℝ :=
  M.synthesis *ᵥ (fun i => scalarForcedSolution (M.rates i)
    (fun v => M.amplitudes i*u v) a ((M.analysis*ᵥz0) i) s)

@[simp] theorem modalForcedSolution_initial (M : RootModalData A)
    (u : ℝ → ℝ) (a : ℝ) (z0 : Fin (n+1) → ℝ) :
    modalForcedSolution M u a z0 a=z0 := by
  simp only [modalForcedSolution,scalarForcedSolution_initial]
  rw [Matrix.mulVec_mulVec,M.synth_analysis,Matrix.one_mulVec]

/-- The formula satisfies the ORIGINAL matrix differential equation. -/
theorem modalForcedSolution_ode (M : RootModalData A) (u : ℝ → ℝ)
    (hu : Continuous u) (a : ℝ) (z0 : Fin (n+1) → ℝ) :
    IsForcedMatrixSolution A (Pi.single 0 1) u (modalForcedSolution M u a z0) := by
  intro s
  let y : ℝ → Fin (n+1) → ℝ := fun v i => scalarForcedSolution (M.rates i)
    (fun q => M.amplitudes i*u q) a ((M.analysis*ᵥz0) i) v
  have hy : HasDerivAt y (Matrix.diagonal (fun i => -M.rates i)*ᵥy s + u s • M.amplitudes) s := by
    apply hasDerivAt_pi.mpr
    intro i
    convert scalarForcedSolution_hasDerivAt (M.rates i) (fun q => M.amplitudes i*u q)
      (continuous_const.mul hu) a ((M.analysis*ᵥz0) i) s using 1 <;>
      simp [y,Matrix.mulVec, dotProduct, Matrix.diagonal_apply,smul_eq_mul,mul_comm]
  have h := (matrixOperator M.synthesis).hasFDerivAt.comp_hasDerivAt s hy
  apply h.congr_deriv
  exact rootModal_synthesis_rhs M (y s) (u s)

/-- Global existence and uniqueness for any initial state and continuous input. -/
theorem modalForcedSolution_existsUnique (M : RootModalData A)
    (u : ℝ → ℝ) (hu : Continuous u) (a : ℝ) (z0 : Fin (n+1) → ℝ) :
    ∃! z : ℝ → Fin (n+1) → ℝ, IsForcedMatrixSolution A (Pi.single 0 1) u z ∧ z a=z0 := by
  refine ⟨modalForcedSolution M u a z0,⟨modalForcedSolution_ode M u hu a z0,
    modalForcedSolution_initial M u a z0⟩,?_⟩
  intro z hz
  exact forcedMatrixSolution_unique A (Pi.single 0 1) u z (modalForcedSolution M u a z0) a
    hz.1 (modalForcedSolution_ode M u hu a z0)
    (hz.2.trans (modalForcedSolution_initial M u a z0).symm)

/-- The root trajectory for zero initial storage is determined by the modal
rates and squared amplitudes for EVERY input, not only a finite sample. -/
theorem modalForcedSolution_root_zero (M : RootModalData A)
    (u : ℝ → ℝ) (a s : ℝ) :
    (modalForcedSolution M u a 0 s) 0 =
      ∑ i, (M.amplitudes i)^2 * scalarForcedSolution (M.rates i) u a 0 s := by
  rw [modalForcedSolution,M.root_output]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mulVec_zero,Pi.zero_apply]
  have h := scalarForcedSolution_scale (M.rates i) (M.amplitudes i) u a 0 s
  simp only [mul_zero] at h
  rw [h]
  ring

end HydrologyTree
