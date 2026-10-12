import HydrologyTree.LinearForcedODE
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Actual homogeneous matrix flow for ARBITRARY real matrices, and a proved
forward growth bound. No stability, real spectrum or positivity is assumed. -/
open Matrix Filter
open scoped Topology
noncomputable section
namespace HydrologyTree

variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixFlow (A : Matrix I I ℝ) (s : ℝ) : (I → ℝ) →L[ℝ] (I → ℝ) :=
  NormedSpace.exp (s • matrixOperator A)

@[simp] theorem matrixFlow_zero (A : Matrix I I ℝ) (z : I → ℝ) : matrixFlow A 0 z=z := by
  simp [matrixFlow]

theorem matrixFlow_hasDerivAt (A : Matrix I I ℝ) (z : I → ℝ) (s : ℝ) :
    HasDerivAt (fun v => matrixFlow A v z) (A *ᵥ matrixFlow A s z) s := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (matrixOperator A) s).clm_apply
    (hasDerivAt_const s z)
  simpa [matrixFlow,ContinuousLinearMap.mul_apply] using h

/-- A global forward bound obtained from the actual ODE by Gronwall. -/
theorem matrixFlow_norm_bound (A : Matrix I I ℝ) (z : I → ℝ) (s : ℝ) (hs : 0 ≤ s) :
    ‖matrixFlow A s z‖ ≤ ‖z‖*Real.exp (‖matrixOperator A‖*s) := by
  have hc : Continuous (fun v => matrixFlow A v z) :=
    continuous_iff_continuousAt.mpr (fun v => (matrixFlow_hasDerivAt A z v).continuousAt)
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (a := 0) (b := s)
    (δ := ‖z‖) (K := ‖matrixOperator A‖) (ε := 0) hc.continuousOn
    (fun v _ => (matrixFlow_hasDerivAt A z v).hasDerivWithinAt)
    (by simp) (fun v _ => by simpa using (matrixOperator A).le_opNorm (matrixFlow A v z))
  simpa only [sub_zero,gronwallBound_ε0] using h s ⟨hs,le_rfl⟩

/-- Exponential rescaling kills every homogeneous transient when the probing
exponent exceeds the actual operator norm, even for unstable real matrices. -/
theorem matrixFlow_scaled_tendsto_zero (A : Matrix I I ℝ) (z : I → ℝ) (q : ℝ)
    (hq : ‖matrixOperator A‖ < q) :
    Tendsto (fun s : ℝ => Real.exp (-q*s) • matrixFlow A s z) atTop (𝓝 0) := by
  have hl : Tendsto (fun s : ℝ => (‖matrixOperator A‖-q)*s) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (sub_neg.mpr hq)).mpr tendsto_id
  have he : Tendsto (fun s : ℝ => ‖z‖*Real.exp ((‖matrixOperator A‖-q)*s)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hl)
  apply squeeze_zero_norm' ((eventually_ge_atTop (0 : ℝ)).mono (fun s hs => ?_)) he
  rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (-q*s)*(‖z‖*Real.exp (‖matrixOperator A‖*s)) :=
      mul_le_mul_of_nonneg_left (matrixFlow_norm_bound A z s hs) (Real.exp_pos _).le
    _ = ‖z‖*(Real.exp (-q*s)*Real.exp (‖matrixOperator A‖*s)) := by ring
    _ = ‖z‖*Real.exp ((‖matrixOperator A‖-q)*s) := by
      rw [← Real.exp_add]
      congr 2
      ring

end HydrologyTree
