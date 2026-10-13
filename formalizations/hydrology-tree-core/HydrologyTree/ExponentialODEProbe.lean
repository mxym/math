import HydrologyTree.MatrixFlow
import HydrologyTree.ScalarForcedODE
import HydrologyTree.Resolvent

/-! Exact exponential input probes for arbitrary real matrices. The recovered
quantity is the actual resolvent, with its domain of invertibility checked. -/
open Matrix Filter
open scoped Topology
noncomputable section
namespace HydrologyTree

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma scalar_mulVec_eq_smul (q : ℝ) (z : I → ℝ) : Matrix.scalar I q *ᵥ z=q • z := by
  ext i
  simp [Matrix.scalar_apply,Matrix.mulVec,dotProduct,Matrix.diagonal_apply]

def resolventVector (A : Matrix I I ℝ) (b : I → ℝ) (q : ℝ) : I → ℝ :=
  (Matrix.scalar I q-A)⁻¹ *ᵥ b

lemma resolventVector_equation (A : Matrix I I ℝ) (b : I → ℝ) (q : ℝ)
    (hq : (Matrix.scalar I q-A).det ≠ 0) :
    q • resolventVector A b q-A*ᵥresolventVector A b q=b := by
  have h : (Matrix.scalar I q-A)*ᵥresolventVector A b q=b := by
    rw [resolventVector,Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hq),Matrix.one_mulVec]
  simpa only [Matrix.sub_mulVec,scalar_mulVec_eq_smul] using h

def exponentialODEProbe (A : Matrix I I ℝ) (b : I → ℝ) (q s : ℝ) : I → ℝ :=
  Real.exp (q*s) • resolventVector A b q - matrixFlow A s (resolventVector A b q)

@[simp] theorem exponentialODEProbe_initial (A : Matrix I I ℝ) (b : I → ℝ) (q : ℝ) :
    exponentialODEProbe A b q 0=0 := by simp [exponentialODEProbe]

/-- A genuine zero-initial solution for the positive smooth input exp(q*s). -/
theorem exponentialODEProbe_ode (A : Matrix I I ℝ) (b : I → ℝ) (q : ℝ)
    (hq : (Matrix.scalar I q-A).det ≠ 0) :
    IsForcedMatrixSolution A b (fun s => Real.exp (q*s)) (exponentialODEProbe A b q) := by
  intro s
  have h := ((((hasDerivAt_id s).const_mul q).exp).smul_const (resolventVector A b q)).sub
    (matrixFlow_hasDerivAt A (resolventVector A b q) s)
  apply h.congr_deriv
  simp only [exponentialODEProbe,Matrix.mulVec_sub,Matrix.mulVec_smul,id_eq,mul_one]
  ext i
  have hv := congrFun (resolventVector_equation A b q hq) i
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hv ⊢
  linear_combination Real.exp (q*s)*hv

/-- The scaled actual trajectory tends to the true resolvent vector. -/
theorem exponentialODEProbe_scaled_limit (A : Matrix I I ℝ) (b : I → ℝ) (q : ℝ)
    (hq : ‖matrixOperator A‖ < q) :
    Tendsto (fun s : ℝ => Real.exp (-q*s) • exponentialODEProbe A b q s)
      atTop (𝓝 (resolventVector A b q)) := by
  have h : Tendsto (fun s : ℝ => resolventVector A b q -
      Real.exp (-q*s) • matrixFlow A s (resolventVector A b q)) atTop
      (𝓝 (resolventVector A b q-0)) :=
    tendsto_const_nhds.sub (matrixFlow_scaled_tendsto_zero A (resolventVector A b q) q hq)
  have he (s : ℝ) : Real.exp (-q*s) • exponentialODEProbe A b q s =
      resolventVector A b q - Real.exp (-q*s) • matrixFlow A s (resolventVector A b q) := by
    rw [exponentialODEProbe,smul_sub,smul_smul]
    have hc : Real.exp (-q*s)*Real.exp (q*s)=1 := by
      simpa using scalarIntegratingFactor_cancel q 0 s
    rw [hc,one_smul]
  simpa only [sub_zero,← he] using h

/-- Every observed coordinate has the corresponding exact asymptotic response. -/
theorem exponentialODEProbe_coordinate_limit (A : Matrix I I ℝ) (b : I → ℝ) (q : ℝ)
    (hq : ‖matrixOperator A‖ < q) (o : I) :
    Tendsto (fun s : ℝ => Real.exp (-q*s)*exponentialODEProbe A b q s o)
      atTop (𝓝 (resolventVector A b q o)) := by
  exact ((continuous_apply o).tendsto (resolventVector A b q)).comp (exponentialODEProbe_scaled_limit A b q hq)

end HydrologyTree
