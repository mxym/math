import HydrologyTree.LinearForcedODE
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Actual short-time derivatives under a constant continuous input. These
are derivatives of classical trajectories, not assumed transfer coefficients
or idealized impulse inputs. No sign or spectral premise is needed. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma constant_input_velocity {A : Matrix V V ℝ} {b : V → ℝ} {z : ℝ → V → ℝ}
    (hz : IsForcedMatrixSolution A b (fun _ => 1) z) (s : ℝ) :
    HasDerivAt z (A*ᵥz s+b) s := by
  simpa only [one_smul] using hz s

lemma constant_input_power_signal_derivative {A : Matrix V V ℝ} {b : V → ℝ}
    {z : ℝ → V → ℝ} (hz : IsForcedMatrixSolution A b (fun _ => 1) z)
    (k : ℕ) (v : V) (s : ℝ) :
    HasDerivAt (fun t => (A^k*ᵥ(A*ᵥz t+b)) v)
      ((A^(k+1)*ᵥ(A*ᵥz s+b)) v) s := by
  have h1 := ((matrixOperator A).hasFDerivAt.comp_hasDerivAt s
    (constant_input_velocity hz s)).add_const b
  have h2 := (matrixOperator (A^k)).hasFDerivAt.comp_hasDerivAt s h1
  have he := hasDerivAt_pi.mp h2 v
  simpa only [Function.comp_apply,matrixOperator_apply,Matrix.mulVec_mulVec,pow_succ] using he

/-- Every finite Taylor derivative of an actual constant-input solution is a
proved matrix moment. This includes any spectral collisions or hidden modes. -/
theorem constant_input_iterated_output_derivative {A : Matrix V V ℝ} {b : V → ℝ}
    {z : ℝ → V → ℝ} (hz : IsForcedMatrixSolution A b (fun _ => 1) z)
    (k : ℕ) (v : V) :
    iteratedDeriv (k+1) (fun s => z s v) = fun s => (A^k*ᵥ(A*ᵥz s+b)) v := by
  induction k with
  | zero =>
    rw [iteratedDeriv_one]
    funext s
    have he := hasDerivAt_pi.mp (constant_input_velocity hz s) v
    simpa only [pow_zero,Matrix.one_mulVec] using he.deriv
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    funext s
    exact (constant_input_power_signal_derivative hz k v s).deriv

/-- Zero initial state: the k+1 derivative is the k-th actual matrix moment. -/
theorem constant_input_zero_initial_moment {A : Matrix V V ℝ} {b : V → ℝ}
    {z : ℝ → V → ℝ} (hz : IsForcedMatrixSolution A b (fun _ => 1) z) (hz0 : z 0=0)
    (k : ℕ) (v : V) : iteratedDeriv (k+1) (fun s => z s v) 0=(A^k*ᵥb) v := by
  rw [constant_input_iterated_output_derivative hz k v]
  change (A^k*ᵥ(A*ᵥz 0+b)) v=(A^k*ᵥb) v
  rw [hz0,Matrix.mulVec_zero,zero_add]

/-- The measured pair consists only of second and third scalar derivatives. -/
def stepOutputJet (f : ℝ → ℝ) : ℝ × ℝ := (iteratedDeriv 2 f 0,iteratedDeriv 3 f 0)

/-- Inject at v and observe that SAME compartment. A continuous constant input
suffices: no impulse, unobserved coefficient, or fitted eigenvalue is assumed. -/
theorem constant_input_collocated_jet {A : Matrix V V ℝ} (v : V) {z : ℝ → V → ℝ}
    (hz : IsForcedMatrixSolution A (Pi.single v 1) (fun _ => 1) z) (hz0 : z 0=0) :
    stepOutputJet (fun s => z s v)=(A v v,(A*A) v v) := by
  apply Prod.ext
  · have h := constant_input_zero_initial_moment hz hz0 1 v
    simpa only [stepOutputJet,pow_one,Matrix.mulVec_single_one,Matrix.col_apply] using h
  · have h := constant_input_zero_initial_moment hz hz0 2 v
    simpa only [stepOutputJet,pow_two,Matrix.mulVec_single_one,Matrix.col_apply] using h

end HydrologyTree
