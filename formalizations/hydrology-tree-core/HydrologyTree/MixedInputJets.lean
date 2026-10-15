import HydrologyTree.ConstantInputJets
import HydrologyTree.PositiveMatrixProbe
import HydrologyTree.LocatedLeakDynamics

/-! Positive mixed-input/mixed-output probes are actual constant-forcing ODE
experiments. The second observed derivative is c^T A b. No impulses are used. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V]

def probeObservation (c : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ v,c v • ContinuousLinearMap.proj v

@[simp] lemma probeObservation_apply (c z : V → ℝ) : probeObservation c z=∑ v,c v*z v := by
  simp [probeObservation]

/-- Actual second derivative under constant input vector b. -/
theorem constant_input_functional_second {A : Matrix V V ℝ} {b : V → ℝ}
    {z : ℝ → V → ℝ} (hz : IsForcedMatrixSolution A b (fun _ => 1) z) (hz0 : z 0=0)
    (L : (V → ℝ) →L[ℝ] ℝ) :
    iteratedDeriv 2 (fun s => L (z s)) 0=L (A*ᵥb) := by
  have h1 : deriv (fun s => L (z s))=fun s => L (A*ᵥz s+b) := by
    funext s
    exact (L.hasFDerivAt.comp_hasDerivAt s (constant_input_velocity hz s)).deriv
  rw [iteratedDeriv_succ,iteratedDeriv_one,h1]
  have hv := ((matrixOperator A).hasFDerivAt.comp_hasDerivAt 0 (constant_input_velocity hz 0)).add_const b
  have he := L.hasFDerivAt.comp_hasDerivAt 0 hv
  change HasDerivAt (fun s => L (A*ᵥz s+b)) (L (A*ᵥ(A*ᵥz 0+b))) 0 at he
  rw [he.deriv,hz0,Matrix.mulVec_zero,zero_add]

theorem mixed_step_second_derivative {A : Matrix V V ℝ} {b : V → ℝ}
    {z : ℝ → V → ℝ} (hz : IsForcedMatrixSolution A b (fun _ => 1) z) (hz0 : z 0=0)
    (c : V → ℝ) :
    iteratedDeriv 2 (fun s => ∑ v,c v*z s v) 0=matrixProbeValue A b c := by
  simpa only [probeObservation_apply,matrixProbeValue] using
    constant_input_functional_second hz hz0 (probeObservation c)

/-- Superposition supplies actual mixed-input solutions from the already
constructed physical single-node experiments. -/
lemma constant_input_basis_superposition (A : Matrix V V ℝ) (b : V → ℝ)
    (z : V → ℝ → V → ℝ)
    (hz : ∀ v,IsForcedMatrixSolution A (Pi.single v 1) (fun _ => 1) (z v)) :
    IsForcedMatrixSolution A b (fun _ => 1) (fun s => ∑ v,b v • z v s) := by
  intro s
  have he := HasDerivAt.sum (u := Finset.univ) (fun v _ =>
    HasDerivAt.const_smul (b v) (constant_input_velocity (hz v) s))
  have hsum : HasDerivAt (fun t => ∑ v,b v • z v t)
      (∑ v,b v • (A*ᵥz v s+Pi.single v 1)) s := by
    convert he using 1
    funext t
    simp only [Finset.sum_apply,Pi.smul_apply]
  apply hsum.congr_deriv
  have hinput : (∑ v : V,b v • Pi.single v (1 : ℝ))=b := by
    ext w
    simp [Pi.single_apply,Pi.smul_apply]
  have hm : (∑ v,b v • (A*ᵥz v s))=A*ᵥ(∑ v,b v • z v s) := by
    change (∑ v,b v • matrixOperator A (z v s))=matrixOperator A (∑ v,b v • z v s)
    rw [map_sum]
    simp only [map_smul]
  simp only [smul_add,Finset.sum_add_distrib,one_smul]
  rw [hm,hinput]

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Existence and uniqueness for the chosen experiment are part of the theorem,
so later identification predicates cannot be true because no solution exists. -/
theorem positive_graph_mixed_step_existsUnique (hG : G.IsTree) (ell : V)
    (x : PositiveGraphRateSpace G) (b : V → ℝ) :
    ∃! z : ℝ → V → ℝ,IsForcedMatrixSolution (graphCompartmentMatrix G ell x.val) b (fun _ => 1) z ∧ z 0=0 := by
  have hv (v : V) : ∃ z : ℝ → V → ℝ,
      IsLocatedGraphSolution v ell x.val (fun _ => 1) z ∧ z 0=0 :=
    (located_forced_ODE_existsUnique hG v ell x (fun _ => 1) continuous_const 0 0).exists
  choose z hz hz0 using hv
  let q : ℝ → V → ℝ := fun s => ∑ v,b v • z v s
  have hq : IsForcedMatrixSolution (graphCompartmentMatrix G ell x.val) b (fun _ => 1) q :=
    constant_input_basis_superposition _ b z hz
  have hq0 : q 0=0 := by simp [q,hz0]
  refine ⟨q,⟨hq,hq0⟩,?_⟩
  intro w hw
  exact forcedMatrixSolution_unique _ b (fun _ => 1) w q 0 hw.1 hq (hw.2.trans hq0.symm)

end HydrologyTree
