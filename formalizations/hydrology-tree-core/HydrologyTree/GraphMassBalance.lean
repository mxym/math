import HydrologyTree.GraphODETransport
import HydrologyTree.PhysicalMassODE

/-! Actual mass balance on any finite simple graph, independently of a tree
presentation. Real rates may be signed; positivity is not needed for conservation. -/
open Matrix MeasureTheory
noncomputable section
namespace HydrologyTree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma graph_single_column_sum (i j w : V) (r : ℝ) :
    (∑ v : V, (Matrix.single i j r) v w) = if j=w then r else 0 := by
  by_cases h : j=w
  · subst w
    simp [Matrix.single_apply]
  · simp [Matrix.single_apply,h]

lemma graphTransfer_column_sum (y : GraphRates G) (d : G.Dart) (w : V) :
    (∑ v : V, graphTransfer y d v w)=0 := by
  simp only [graphTransfer,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,mul_sub,
    Finset.sum_sub_distrib,← Finset.mul_sum,graph_single_column_sum,sub_self]

/-- All internal transfers cancel exactly, with only the specified physical leak. -/
theorem graphCompartment_column_sum (o : V) (y : GraphRates G) (w : V) :
    (∑ v : V, graphCompartmentMatrix G o y v w)=if w=o then -y.1 else 0 := by
  simp only [graphCompartmentMatrix,Matrix.sub_apply,Matrix.sum_apply,Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp only [graphTransfer_column_sum,Finset.sum_const_zero,zero_sub,
    Matrix.smul_apply,smul_eq_mul,← Finset.mul_sum,graph_single_column_sum]
  by_cases h : w=o
  · simp [h]
  · simp [h,Ne.symm h]

theorem graph_total_flux (o : V) (y : GraphRates G) (s : V → ℝ) :
    (∑ v, (graphCompartmentMatrix G o y *ᵥ s) v) = -y.1*s o := by
  simp only [Matrix.mulVec,dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,graphCompartment_column_sum]
  simp

/-- Differential storage balance follows from the independently defined graph ODE. -/
theorem graph_storage_hasDerivAt (o : V) (y : GraphRates G) (u : ℝ → ℝ)
    (z : ℝ → V → ℝ) (hz : IsGraphForcedSolution o y u z) (s : ℝ) :
    HasDerivAt (fun t => ∑ v, z t v) (u s-y.1*z s o) s := by
  have h := (coordinateSumCLM V).hasFDerivAt.comp_hasDerivAt s (hz s)
  apply h.congr_deriv
  change (∑ v, (graphCompartmentMatrix G o y *ᵥ z s+u s • (Pi.single o 1 : V → ℝ)) v)=_
  simp only [Pi.add_apply,Finset.sum_add_distrib,Pi.smul_apply,smul_eq_mul]
  rw [graph_total_flux]
  simp [← Finset.mul_sum]
  ring

/-- Exact integral storage balance, with either orientation of the time interval. -/
theorem graph_storage_integral_balance (o : V) (y : GraphRates G) (u : ℝ → ℝ)
    (hu : Continuous u) (z : ℝ → V → ℝ) (hz : IsGraphForcedSolution o y u z) (a t : ℝ) :
    (∑ v, z t v) = (∑ v, z a v)+∫ s in a..t, (u s-y.1*z s o) := by
  have hzc : Continuous z := continuous_iff_continuousAt.mpr (fun s => (hz s).continuousAt)
  have hc : Continuous (fun s => u s-y.1*z s o) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => graph_storage_hasDerivAt o y u z hz s) (hc.intervalIntegrable a t)
  linarith

end HydrologyTree
