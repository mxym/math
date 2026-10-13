import HydrologyTree.ExponentialODEProbe
import HydrologyTree.DiagonalGauge
import Mathlib.Order.Interval.Set.Infinite

/-! Actual all-continuous-input collocated output equality identifies transfer
functions for arbitrary real matrices. Explicit exponential probe trajectories
prevent vacuous reliance on existence, positivity, or spectral stability. -/
open Matrix Polynomial Filter
open scoped Topology
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V]

def SameMatrixContinuousRootOutputs (A B : Matrix V V ℝ) (o : V) : Prop :=
  ∀ u : ℝ → ℝ, Continuous u → ∀ z q : ℝ → V → ℝ,
    IsForcedMatrixSolution A (Pi.single o 1) u z → IsForcedMatrixSolution B (Pi.single o 1) u q →
    z 0=0 → q 0=0 → ∀ s : ℝ,0≤s → z s o=q s o

lemma same_matrix_outputs_resolvent (A B : Matrix V V ℝ) (o : V)
    (h : SameMatrixContinuousRootOutputs A B o) (q : ℝ)
    (hqA : ‖matrixOperator A‖<q) (hqB : ‖matrixOperator B‖<q)
    (hA : A.charpoly.eval q ≠ 0) (hB : B.charpoly.eval q ≠ 0) :
    (Matrix.scalar V q-A)⁻¹ o o=(Matrix.scalar V q-B)⁻¹ o o := by
  let b : V → ℝ := Pi.single o 1
  have hdA : (Matrix.scalar V q-A).det ≠ 0 := by rwa [← Matrix.eval_charpoly]
  have hdB : (Matrix.scalar V q-B).det ≠ 0 := by rwa [← Matrix.eval_charpoly]
  have hout := h (fun s => Real.exp (q*s)) (by fun_prop)
    (exponentialODEProbe A b q) (exponentialODEProbe B b q)
    (exponentialODEProbe_ode A b q hdA) (exponentialODEProbe_ode B b q hdB)
    (exponentialODEProbe_initial A b q) (exponentialODEProbe_initial B b q)
  have hlA := exponentialODEProbe_coordinate_limit A b q hqA o
  have hlB := exponentialODEProbe_coordinate_limit B b q hqB o
  have he : (fun s : ℝ => Real.exp (-q*s)*exponentialODEProbe A b q s o) =ᶠ[atTop]
      (fun s : ℝ => Real.exp (-q*s)*exponentialODEProbe B b q s o) :=
    (eventually_ge_atTop (0 : ℝ)).mono (fun s hs => congrArg (fun z => Real.exp (-q*s)*z) (hout s hs))
  have hh := tendsto_nhds_unique (hlA.congr' he) hlB
  simpa only [resolventVector,b,Matrix.mulVec_single_one,Matrix.col_apply] using hh

/-- Exact full polynomial cross identity, from infinitely many genuine
positive exponential-input experiments, not a finite numerical test set. -/
theorem same_matrix_outputs_cross_identity (A B : Matrix V V ℝ) (o : V)
    (h : SameMatrixContinuousRootOutputs A B o) :
    diagonalCofactor A o*B.charpoly=diagonalCofactor B o*A.charpoly := by
  obtain ⟨a,ha⟩ := Polynomial.exists_max_root A.charpoly (Matrix.charpoly_monic A).ne_zero
  obtain ⟨b,hb⟩ := Polynomial.exists_max_root B.charpoly (Matrix.charpoly_monic B).ne_zero
  let R := max (max a b) (max ‖matrixOperator A‖ ‖matrixOperator B‖)
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite R).mono
  intro q hq
  change R<q at hq
  have hqa : a<q := lt_of_le_of_lt (le_trans (le_max_left a b) (le_max_left _ _)) hq
  have hqb : b<q := lt_of_le_of_lt (le_trans (le_max_right a b) (le_max_left _ _)) hq
  have hnA : A.charpoly.eval q ≠ 0 := fun hz => (not_le_of_gt hqa) (ha q hz)
  have hnB : B.charpoly.eval q ≠ 0 := fun hz => (not_le_of_gt hqb) (hb q hz)
  have hqA : ‖matrixOperator A‖<q := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hqB : ‖matrixOperator B‖<q := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have he := same_matrix_outputs_resolvent A B o h q hqA hqB hnA hnB
  rw [inverse_diagonal_eq_cofactor,inverse_diagonal_eq_cofactor] at he
  have hh := (div_eq_div_iff hnA hnB).mp he
  simpa only [Set.mem_setOf_eq,Polynomial.eval_mul] using hh

end HydrologyTree
