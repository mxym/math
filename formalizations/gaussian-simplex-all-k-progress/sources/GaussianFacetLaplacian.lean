import GaussianCovarianceFluxDerivative
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The facet matrix is the actual positive weighted Laplacian, with the
paper's exact trace normalization and covariance derivative factor. -/
open MeasureTheory ProbabilityTheory Set Module Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {k : ℕ} [NeZero k]

noncomputable def facetLaplacian (w : Fin k → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal (fun i => ∑ j, w i j) - Matrix.of w

lemma facetLaplacian_mulVec (w : Fin k → Fin k → ℝ) (x : Fin k → ℝ) (i : Fin k) :
    (facetLaplacian w *ᵥ x) i = ∑ j, w i j * (x i - x j) := by
  unfold facetLaplacian
  rw [sub_mulVec]
  simp only [Pi.sub_apply]
  rw [mulVec_diagonal]
  simp only [mulVec,dotProduct,Matrix.of_apply,
    mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]

lemma facetLaplacian_trace (w : Fin k → Fin k → ℝ) (hd : ∀ i, w i i = 0) :
    (facetLaplacian w).trace = fluxTrace w := by
  simp [facetLaplacian,trace_sub,Matrix.trace,hd,fluxTrace]

lemma facetLaplacian_row_sum (w : Fin k → Fin k → ℝ) (i : Fin k) :
    (∑ j, facetLaplacian w i j) = 0 := by
  have hh := facetLaplacian_mulVec w (fun _ => 1) i
  simpa [mulVec,dotProduct] using hh

lemma facetLaplacian_symmetric (w : Fin k → Fin k → ℝ) (hs : ∀ i j, w i j = w j i) :
    (facetLaplacian w).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [facetLaplacian,Matrix.sub_apply,Matrix.diagonal_apply,conj_trivial]
  by_cases h : i = j
  · simp [h]
  · simp [h,Ne.symm h,hs i j]

lemma facetLaplacian_trace_mul (w : Fin k → Fin k → ℝ)
    (D : Matrix (Fin k) (Fin k) ℝ) :
    (facetLaplacian w * D).trace = ∑ i, ∑ j, w i j * (D i i - D j i) := by
  unfold facetLaplacian
  rw [Matrix.sub_mul,trace_sub]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.diagonal_mul]
  simp only [Matrix.mul_apply,Matrix.of_apply,mul_sub,Finset.sum_sub_distrib,
    ← Finset.sum_mul]

theorem fluxCovarianceDifferential_eq_trace (w : Fin k → Fin k → ℝ)
    (hs : ∀ i j, w i j = w j i) (D : Matrix (Fin k) (Fin k) ℝ) :
    fluxCovarianceDifferential w D = (facetLaplacian w * D).trace / 2 := by
  have hswap : (∑ i, ∑ j, w i j * (D j j - D i j)) =
      ∑ i, ∑ j, w i j * (D i i - D j i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  unfold fluxCovarianceDifferential
  simp_rw [show ∀ a b c e : ℝ, a+b-c-e = (a-e)+(b-c) by intros; ring,
    mul_add,Finset.sum_add_distrib]
  rw [hswap,facetLaplacian_trace_mul]
  ring

end GaussianMeasureBridge
