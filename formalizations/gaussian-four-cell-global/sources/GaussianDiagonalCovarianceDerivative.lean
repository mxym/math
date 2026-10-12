import GaussianActualEnvelope
import GaussianCovarianceValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! An actual affine covariance derivative, obtained by a local square-root
lift of coordinate variances and the proved optimal-partition envelope theorem.
No covariance derivative, price Hessian, or boundary-flux identity is assumed. -/
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

noncomputable def diagonalScorePath (v : Fin k → Space d) (a : Fin d → ℝ)
    (t : ℝ) : Fin k → Space d :=
  fun i => WithLp.toLp 2 (fun j => Real.sqrt (1 + t * a j) * v i j)

noncomputable def diagonalScoreVelocity (v : Fin k → Space d) (a : Fin d → ℝ) :
    Fin k → Space d := fun i => WithLp.toLp 2 (fun j => (a j / 2) * v i j)

noncomputable def diagonalCovarianceDirection (v : Fin k → Space d) (a : Fin d → ℝ) :
    Matrix (Fin k) (Fin k) ℝ := fun i l => ∑ j, a j * (v i j * v l j)

@[simp] lemma diagonalScorePath_zero (v : Fin k → Space d) (a : Fin d → ℝ) :
    diagonalScorePath v a 0 = v := by
  funext i
  ext j
  simp [diagonalScorePath]

lemma eventually_positive_diagonal (a : Fin d → ℝ) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ j, 0 < 1 + t * a j := by
  apply eventually_all.mpr
  intro j
  have hc : ContinuousAt (fun t : ℝ => 1 + t * a j) 0 := by fun_prop
  exact continuousAt_const.eventually_lt hc (by norm_num)

lemma diagonalScorePath_hasDerivAt (v : Fin k → Space d) (a : Fin d → ℝ) :
    HasDerivAt (diagonalScorePath v a) (diagonalScoreVelocity v a) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  have hc : HasDerivAt (fun t : ℝ => fun j : Fin d =>
      Real.sqrt (1 + t * a j) * v i j) (fun j => (a j / 2) * v i j) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    have harg : HasDerivAt (fun t : ℝ => 1 + t * a j) (a j) 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).mul_const (a j)).const_add 1 using 1 <;> simp
    have h := (harg.sqrt (by norm_num : (1 + (0 : ℝ) * a j) ≠ 0)).mul_const (v i j)
    convert h using 1 <;> simp [div_eq_mul_inv, mul_comm]
  have h := (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hc
  convert h using 1
  · rfl
  · rfl

lemma scoreGram_diagonalScorePath (v : Fin k → Space d) (a : Fin d → ℝ)
    (t : ℝ) (ht : ∀ j, 0 ≤ 1 + t * a j) :
    scoreGram (diagonalScorePath v a t) = scoreGram v + t • diagonalCovarianceDirection v a := by
  ext i l
  simp only [scoreGram, diagonalScorePath, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    diagonalCovarianceDirection, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (Real.sqrt (1 + t * a j) * v l j) * (Real.sqrt (1 + t * a j) * v i j) =
        Real.sqrt (1 + t * a j) ^ 2 * (v i j * v l j) := by ring
    _ = v l j * v i j + t * (a j * (v i j * v l j)) := by
      rw [Real.sq_sqrt (ht j)]
      ring

/-- The derivative of the genuine covariance infimum along an affine change of
coordinate variances. The direction may have either sign. -/
theorem covarianceValue_diagonal_derivative (v : Fin k → Space d) (hv : Function.Injective v)
    (a : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ => covarianceValue (scoreGram v + t • diagonalCovarianceDirection v a))
      (∑ i, ⟪diagonalScoreVelocity v a i, balancedMoment v i⟫) 0 := by
  have hd := equalMassValue_path_derivative (diagonalScorePath v a) 0
    (diagonalScoreVelocity v a) (by simpa using hv) (diagonalScorePath_hasDerivAt v a)
  simp only [diagonalScorePath_zero] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_positive_diagonal a] with t ht
  rw [← covarianceValue_scoreGram, scoreGram_diagonalScorePath v a t (fun j => (ht j).le)]

end GaussianMeasureBridge
