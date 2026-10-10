import GaussianAffineMatrixFactorization
import GaussianDiagonalCovarianceDerivative

/-! Existence of a genuine differentiable score lift for every affine path
through a positive-definite covariance. Spectral congruence reduces it to the
already proved scalar square-root variance path. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {n : ℕ} [NeZero n]

theorem positive_covariance_diagonal_scores
    (A E : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hE : E.IsHermitian) :
    ∃ r : Fin n → Space n, ∃ a : Fin n → ℝ,
      LinearIndependent ℝ r ∧ scoreGram r = A ∧ diagonalCovarianceDirection r a = E := by
  obtain ⟨M,a,hM,hMM,hME⟩ := affine_matrix_diagonal_factorization A E hA hE
  let r : Fin n → Space n := fun i => WithLp.toLp 2 (fun j => M i j)
  have hg : scoreGram r = M*Mᴴ := by
    ext i j
    simp only [scoreGram,r,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
      Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hd : diagonalCovarianceDirection r a = M*Matrix.diagonal a*Mᴴ := by
    ext i j
    simp only [diagonalCovarianceDirection,r]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply,star_trivial]
    apply Finset.sum_congr rfl
    intro l _
    ring
  refine ⟨r,a,?_,hg.trans hMM,hd.trans hME⟩
  apply Matrix.linearIndependent_of_posDef_gram
  change (scoreGram r).PosDef
  rw [hg,hMM]
  exact hA

theorem positive_covariance_affine_score_lift
    (A E : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hE : E.IsHermitian) :
    ∃ v : ℝ → Fin n → Space n, ∃ h : Fin n → Space n,
      HasDerivAt v h 0 ∧ LinearIndependent ℝ (v 0) ∧ scoreGram (v 0) = A ∧
      (fun t : ℝ => scoreGram (v t)) =ᶠ[𝓝 (0:ℝ)] (fun t : ℝ => A+t•E) := by
  obtain ⟨r,a,hr,hg,he⟩ := positive_covariance_diagonal_scores A E hA hE
  refine ⟨diagonalScorePath r a,diagonalScoreVelocity r a,
    diagonalScorePath_hasDerivAt r a,?_,?_,?_⟩
  · simpa only [diagonalScorePath_zero] using hr
  · simpa only [diagonalScorePath_zero] using hg
  · filter_upwards [eventually_positive_diagonal a] with t ht
    rw [scoreGram_diagonalScorePath r a t (fun j => (ht j).le),hg,he]

end GaussianMeasureBridge
