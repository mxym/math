import GaussianScoreDerivative
import GaussianScoreSymmetry

/-! A Gaussian rotational moment identity derived from actual score integrals.
Infinitesimal skew motions give an even Gram path, so its existing derivative
must vanish. This supplies tangential components in a slicing proof of flux. -/
open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma scoreGram_skew_path_even (v h : Fin k → Space d)
    (hskew : ∀ i j, ⟪h i, v j⟫ + ⟪v i, h j⟫ = 0) (t : ℝ) :
    scoreGram (affineScores v h (-t)) = scoreGram (affineScores v h t) := by
  ext i j
  simp only [scoreGram, affineScores, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  have he : ⟪h i, v j⟫ = -⟪v i, h j⟫ := by linarith [hskew i j]
  rw [he]
  ring

/-- Every skew infinitesimal score motion has zero pairing with the genuine
Gaussian winning moments, at arbitrary prices. -/
theorem gaussian_skew_moment_identity (v h : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v)
    (hskew : ∀ i j, ⟪h i, v j⟫ + ⟪v i, h j⟫ = 0) :
    (∑ i, ⟪h i, (winningPartition v b hv).moment i⟫) = 0 := by
  let f : ℝ → ℝ := fun t => expectedScore (affineScores v h t) b
  let a : ℝ := ∑ i, ⟪h i, (winningPartition v b hv).moment i⟫
  have hzero (t : ℝ) : affinePrices b 0 t = b := by
    funext i; simp [affinePrices]
  have hd : HasDerivAt f a 0 := by
    have hh := expectedScore_directional_derivative v h b 0 hv
    simpa only [hzero, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero] using hh
  have he (t : ℝ) : f (-t) = f t :=
    expectedScore_eq_of_gram_eq _ _ (scoreGram_skew_path_even v h hskew t) b
  have hn : HasDerivAt (fun t => f (-t)) (-a) 0 := by
    have hd' : HasDerivAt f a ((-id) (0 : ℝ)) := by simpa using hd
    have hh := hd'.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg)
    convert hh using 1
    · rfl
    · ring
  have hn' : HasDerivAt f (-a) 0 := by
    convert hn using 1
    exact funext fun t => (he t).symm
  have hh := hd.unique hn'
  change a = 0
  linarith

/-- The score/moment cross-matrix is symmetric. This is an actual Gaussian
integration identity and does not presuppose a facet Laplacian. -/
theorem gaussian_score_moment_symmetric (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) (p q : Fin d) :
    (∑ i, v i p * (winningPartition v b hv).moment i q) =
      ∑ i, v i q * (winningPartition v b hv).moment i p := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  let h : Fin k → Space d := fun i => v i p • e q - v i q • e p
  have hskew (i j : Fin k) : ⟪h i, v j⟫ + ⟪v i, h j⟫ = 0 := by
    simp [h, e, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, PiLp.inner_apply]
  have hh := gaussian_skew_moment_identity v h b hv hskew
  simp only [h, inner_sub_left, real_inner_smul_left, Finset.sum_sub_distrib] at hh
  have hcoord (r : Fin d) (x : Space d) : ⟪e r, x⟫ = x r := by
    simp [e, PiLp.inner_apply]
  simp_rw [hcoord] at hh
  exact sub_eq_zero.mp hh

end GaussianMeasureBridge
